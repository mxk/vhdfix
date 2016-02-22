//
// Written by Maxim Khitrov (February 2016)
//

package main

import (
	"bytes"
	"encoding/binary"
	"encoding/hex"
	"flag"
	"fmt"
	"io"
	"log"
	"os"
	"path/filepath"
	"sort"
	"time"
)

const (
	dstSuffix  = "-fixed.vhd"
	sector     = 512
	hdrSize    = 512
	hdrCookie  = "conectix"
	hdrVersion = uint32(0x00010000)
	hdrCsumOff = 64
	dynSize    = 1024
	dynCookie  = "cxsparse"
	dynVersion = uint32(0x00010000)
	dynCsumOff = 36
	blkMinSize = 2097152
	unused     = uint32(0xFFFFFFFF)
	dataAlign  = 4096
)

// Command-line options.
var (
	blkAlign = flag.Bool("align", false,
		"align data on a 4096 byte boundary")
	batExtend = flag.Uint("batExtend", 0xFF,
		"`byte` value used to extend bat to a sector boundary")
	batOff = flag.Uint64("batOff", 0,
		"manually set bat `offset` (0=auto, 1=original)")
	batReserve = flag.Uint64("batReserve", 0,
		"allocate additional number of bat `entries`")
	blkOff = flag.Uint64("blkOff", 0,
		"manually set first data block `offset` (0=auto, 1=original)")
	copyId = flag.Bool("copyId", false,
		"copy uuid from one vhd to another (destination must be a valid vhd)")
	force = flag.Bool("f", false,
		"overwrite destination vhd if it exists")
	noCompact = flag.Bool("noCompact", false,
		"keep all-zero data blocks")
	noReorder = flag.Bool("noReorder", false,
		"keep data blocks in their original order")
	parseOnly = flag.Bool("parseOnly", false,
		"do not write new vhd")
)

// Source and destination file names.
var srcName, dstName string

func usage(err string) {
	fmt.Fprintf(os.Stderr, "Usage: %s [options] <src> [<dst>]\n\n",
		filepath.Base(os.Args[0]))
	fmt.Fprintf(os.Stderr, "Options ('bat' = block allocation table):\n")
	flag.PrintDefaults()
	fmt.Fprint(os.Stderr, "\n")
	if err != "" {
		fmt.Fprintf(os.Stderr, "Error: %s\n", err)
		os.Exit(2)
	}
}

func init() {
	log.SetFlags(log.Ltime)
	flag.Usage = func() { usage("") }
	flag.Parse()
	switch flag.NArg() {
	case 1:
		srcName = flag.Arg(0)
		dstName = srcName[:len(srcName)-len(filepath.Ext(srcName))] + dstSuffix
	case 2:
		srcName = flag.Arg(0)
		dstName = flag.Arg(1)
	default:
		usage("invalid number of arguments")
	}
	srcAbs, _ := filepath.Abs(srcName)
	dstAbs, _ := filepath.Abs(dstName)
	if srcAbs == dstAbs {
		usage("I'm sorry Dave, I'm afraid I can't do that")
	}
}

func main() {
	src := OpenVHD(srcName, false)
	defer src.Close()

	if *copyId && !*parseOnly {
		dst := OpenVHD(dstName, true)
		defer dst.Close()

		msg("copying uuid")
		copy(dst.uuid, src.uuid)
		csum(dst.hdr, hdrCsumOff)
		diff := dst.hdr[hdrCsumOff : hdrCsumOff+20]

		seek(dst, hdrCsumOff)
		write(dst, diff)
		seek(dst, dst.ftrOff+hdrCsumOff)
		write(dst, diff)
		return
	}

	src.ParseDynamic()
	src.ParseBat()
	if *parseOnly {
		msg("vhd ok")
		return
	}

	// Write VHD header
	dst := CreateVHD(dstName, *force)
	defer dst.Close()
	copy(dst.hdr, src.hdr)
	write(dst, dst.hdr)

	// Calculate new BAT and data block offsets
	dst.batOff = pickOff(dst.batOff, src.batOff, *batOff)
	if dst.batOff != src.batOff {
		msg("relocating bat to: %#x", dst.batOff)
	}
	dst.blkNum = src.blkNum + uint32(*batReserve)
	dst.blkSize = src.blkSize
	dst.blkOff = pickOff(dst.EndOfBat(), src.blkOff, *blkOff)
	if *blkAlign {
		dst.blkOff = alignBlock(dst.blkOff, dst.blkSize)
	}
	if dst.blkOff != src.blkOff {
		msg("relocating data blocks to: %#x", dst.blkOff)
	}

	// Write dynamic disk header
	copy(dst.dyn, src.dyn)
	w64(dst.dyn, 16, dst.batOff)
	csum(dst.dyn, dynCsumOff)
	extend(dst, dst.dynOff)
	write(dst, dst.dyn)

	// Copy blocks
	dst.bat, src.bat = src.bat, nil
	if *noReorder {
		sort.Sort(BySec(dst.bat))
	}
	extend(dst, dst.blkOff)
	buf := make([]byte, dst.BlockSize())
	removed := 0
	for i, be := range dst.bat {
		seek(src, be.Off())
		read(src, buf)
		if *noCompact || !isUnused(buf, dst.blkSize) {
			checkBitmap(buf, dst.blkSize, be)
			off := tell(dst)
			if *blkAlign {
				off = alignBlock(off, dst.blkSize)
				extend(dst, off)
			}
			be.Set(off)
			write(dst, buf)
		} else {
			be.Set(0)
			removed++
		}
		dst.bat[i] = be
		progress(i+1, len(dst.bat))
	}
	if !*noCompact {
		msg("empty data blocks removed: %d", removed)
	}

	// Write footer
	dst.ftrOff = tell(dst)
	if *blkAlign {
		dst.ftrOff = alignBlock(dst.ftrOff, dst.blkSize)
		extend(dst, dst.ftrOff)
	}
	if dst.ftrOff != src.ftrOff {
		msg("relocating footer to: %#x", dst.ftrOff)
	}
	write(dst, dst.hdr)

	// Write BAT
	buf = bytes.Repeat([]byte{0xFF}, int(dst.BatSize()))
	if removed < len(dst.bat) {
		for _, be := range dst.bat {
			if be.sec != unused {
				w32(buf, int(be.idx*4), be.sec)
			}
		}
	} else {
		msg("new vhd is empty")
	}
	seek(dst, dst.batOff)
	write(dst, buf)
	if extend := int(dst.BatExtra()); extend > 0 {
		write(dst, bytes.Repeat([]byte{byte(*batExtend)}, extend))
	}
	msg("all done :)")
}

// pickOff selects which offset to use based on user preference.
func pickOff(min, src, usr uint64) (off uint64) {
	switch usr {
	case 0:
		off = min
	case 1:
		off = src
	default:
		off = usr
	}
	if off < min || !aligned(off, sector) {
		die("invalid offset: %#x", off)
	}
	return
}

var lastProgress time.Time

// progress reports operation progress as a percentage to stdout.
func progress(i, n int) {
	now := time.Now()
	if 0 < i && i < n && now.Sub(lastProgress) < time.Second {
		return
	}
	lastProgress = now
	w := bytes.Buffer{}
	log.SetOutput(&w)
	defer log.SetOutput(os.Stderr)
	log.Printf("%.1f%%", float64(i)/float64(n)*100)
	w.Truncate(w.Len() - 1)
	w.WriteByte('\r')
	w.WriteTo(os.Stdout)
}

// VHD represents a single dynamic VHD file.
type VHD struct {
	*os.File

	hdr     []byte
	dyn     []byte
	bat     []BatEntry
	uuid    UUID
	fSize   uint64
	vSize   uint64
	dynOff  uint64
	batOff  uint64
	blkOff  uint64
	ftrOff  uint64
	blkNum  uint32
	blkSize uint32
}

// OpenVHD opens an existing VHD file for reading and/or writing.
func OpenVHD(name string, rw bool) *VHD {
	flag := os.O_RDONLY
	if rw {
		flag = os.O_RDWR
	}
	f := &VHD{File: openFile(name, flag, 0)}
	f.ParseHeader()
	f.CompareFooter()
	return f
}

// CreateVHD creates a new VHD file, optionally overwriting an existing one.
func CreateVHD(name string, overwrite bool) *VHD {
	flag := os.O_WRONLY | os.O_CREATE
	if overwrite {
		flag |= os.O_TRUNC
	} else {
		flag |= os.O_EXCL
	}
	hdr := make([]byte, hdrSize)
	ftrOff := uint64(hdrSize + dynSize + sector)
	return &VHD{
		File:    openFile(name, flag, 0666),
		hdr:     hdr,
		dyn:     make([]byte, dynSize),
		uuid:    UUID(hdr[68:84]),
		dynOff:  hdrSize,
		batOff:  hdrSize + dynSize,
		blkOff:  ftrOff,
		ftrOff:  ftrOff,
		blkSize: blkMinSize,
	}
}

// BatSize returns the total number of bytes used by valid BAT entries.
func (f *VHD) BatSize() uint64 {
	return 4 * uint64(f.blkNum)
}

// BatExtra returns the number of bytes needed to extend the BAT to a sector
// boundary.
func (f *VHD) BatExtra() uint64 {
	if n := f.BatSize(); n > 0 {
		return align(n, sector) - n
	}
	return sector
}

// EndOfBat returns the offset of the first sector past the BAT.
func (f *VHD) EndOfBat() uint64 {
	return f.batOff + f.BatSize() + f.BatExtra()
}

// BlockSize returns the total number of bytes used by each data block including
// the bitmap.
func (f *VHD) BlockSize() uint64 {
	return bitmapSize(f.blkSize) + uint64(f.blkSize)
}

// ParseHeader validates VHD header and extracts required fields.
//
// Field order and sizes:
// 	8   Cookie
// 	4   Features
// 	4   File Format Version
// 	8   Data Offset
// 	4   Time Stamp
// 	4   Creator Application
// 	4   Creator Version
// 	4   Creator Host OS
// 	8   Original Size
// 	8   Current Size
// 	4   Disk Geometry
// 	4   Disk Type
// 	4   Checksum
// 	16  Unique Id
// 	1   Saved State
//
func (f *VHD) ParseHeader() {
	seek(f, 0)
	f.hdr = readn(f, hdrSize)

	if string(f.hdr[:len(hdrCookie)]) != hdrCookie {
		die("invalid vhd header cookie")
	}
	if r32(f.hdr, 12) != hdrVersion {
		die("unsupported vhd file format")
	}
	if !csum(f.hdr, hdrCsumOff) {
		die("invalid vhd header checksum")
	}
	if r32(f.hdr, 60) != 3 {
		die("not a dynamic vhd")
	}
	if f.hdr[84] != 0 {
		die("saved state vhd (can't be modified)")
	}
	if !isZero(f.hdr[85:]) {
		die("unexpected non-zero data in vhd header")
	}

	f.dynOff = r64(f.hdr, 16)
	f.vSize = r64(f.hdr, 48)
	f.uuid = UUID(f.hdr[68:84])

	msg("vhd uuid: %s", f.uuid)
	msg("virtual size: %d", f.vSize)
}

// CompareFooter verifies that the VHD header and footer are identical.
func (f *VHD) CompareFooter() {
	f.fSize = seekw(f, 0, 2)
	if f.fSize < hdrSize+dynSize+sector+hdrSize-1 {
		die("invalid file size")
	}
	f.ftrOff = (f.fSize - 1) / sector * sector
	n := int(f.fSize - f.ftrOff)
	if n < hdrSize-1 || hdrSize < n {
		die("invalid footer alignment or size")
	}
	seek(f, f.ftrOff)
	if !bytes.Equal(f.hdr[:n], readn(f, n)) {
		die("header != footer")
	}
}

// ParseDynamic validates dynamic disk header and extracts required fields.
//
// Field order and sizes:
// 	8   Cookie
// 	8   Unused
// 	8   Table Offset
// 	4   Header Version
// 	4   Max Table Entries
// 	4   Block Size
// 	4   Checksum
// 	16  Parent Unique ID
// 	4   Parent Time Stamp
// 	4   Reserved
// 	512 Parent Unicode Name
// 	24  Parent Locator Entry 1-8 (each)
//
func (f *VHD) ParseDynamic() {
	if f.dynOff != hdrSize {
		die("invalid dynamic header offset: %#x", f.dynOff)
	}
	seek(f, f.dynOff)
	f.dyn = readn(f, dynSize)

	if string(f.dyn[:len(dynCookie)]) != dynCookie {
		die("invalid dynamic header cookie")
	}
	if r32(f.dyn, 24) != dynVersion {
		die("unsupported dynamic header version")
	}
	if !csum(f.dyn, dynCsumOff) {
		die("invalid dynamic header checksum")
	}
	if r64(f.dyn, 8) != 1<<64-1 {
		die("invalid dynamic header data offset field")
	}
	if !isZero(f.dyn[40:]) {
		die("non-zero parent data in dynamic header")
	}

	f.batOff = r64(f.dyn, 16)
	f.blkNum = r32(f.dyn, 28)
	f.blkSize = r32(f.dyn, 32)

	if f.blkSize < blkMinSize || (f.blkSize&(f.blkSize-1)) != 0 {
		die("unsupported block size")
	}
	if max := uint64(f.blkNum) * uint64(f.blkSize); max > 2040<<30 {
		die("invalid block count (capacity > 2040 GB)")
	} else if f.vSize != max {
		msg("virtual size not equal to max capacity: %d != %d", f.vSize, max)
		if f.vSize > max {
			die("invalid virtual size")
		}
	}
}

// ParseBat validates and extracts data block offsets from the BAT.
func (f *VHD) ParseBat() {
	msg("bat offset: %#x", f.batOff)
	if f.batOff < hdrSize+dynSize || !aligned(f.batOff, sector) {
		die("invalid bat offset")
	}
	if f.blkOff = f.EndOfBat(); f.blkOff > f.ftrOff {
		die("bat extends past footer")
	}
	seek(f, f.batOff)
	buf := readn(f, int(f.BatSize()))

	// Decode all entries and count how many are used
	raw := make(RawBat, f.blkNum)
	used := uint32(0)
	for i := range raw {
		s := r32(buf, i*4)
		if raw[i] = s; s != unused {
			used++
		}
	}
	msg("used bat entries: %d / %d (%.1f%%)", used, f.blkNum,
		float64(used)/float64(f.blkNum)*100)
	buf = nil

	// Convert used entries to BatEntry structs
	if f.bat = make([]BatEntry, used); used > 0 {
		i := 0
		bat := f.bat
		for j, s := range raw {
			if s != unused {
				bat[i] = BatEntry{uint32(j), s}
				raw[i] = s
				i++
			}
		}
	}
	raw = raw[:used]
	sort.Sort(raw)

	// Find first data block and check all entries for errors
	a4k := true
	minOff := f.ftrOff
	bs := bitmapSize(f.blkSize)
	if used > 0 {
		if minOff = uint64(raw[0]) * sector; minOff < f.blkOff {
			die("invalid bat entry (< end of bat): %#x", raw[0])
		}
		pos := minOff
		inc := f.BlockSize()
		gaps := 0
		for _, s := range raw {
			off := uint64(s) * sector
			if off < pos {
				die("invalid bat entry (overlap): %#x", s)
			} else if off > pos {
				gaps++
			}
			if a4k && !aligned(off+bs, dataAlign) {
				a4k = false
				msg("first unaligned data block at: %#x", off)
			}
			pos = off + inc
		}
		if gaps > 0 {
			msg("data blocks are not contiguous: %d gap(s)", gaps)
		}
		if a4k {
			msg("all data blocks are aligned")
		}
		if pos > f.ftrOff {
			die("invalid bat entry (> footer): %#x", raw[len(raw)-1])
		}
		if pos < f.ftrOff && !(a4k && aligned(f.ftrOff+bs, dataAlign)) {
			msg("extra space between data blocks and footer: %d bytes",
				f.ftrOff-pos)
		}
	}
	if f.blkOff < minOff && !(a4k && aligned(minOff+bs, dataAlign)) {
		msg("extra space between bat and first data block: %d bytes",
			minOff-f.blkOff)
	}
	f.blkOff = minOff
	msg("first data block offset: %#x", f.blkOff)
}

// BatEntry represents a single BAT sector offset entry.
type BatEntry struct{ idx, sec uint32 }

func (b BatEntry) Off() uint64 {
	return uint64(b.sec) * sector
}

func (b *BatEntry) Set(off uint64) {
	if off >= hdrSize+dynSize+sector && aligned(off, sector) {
		b.sec = uint32(off / sector)
	} else {
		if off != 0 {
			die("invalid data block offset: %#x", off)
		}
		b.sec = unused
	}
}

type BySec []BatEntry

func (s BySec) Len() int           { return len(s) }
func (s BySec) Swap(i, j int)      { s[i], s[j] = s[j], s[i] }
func (s BySec) Less(i, j int) bool { return s[i].sec < s[j].sec }

type RawBat []uint32

func (s RawBat) Len() int           { return len(s) }
func (s RawBat) Swap(i, j int)      { s[i], s[j] = s[j], s[i] }
func (s RawBat) Less(i, j int) bool { return s[i] < s[j] }

// UUID is a universally unique identifier.
type UUID []byte

func (u UUID) String() string {
	if len(u) != 16 {
		die("invalid uuid")
	}
	b := make([]byte, 36)
	hex.Encode(b[0:8], u[0:4])
	b[8] = '-'
	hex.Encode(b[9:13], u[4:6])
	b[13] = '-'
	hex.Encode(b[14:18], u[6:8])
	b[18] = '-'
	hex.Encode(b[19:23], u[8:10])
	b[23] = '-'
	hex.Encode(b[24:], u[10:])
	return string(b)
}

// bitmapSize returns the size of the sector bitmap for a given data block size
// extended to a sector boundary.
func bitmapSize(blkSize uint32) uint64 {
	return align(uint64(blkSize)/(8*sector), sector)
}

// isUnused returns true if the data block in buf contains only all-zero data.
func isUnused(buf []byte, blkSize uint32) bool {
	dataOff := int(bitmapSize(blkSize))
	if len(buf) != dataOff+int(blkSize) {
		die("invalid data block buffer")
	}
	return isZero(buf[dataOff:])
}

// checkBitmap confirms that every non-zero sector is marked as used.
func checkBitmap(buf []byte, blkSize uint32, be BatEntry) {
	bitmap, data := buf[:blkSize/(8*sector)], buf[bitmapSize(blkSize):]
	for i, b := range bitmap {
		if b == 0xFF {
			continue // All sectors used
		}
		page := data[i*8*sector : (i+1)*8*sector]
		if b == 0x00 {
			if !isZero(page) {
				die("non-zero data in unused sectors at: %#x[%d]", be.Off(), i)
			}
			continue // All sectors unused
		}
		used := byte(0)
		for len(page) > 0 {
			if used = used << 1; !isZero(page[:sector]) {
				used |= 1
			}
			page = page[sector:]
		}
		//    b: 0 0 1 1
		// used: 0 1 0 1
		// -------------
		//  bad: 0 1 0 0
		if ^b&used != 0 {
			die("non-zero data in unused sectors at: %#x[%d]", be.Off(), i)
		}
	}
}

// csum returns true if buf contains a valid 32-bit VHD checksum at offset off.
// The correct checksum is written to buf[off:off+4].
func csum(buf []byte, off int) bool {
	sum := uint32(0)
	for _, b := range buf[:off] {
		sum += uint32(b)
	}
	for _, b := range buf[off+4:] {
		sum += uint32(b)
	}
	sum = ^sum
	ok := r32(buf, off) == sum
	w32(buf, off, sum)
	return ok
}

var zero [8192]byte

// isZero returns true if b contains all-zero data.
func isZero(b []byte) bool {
	for len(b) > len(zero) {
		if !bytes.Equal(b[:len(zero)], zero[:]) {
			return false
		}
		b = b[len(zero):]
	}
	return len(b) == 0 || bytes.Equal(b, zero[:len(b)])
}

func msg(f string, v ...interface{}) { log.Printf(f, v...) }
func die(f string, v ...interface{}) { log.Panicf(f, v...) }

func fatal(err error) {
	log.Printf("error: %v", err)
	panic(err.Error()) // Fix for https://github.com/golang/go/issues/14432
}

func align(off, bnd uint64) uint64 { return (off + bnd - 1) / bnd * bnd }
func aligned(off, bnd uint64) bool { return off%bnd == 0 }

func alignBlock(blkOff uint64, blkSize uint32) uint64 {
	bs := bitmapSize(blkSize)
	return align(blkOff+bs, dataAlign) - bs
}

func r32(b []byte, i int) uint32    { return binary.BigEndian.Uint32(b[i:]) }
func r64(b []byte, i int) uint64    { return binary.BigEndian.Uint64(b[i:]) }
func w32(b []byte, i int, v uint32) { binary.BigEndian.PutUint32(b[i:], v) }
func w64(b []byte, i int, v uint64) { binary.BigEndian.PutUint64(b[i:], v) }

func openFile(name string, flag int, perm os.FileMode) *os.File {
	f, err := os.OpenFile(name, flag, perm)
	if err != nil {
		fatal(err)
	}
	return f
}

func seek(s io.Seeker, off uint64) uint64 { return seekw(s, int64(off), 0) }
func tell(s io.Seeker) uint64             { return seekw(s, 0, 1) }

func seekw(s io.Seeker, off int64, whence int) uint64 {
	off, err := s.Seek(off, whence)
	if err != nil {
		fatal(err)
	}
	return uint64(off)
}

func readn(r io.Reader, n int) []byte {
	return read(r, make([]byte, n))
}

func read(r io.Reader, b []byte) []byte {
	if _, err := io.ReadFull(r, b); err != nil {
		fatal(err)
	}
	return b
}

func write(w io.Writer, b []byte) int {
	n, err := w.Write(b)
	if err != nil {
		fatal(err)
	}
	return n
}

func extend(w io.WriteSeeker, off uint64) {
	if eof := seekw(w, 0, 2); eof < off {
		n := int(off - eof)
		for n > len(zero) {
			n -= write(w, zero[:])
		}
		write(w, zero[:n])
	} else if off < eof {
		die("extend offset < file size")
	}
}
