vhdfix
======

Utility for manipulating VHD files. By default, it writes a new VHD file of the
smallest possible size and reorders the data blocks by virtual sector order. It
provides various options to control the format of the output file.

Installation:

1. Install [Go](https://golang.org/dl/).
2. `go build vhdfix.go`

Usage:

* `vhdfix [options] <src> [<dst>]`
* `vhdfix -h`
