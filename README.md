vhdfix
======

Utility for manipulating Virtual Hard Disk (VHD) files. By default, vhdfix
creates the smallest possible copy of the source VHD with the data blocks in
optimal order. It performs a thorough validation of the source VHD and reports
any problems found. The output format can be controlled with command-line
options.

To build and run:

1. Install [Go](https://golang.org/dl/).
2. `go build vhdfix.go`
3. `./vhdfix -h`
