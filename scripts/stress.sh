#!/bin/bash
set -e
while true
do
  python3 scripts/random6502.py >foo.bin
  python3 decomp.py foo.bin 2>&1 >log
  grep RAW log && false
  grep TBD: log && false
  cat log
done
