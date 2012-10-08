# decomp.py
# Copyright (C) 2012 Ulrich Hecht

# This file is part of 6502 Decompiler.

# 6502 Decompiler is free software: you can redistribute it and/or modify it
# under the terms of the GNU General Public License version 3 as published
# by the Free Software Foundation.

# 6502 Decompiler is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
# or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
# for more details.

# You should have received a copy of the GNU General Public License along
# with 6502 Decompiler.  If not, see <http://www.gnu.org/licenses/>.

from __future__ import print_function

import optparse
import sys

from util import *

import debug
import insn
import ssa
import block
import code

def main():
  sys.setrecursionlimit(10000)

  parser = optparse.OptionParser()
  parser.add_option('-o', '--origin', help='Binary start address', default='0x8000')
  parser.add_option('-e', '--entries', help='Program entry point', default=None)
  parser.add_option('-i', '--io-ranges', help='MMIO address ranges', default=None)
  parser.add_option('-d', '--debug', help='Debug types enabled', default='all')
  parser.add_option('-v', '--debug-level', help='Debug verbosity level', default='0')
  parser.add_option('-f', '--debug-file', help='Debug output file name', default=None)
  options, args = parser.parse_args()

  try:
    debug.debug_level = int(options.debug_level)
  except ValueError:
    raise UserError('invalid debug level')

  if options.debug_file != None:
    debug.debugout = open(options.debug_file, 'w')
  debug.enable(options.debug.split(','))

  try:
    bin = args[0]
    text = bytearray(open(bin, 'rb').read())
  except Exception as e:
    raise UserError('failed to open code file: ' + str(args[0]))

  try:
    org = int(options.origin, 16)
  except ValueError:
    raise UserError('invalid origin address')

  if options.entries != None:
    try:
      entries = [int(x, 16) for x in options.entries.split(',')]
    except ValueError:
      raise UserError('invalid entry point(s) specified')
  else:
    if len(text) + org >= 0x10000:
      entries = [text[0xfffc - org] + (text[0xfffd - org] << 8),
                 text[0xfffa - org] + (text[0xfffb - org] << 8)]
    else:
      entries = [org]

  try:
    if options.io_ranges != None:
      iomap = []
      ranges = options.io_ranges.split(',')
      for i in ranges:
        if '-' in i:
          iomap += [tuple([int(x, 16) for x in i.split('-')])]
        else:
          iomap += [int(i, 16)]
    else:
      iomap = [(0x2000, 0x4017)]
  except ValueError:
    raise UserError('invalid MMIO ranges specified')

  debug.debug(debug.MAIN, 1, 'iomap', iomap)

  mcg = insn.MCodeGraph()
  ins = mcg.traceall(text, org, entries)
  ssa_funs = []
  for k,v in mcg.symbols.items():
    debug.debug(debug.MAIN, 2, '=== OSSIFY', v.address, v.name, v.insn)
    ssag = ssa.ssaify(v.insn, v.name, iomap)
    ssa_funs += [ssag]
    debug.debug(debug.MAIN, 3, 'callers', ssag.callers_graphs)
    debug.debug(debug.MAIN, 3, 'callsts', ssag.callers_st)
    #break
  ssa.identifyreturns(ssa_funs)
  for i in ssa_funs:
    # depropagation must be done after DCE, i.e. after identifyreturns()
    i.depropagate()
    i.dessa()
    bb = block.blockify(i)
    debug.debug(debug.MAIN, 3, '-- PREDESSA')
    block.dump(3, bb)
    debug.debug(debug.MAIN, 3, '-- PRESTRUCT')
    block.dump(3, bb)
    (bb, found) = block.structure(bb)
    debug.debug(debug.MAIN, 3, '-- POSTSTRUCT')
    while found:
      debug.debug(debug.MAIN, 3, 'retrying', bb)
      (bb, found) = block.structure(bb)
    debug.debug(debug.MAIN, 2, '-- POSTPOSTSTRUCT')
    block.dump(2, bb)
    if debug.debug_level >= 4:
      block.graphviz(bb)
    i.blocks = bb
  for i in ssa_funs:
    print(code.code(i.blocks, i.symbol, symbols = mcg.symbols, graphs = ssa_funs, graph = i), end='')
    print('=' * 78)

if __name__ == '__main__':
  try:
    main()
  except InternalError as e:
    if debug.debug_level == 0:
      print('Internal error:', str(e))
    else:
      raise e
  except UserError as e:
    print('User error:', str(e))
  except AssertionError as e:
    if debug.debug_level == 0:
      print('Internal error: assertion failed')
    else:
      raise e
  else:
    sys.exit(0)
  sys.exit(1)
