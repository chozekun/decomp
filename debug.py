# debug.py
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

import sys

SSA, DESSA, EXPR, ARGRET, TRACE, BLOCK, CODE, MAIN = range(0, 8)
_name = ['ssa', 'dessa', 'expr', 'argret', 'trace', 'block', 'code', 'main']
enabled = set()

debug_level = 0
debugout = sys.stdout
enabled = set()

def debug(type, level, *args, **kwargs):
  global enabled
  if debug_level >= level and type in enabled:
    print(_name[type].ljust(6).upper(), *args, file=debugout, **kwargs)

def enable(lst):
  global enabled
  if 'all' in lst:
    lst = _name
  enabled = [list.index(_name, x) for x in lst]

def debug_enabled(level):
  return debug_level >= level
