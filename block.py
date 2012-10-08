# block.py
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

import ssa
import expr

from debug import *

class BasicBlock:
  def __init__(self):
    self.next = []
    self.comefrom = []
    self.start_st = None
    self.end_st = None
    self.containered = False
    self.dont_clip = False
    self.clipped = False
  
  def __str__(self):
    if self.start_st:
      return 'bas' + hex(self.start_st.insn.addr)[2:].upper()
    else:
      return object.__str__(self)

  def parse(self, start, comefrom = None, blockified = None):
    self.start_st = start
    basic_blocks[start] = self
    if comefrom != None:
      self.comefrom += [comefrom]
    curst = start
    debug(BLOCK, 3, 'startblockat', curst)
    while len(curst.next) == 1 and len(list(curst.next)[0].comefrom) == 1 and curst.op != ssa.ENDLESS_LOOP and not curst.next[0] in basic_blocks:
      curst = list(curst.next)[0]
    debug(BLOCK, 3, 'endblockat', curst)
    self.end_st = curst
    if curst.op != ssa.ENDLESS_LOOP:
      for i in curst.next:
        if i in basic_blocks:
          basic_blocks[i].comefrom += [self]
          self.next += [basic_blocks[i]]
        else:
          nb = BasicBlock()
          nb.parse(i, self, blockified)
          basic_blocks[i] = nb
          self.next += [nb]
      # Workaround for "Bxx 0": A basic block should not have the same
      # successor multiple times.
      final_next = []
      for i in self.next:
        if i not in final_next:
          final_next += [i]
      self.next = final_next

  def dump(self, level):
    if not debug_enabled(level):
      return
    debug(BLOCK, level, '--- BASIC BLOCK', self, [str(x) for x in self.comefrom])
    debug(BLOCK, level, '--- START', self.start_st, 'END', self.end_st)
    curst = self.start_st
    while curst != self.end_st:
      debug(BLOCK, level, curst)
      curst = list(curst.next)[0]
    debug(BLOCK, level, curst)
    debug(BLOCK, level, '--- NEXT:', [str(x) for x in self.next])
  def sdump(self):
    s = '--- BASIC BLOCK' + '\n'
    curst = self.start_st
    while curst != self.end_st:
      s += str(curst) + '\n'
      curst = curst.next[0]
    s += str(curst) + '\n'
    return s

  def relink(self, new):
    for i in self.comefrom:
      newnext = []
      for j in i.next:
        if j == self:
          newnext += [new]
        else:
          newnext += [j]
      i.next = newnext
    new.comefrom = self.comefrom
  def recomefrom(self, old, new):
    newcomefrom = []
    for i in self.comefrom:
      if i in old:
        if not new in newcomefrom:
          newcomefrom += [new]
      else:
        newcomefrom += [i]
    self.comefrom = newcomefrom

def dump(level, block, dumped = None):
  if dumped == None:
    dumped = dict()
  block.dump(level)
  dumped[block] = True
  for i in block.next:
    if not i in dumped:
      dump(level, i, dumped)

def graphviz(blk, file = None, done = None):
  import re
  def shp(blkk):
    s = str(blkk) + '['
    if isinstance(blkk, AdvancedBlock):
      s += 'shape = box, '
    elif blkk.end_st.op == ssa.RETURN:
      s += 'shape = box, '
    #s += 'label = <' + blkk.sdump().replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;').replace('\n', '<br />') + '>];\n'
    s += 'label = <' + str(blkk) + '<br />'
    if blkk.start_st != blkk.end_st:
      s += '...<br />'
    lastins = re.sub(' -> .*$', '', str(blkk.end_st))
    if len(lastins) > 30:
      lastins = lastins.replace('] ', ']\n')
    s += lastins.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;').replace('\n', '<br />') + '>'
    s += '];\n'
    return s

  if file == None:
    file = open(hex(blk.start_st.insn.addr)[2:] + '.gv', 'w')
    file.write('digraph G {\n')
    closeit = True
    done = dict()
  else:
    closeit = False
  
  done[blk] = True

  if isinstance(blk, AdvancedBlock):
    file.write('subgraph cluster_' + str(blk) + ' {\nstyle=filled;\ncolor=lightgrey;\n')
    file.write('label = "' + AdvancedBlock.t[blk.type] + '"\n')
    if blk.type in [IF_THEN, IF_THEN_ELSE]:
      for i in blk.blocks:
        file.write(shp(i))
        file.write(str(blk) + ' -> ' + str(i) + ';\n')
        file.write(shp(blk.next[0]))
        file.write(str(i) + ' -> ' + str(blk.next[0]) + '\n')
    elif blk.type in [SEQUENCE, POST_LOOP]:
      file.write(str(blk) + ' -> ' + str(blk.blocks[0]) + ';\n')
      for i in blk.blocks[:-1]:
        file.write(shp(i))
        file.write(shp(i.next[0]))
        file.write(str(i) + ' -> ' + str(i.next[0]) + ';\n')
    file.write('}\n')
  else:
    if len(blk.next) == 0:
      file.write(shp(blk))
      file.write(str(blk) + ';\n')
  for i in blk.next:
    if isinstance(blk, AdvancedBlock) and len(blk.blocks) > 0:
      tb = blk.blocks[-1]
    else:
      tb = blk
    file.write(shp(tb))
    file.write(str(tb) + ' -> ' + str(i) + ';\n')
    if not i in done:
      graphviz(i, file, done)

  if closeit:
    file.write('}\n')
    file.close()
  
basic_blocks = dict()

def blockify(graph):
  first_block = BasicBlock()
  first_block.parse(graph.start)
  return first_block

IF_THEN = 0
IF_THEN_ELSE = 1
SEQUENCE = 2
POST_LOOP = 3
EMPTY_LOOP = 4
PRE_LOOP = 5

class AdvancedBlock(BasicBlock):
  t = {
    IF_THEN: 'ifthen',
    IF_THEN_ELSE: 'ite',
    SEQUENCE: 'sequence',
    POST_LOOP: 'ploop',
    EMPTY_LOOP: 'eloop',
    PRE_LOOP: 'prelp',
  }
  def __init__(self):
    BasicBlock.__init__(self)
    self.type = None
    self.blocks = []
    self.condition = None
    self.prolog = None
  def __str__(self):
    if self.start_st:
      return 'adv' + AdvancedBlock.t[self.type] + hex(self.start_st.insn.addr)[2:].upper()
    else:
      return object.__str__(self)
  def dump(self, level):
    if not debug_enabled(level):
      return
    debug(BLOCK, level, '--- ADVANCED BLOCK', AdvancedBlock.t[self.type], self.condition, self.blocks, self.comefrom)
    for i in self.blocks:
      i.dump(level)
    debug(BLOCK, level, '--- END ADVANCED BLOCK; NEXT:', self.next)
  def sdump(self):
    s = '--- ADVANCED BLOCK' + '\n'
    if self.condition:
      s += 'COND ' + str(self.condition)
    for i in self.blocks:
      s += i.sdump()
    s += '--- END ADVANCED BLOCK; NEXT:' + '\n'
    return s
  def set_blocks(self, _list):
    self.blocks = _list
    for i in _list:
      i.containered = True
      debug(BLOCK, 5, 'containered', i)
  def add_block(self, block):
    self.blocks += [block]
    block.containered = True
    debug(BLOCK, 5, 'containered', block)

def structure(block, done = None):
  if done == None:
    done = dict()
    if block.start_st != block.end_st:
      block.dont_clip = True
      # This assumes that clipping is only done one multi-statement blocks.
      debug(BLOCK, 5, 'dontclipping', block)
  found = False
  done[block] = True
  startblock = block
  debug(BLOCK, 3, 'structuring', block, 'n', [str(x) for x in block.next], 'c', [str(x) for x in block.comefrom], 'containered', block.containered, end='')
  if len(block.next) > 0:
    debug(BLOCK, 3, 'nc', [str(x) for x in block.next[0].comefrom], end='')
  debug(BLOCK, 3)
  if len(block.next) == 2:
    do = block.next[0]		# block executed if branch not taken
    skip = block.next[1]	# block executed if branch taken
    if len(do.next) == 1 and do.next[0] == block and not do.containered:
      debug(BLOCK, 3, 'FOUND PRETEST LOOP!!!')
      found = True
      ab = AdvancedBlock()
      ab.type = PRE_LOOP
      assert(block.end_st.op == ssa.BRANCH_COND)

      # fill prolog with all statements that are to be performed
      # before the condition check
      st = block.start_st
      ab.prolog = []
      while st != block.end_st:
        ab.prolog += [st]
        st = st.next[0]

      ab.condition = expr.Expr(expr.NOT, [block.end_st.expr])
      ab.condition.simplify()
      ab.set_blocks([do])
      ab.comefrom = block.comefrom
      ab.start_st = block.start_st
      ab.next = [skip]
      skip.recomefrom([do, block], ab)
      block.relink(ab)
      startblock = ab
    elif (do == block or skip == block) and not block.containered and not block.dont_clip:
      debug(BLOCK, 3, 'FOUND POST LOOP!!!')
      found = True
      ab = AdvancedBlock()
      ab.type = POST_LOOP
      assert(block.end_st.op == ssa.BRANCH_COND)
      ab.condition = block.end_st.expr
      if block.start_st == block.end_st:
        ab.type = EMPTY_LOOP
        ab.blocks = []
      else:
        debug(BLOCK, 4, 'clipping', block)
        assert(len(block.end_st.comefrom) == 1)
        block.end_st = block.end_st.comefrom[0]
        block.clipped = True
        ab.set_blocks([block])

      ab.comefrom = block.comefrom
      ab.start_st = block.start_st

      if skip == block:
        ab.next = [do]
        do.recomefrom([block], ab)
      else:
        # This is not possible on the assembly language level, but it
        # can happen due to transformations performed on the SSA level.
        ab.next = [skip]
        skip.recomefrom([block], ab)
        ab.condition = expr.Expr(expr.NOT, [ab.condition])
        #ab.start_st.add_comment('fishy')

      block.relink(ab)
      startblock = ab
    elif len(do.next) == 1 and len(skip.next) == 1 and \
       do.next[0] == skip.next[0] and not (skip.containered or do.containered) and \
       not block.containered and not block.dont_clip:
      debug(BLOCK, 3, 'FOUND AN IF/THEN/ELSE!!!!')
      found = True
      ab = AdvancedBlock()
      ab.type = IF_THEN_ELSE
      ab.start_st = block.end_st
      ab.condition = block.end_st.expr
      assert(block.end_st.op == ssa.BRANCH_COND)
      debug(BLOCK, 4, 'condition', ab.condition)

      if block.start_st == block.end_st:
        debug(BLOCK, 4, 'relinking', ab)
        block.relink(ab)
        startblock = ab
      else:
        debug(BLOCK, 4, 'clipping', block)
        block.end_st = block.end_st.comefrom[0]
        block.clipped = True
        ab.comefrom = [block]
        debug(BLOCK, 4, 'reended block', block, 'to', block.end_st)

      debug(BLOCK, 4, 'comefrommed', ab, 'to', [str(x) for x in ab.comefrom])
      
      # branch -> then, no branch -> else
      ab.set_blocks([skip, do])
      do.next[0].recomefrom([do, skip], ab)
      ab.next = [do.next[0]]
      debug(BLOCK, 4, 'nexted to', ab.next[0])
      block.next = [ab]
    elif ((len(do.next) == 1 and do.next[0] == skip and not do.containered) or \
         (len(skip.next) == 1 and skip.next[0] == do and not skip.containered) or \
         (do.next == [] and not do.containered) or (skip.next == [] and not skip.containered)) and \
         not block.containered and not block.dont_clip:
      debug(BLOCK, 3, 'FOUND AN IF/THEN!!!')
      found = True
      ab = AdvancedBlock()
      ab.type = IF_THEN
      ab.start_st = block.end_st
      ab.condition = block.end_st.expr
      ab.condition.simplify()
      debug(BLOCK, 4, 'block.end_st', block.end_st)
      assert(block.end_st.op == ssa.BRANCH_COND)
      debug(BLOCK, 4, 'condition', ab.condition)

      if block.start_st == block.end_st:
        debug(BLOCK, 4, 'relinking', ab)
        block.relink(ab)
        startblock = ab
      else:
        debug(BLOCK, 4, 'clipping', block)
        block.end_st = block.end_st.comefrom[0]
        block.clipped = True
        ab.comefrom = [block]
        debug(BLOCK, 4, 'reended block', block, 'to', block.end_st)

      debug(BLOCK, 4, 'comefrommed', ab, 'to', [str(x) for x in ab.comefrom])

      if (len(do.next) == 1 and do.next[0] == skip) or len(do.next) == 0:
        ab.set_blocks([do])
        # "then" block is supposed to be executed if the condition
        # is false, so we have to negate it
        ab.condition = expr.Expr(expr.NOT, [ab.condition])
        ab.condition.simplify()
        ab.next = [skip]
        skip.recomefrom([block, do], ab)
      else:
        ab.set_blocks([skip])
        ab.next = [do]
        do.recomefrom([block, skip], ab)
      debug(BLOCK, 4, 'nexted to', ab.next[0], 'block', ab.blocks[0])
      block.next = [ab]
  elif len(block.next) == 1 and len(block.next[0].next) <= 1 and len(block.next[0].comefrom) == 1 and \
       not block.containered and not block.next[0].containered and not block.next[0] == block:
    ab = AdvancedBlock()
    ab.type = SEQUENCE
    ab.set_blocks([block])
    ab.comefrom = block.comefrom
    debug(BLOCK, 4, 'sequencing block', block, block.next)
    while len(block.next) > 0 and len(block.next[0].next) <= 1 and len(block.next[0].comefrom) == 1 and \
          not block.next[0] in ab.blocks and not block.next[0].containered:
      block = block.next[0]
      ab.add_block(block)
      debug(BLOCK, 4, 'adding block', block, [str(x) for x in block.next], [str(x) for x in block.comefrom])
    startblock.relink(ab)
    ab.next = block.next
    ab.start_st = ab.blocks[0].start_st
    for i in block.next:
      i.recomefrom([block], ab)
    found = True
    startblock = ab
  elif len(block.next) == 1 and len(block.next[0].next) == 2 and \
     (block.next[0].next[0] == block or block.next[0].next[1] == block) and \
     len(block.next[0].comefrom) == 1 and not block.containered and not block.next[0].containered and \
     not block.next[0].dont_clip:
    debug(BLOCK, 3, 'FOUND TWO-BLOCK LOOP!!!')
    found = True
    ab = AdvancedBlock()
    ab.type = POST_LOOP

    # The footer is a couple of insn (optional) and a conditional branch
    # that goes back to block.
    footer = block.next[0]
    assert(footer.end_st.op == ssa.BRANCH_COND)

    if footer.next[1] == block:
      # loop if condition true, no need to negate
      ab.condition = footer.end_st.expr
    else:
      # loop if condition false, negate expression
      ab.condition = expr.Expr(expr.NOT, [footer.end_st.expr])
      ab.condition.simplify()

    debug(BLOCK, 4, 'footer', footer, 'end_st', footer.end_st, 'cf', footer.end_st.comefrom)
    if footer.start_st == footer.end_st:
      # single-insn footer -> contains just the branch, we don't need it
      # anymore
      ab.set_blocks([block])
    else:
      # strip the conditional branch from the footer
      debug(BLOCK, 4, 'clipping', footer)
      footer.end_st = footer.end_st.comefrom[0]
      footer.clipped = True
      ab.set_blocks([block, footer])

    # replace block and footer in the graph with the new advanced block
    # make sure block and footer themselves are not changed, lest we risk
    # problems with the recursion below
    ab.next = list(footer.next)
    ab.next.remove(block)
    assert(len(ab.next) == 1)
    ab.next[0].recomefrom([footer], ab)
    ab.start_st = block.start_st
    block.relink(ab)
    # relink() attaches block's comefrom to ab, but we have to override
    # that to remove the footer
    ab.comefrom = list(block.comefrom)
    ab.comefrom.remove(footer)
    startblock = ab

  # if no structuring could be done, try the successor blocks recursively
  # it is not advisable to recurse if something has been changed because
  # stale information may be propagated up the stack if a startblock has
  # been replaced with something else further down
  if not found and not startblock.containered:
    for n, b in enumerate(startblock.next):
      if not b in done and not b.containered:
        debug(BLOCK, 3, 'recustruct from', startblock, repr(startblock), 'to', b)
        assert(startblock in b.comefrom)
        (startblock.next[n], f) = structure(b, done)
        debug(BLOCK, 4, 'renexted', str(startblock), n, 'to', startblock.next[n])
        if f:
          found = True

  return (startblock, found)
