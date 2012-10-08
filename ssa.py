# ssa.py
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

from operator import attrgetter

from debug import *
from expr import *
from insn import OPC_OUTOFRANGE
from util import *

ASGN = 0
BRANCH_COND = 1
CALL = 2
RETURN = 3
ENDLESS_LOOP = 4
IMPURE = 5	# operation with side-effects, leave it alone

ssacache = dict()
ssa_in_progress = set()

class SSAStatement:
  statement_count = 0
  def __init__(self, dest = None, op = None, expr = None):
    self.next = []
    self.comefrom = []
    self.op = op
    if dest == None:
      dest = []
    elif not isinstance(dest, list):
      dest = [dest]
    self.dest = dest
    self.expr = expr
    self.num = SSAStatement.statement_count
    self.insn = None
    self.reaching = []
    self.call_uses = None
    SSAStatement.statement_count += 1
    self.comment = []
    self.comment_once = []
    
  def desthasmem(self):
    for i in self.dest:
      if i.type == 'M':
        return True
    return False
    
  def __str__(self):
    a = { ASGN: ':=',
          BRANCH_COND: 'bcc',
          CALL: 'call',
          RETURN: 'ret',
          ENDLESS_LOOP: 'eloop',
          IMPURE: 'impure',
        }
    s = str(self.num) + ' '
    if len(self.dest) == 1:
      s += str(self.dest[0]) + ' '
    elif len(self.dest) > 1:
      s += '[ '
      for i in self.dest:
        s += str(i) + ' '
      s += '] '
    if self.call_uses != None:
      s += '[ USED '
      for i in self.call_uses:
        s += str(i) + ' '
      s += '] '
    s += a[self.op] + ' '
    s += str(self.expr) + ' -> '
    for i in self.next:
      s += str(i.num) + ' '
    s += '<- '
    for i in self.comefrom:
      s += str(i.num) + ' '
    if self.insn:
      s += '{' + str(self.insn) + '}'
    if self.reaching and len(self.reaching) > 0 and self.op == RETURN:
      s += ' [ reaching '
      for i in self.reaching:
        s += str(i) + ' '
      s += ']'
    return s
  def chain(self, ctx, st1):
    self.next.append(st1)
    self.reaching = list(ctx.local_indices.values())
    st1.comefrom.append(self)
    if st1.insn == None:
      st1.insn = self.insn

  def add_comment(self, text, once = False):
    debug(SSA, 5, 'adding comment', text, once, 'to', self.num)
    if not once:
      if text not in self.comment:
        self.comment += [text]
    else:
      if text not in self.comment_once:
        self.comment_once += [text]

class SSADef:
  def __init__(self, ctx, dtype, addr=None, idx=None, dessa_tmp=False):
    self.type = dtype
    assert(isinstance(dtype, str))
    self.addr = addr
    key = (dtype, addr)

    if idx == None:
      try:
        self.idx = ctx.graph.indices[key].idx + 1
      except KeyError:
        self.idx = 1
    else:
      self.idx = idx
      if idx == 0 and ctx != None:
        ctx.graph.zeros[key] = self

    if ctx != None:
      ctx.local_indices[key] = self
    if ctx != None and ctx.graph != None:
      ctx.graph.indices[key] = self
    #print('adding', key, 'to index, now', len(graph.indices.values()), 'values,', len(set(graph.indices.values())), 'unique')
    self.define_statement = None
    self.dessa_name = None
    self.is_dessa_tmp = dessa_tmp

  @staticmethod
  def cur(ctx, dtype, addr = None):
    key = (dtype, addr)
    try:
      ret = ctx.local_indices[key]
    except KeyError:
      # Only create a new zero-index def if there isn't one already.
      # If we don't check this, we get duplicate arguments.
      if key in ctx.graph.zeros:
        ret = ctx.graph.zeros[key]
      else:
        ret = SSADef(ctx, dtype, addr, 0)
      ctx.local_indices[key] = ret
    return ret
  
  def __str__(self):
    s = self.type
    if self.addr != None:
      assert(isinstance(self.addr, int))
      s += hex(self.addr)
    s += '(' + str(self.idx) + ')'
    return s

fun_returns_d = dict()
fun_returns_tentative = set()
fun_args_d = dict()
fun_args_tentative = set()

class SSAGraph:
  class SSAifyContext:
    def __init__(self, graph, local_indices=None):
      self.graph = graph
      self._pass = graph._pass
      if local_indices == None:
        self.local_indices = dict()
        # XXX: This is a partial workaround for missing phi functions at
        # function entry points.  Actually, we'd have to define every single
        # memory location as well...
        SSADef(self, 'A', idx=0)
        SSADef(self, 'X', idx=0)
        SSADef(self, 'Y', idx=0)
        SSADef(self, 'C', idx=0)
        SSADef(self, 'Z', idx=0)
        SSADef(self, 'N', idx=0)
        SSADef(self, 'V', idx=0)
      else:
        self.local_indices = local_indices
    def copy(self):
      return SSAGraph.SSAifyContext(self.graph, self.local_indices.copy())

  def __init__(self, iomap, _pass):
    self.start = None
    self.insns = dict()
    self.ssa_for_insn = dict()
    self.last_ssa_for_insn = dict()
    self.ssa_counter = 0
    self.definitions = []
    self.first_insn = None
    self.indices = {}
    self.callers_graphs = []
    self.callers_st = []
    self.callee_graphs = []
    self.actual_returns = None
    self.blocks = None
    self.iomap = iomap
    self.origin = None
    # Definitions with index zero are implicitly created when used.
    # To make sure there is only one such definition per graph, we save
    # the first one created in a graph-wide dictionary and always
    # return this instance.
    self.zeros = dict()
    self._pass = _pass

  def dump(self, level, st = None, dumped = None):
    if not debug_enabled(level):
      return
    if st == None:
      st = self.start
      dumped = dict()

    debug(SSA, level, st)
    dumped[st] = True

    while st.next and len(st.next) == 1 and not st.next[0] in dumped:
      st = st.next[0]
      debug(SSA, level, st)
      dumped[st] = True

    if st.next:
      for i in st.next:
        if not i in dumped:
          self.dump(level, i, dumped)

  def add(self, insn, sp = 0, ctx = None):
    if ctx == None:
      ctx = SSAGraph.SSAifyContext(self)
    if self.first_insn == None:
      self.first_insn = insn
    if insn in self.ssa_for_insn:
      return self.ssa_for_insn[insn]
    (st_start, st_end, sp, next) = self.translate(ctx, insn, sp)
    if next == None:
      # default control flow, use the successors of the insn
      next = insn.next
    if self.start == None:
      self.start = st_start
    if st_end != None and next:
      for i in next:
        if i in self.ssa_for_insn:
          self.update_phis(ctx, self.ssa_for_insn[i])
      
      for i in next:
        new_ctx = ctx.copy()
        next_statement = self.add(i, sp, new_ctx)
        st_end.chain(ctx, next_statement)
        if st_end.op == CALL:
          break

    return st_start

  def update_phis(self, ctx, st):
    debug(SSA, 3, 'updating phis for', st)
    while st.expr and st.expr.type == PHI:
      debug(SSA, 4, 'phi expr', st.expr)
      for d in st.dest:
        curd = SSADef.cur(ctx, d.type, d.addr)
        if curd.idx != d.idx and not curd in st.expr.ops:
          st.expr.ops += [curd]
          debug(SSA, 4, 'added phi', curd, 'to', st)
      st = st.next[0]
  
  def fun_returns(self, ctx, insn, st):
    if not insn in fun_returns_d:
      if insn in ssa_in_progress:
        debug(ARGRET, 1, 'function', hex(insn.addr), 'in progress, cannot get returns')
        fun_returns_tentative.add(insn.addr)
        return []
      ssacache[insn.addr] = ssaify(insn)
      debug(ARGRET, 4, 'ssaified', insn, 'to', ssacache[insn.addr])
    if ctx._pass == 2:
      debug(ARGRET, 4, 'adding', self, 'to callers_graph of', insn, repr(insn))
      ssacache[insn.addr].callers_graphs += [self]
      ssacache[insn.addr].callers_st += [st]
    if not ssacache[insn.addr] in self.callee_graphs:
      self.callee_graphs += [ssacache[insn.addr]]
    rets = fun_returns_d[insn]
    myrets = []
    for i in rets:
      if i.idx != 0:	# saveds are not returns
        myrets += [SSADef(ctx, i.type, i.addr)]
    return myrets
  
  def fun_args(self, ctx, insn, st):
    if not insn in fun_args_d:
      if insn in ssa_in_progress:
        debug(ARGRET, 1, 'function', hex(insn.addr), 'in progress at', hex(st.insn.addr), ', cannot get arguments')
        fun_args_tentative.add(insn.addr)
        return []
      ssacache[insn.addr] = ssaify(insn, None, self.iomap)
    myargs = []
    for i in fun_args_d[insn]:
      myargs += [SSADef.cur(ctx, i.type, i.addr)]
    return myargs
  
  def translate(self, ctx, insn, sp):
    debug(SSA, 2, 'translating', insn, hex(insn.bytes[0]))

    def chain_flags_ldimm(st, imm):
      st1 = SSAStatement(SSADef(ctx, 'N'), ASGN)
      st.chain(ctx, st1)
      st = st1
      if imm > 0x80:
        st.expr = Expr(CONST, [1])
      else:
        st.expr = Expr(CONST, [0])
      st2 = SSAStatement(SSADef(ctx, 'Z'), ASGN)
      st.chain(ctx, st2)
      st = st2
      if imm:
        st.expr = Expr(CONST, [0])
      else:
        st.expr = Expr(CONST, [1])
      return st

    def chain_flags_ld(st, reg):
      op = SSADef.cur(ctx, 'A')
      st1 = SSAStatement(SSADef(ctx, 'N'), ASGN)
      st.chain(ctx, st1)
      st = st1
      st.expr = Expr(COMPARE_GE, [Expr(VAR, [op]), 0x80])
      st2 = SSAStatement(SSADef(ctx, 'Z'), ASGN)
      st.chain(ctx, st2)
      st = st2
      st.expr = Expr(NOT, [op])
      return st

    def chain_flags_incdec(st, reg):
      st1 = SSAStatement(SSADef(ctx, 'Z'), ASGN)
      st.chain(ctx, st1)
      st = st1
      st.expr = Expr(NOT, [reg])
      st2 = SSAStatement(SSADef(ctx, 'N'), ASGN)
      st.chain(ctx, st2)
      st = st2
      st.expr = Expr(COMPARE_GE, [reg, 0x80])
      return st

    def chain_flags_bit(st, mem):
      st1 = SSAStatement(SSADef(ctx, 'N'), ASGN)
      st.chain(ctx, st1)
      st = st1
      st.expr = Expr(BITFLAGS_N, [SSADef.cur(ctx, 'M', mem)])
      st2 = SSAStatement(SSADef(ctx, 'V'), ASGN)
      st.chain(ctx, st2)
      st = st2
      st.expr = Expr(BITFLAGS_V, [SSADef.cur(ctx, 'M', mem)])
      return st

    def chain_flags_or(st, reg, op):
      st1 = SSAStatement(SSADef(ctx, 'N'), ASGN)
      st.chain(ctx, st1)
      st = st1
      st.expr = Expr(ORFLAGS_N, [reg, op])
      st2 = SSAStatement(SSADef(ctx, 'Z'), ASGN)
      st.chain(ctx, st2)
      st = st2
      st.expr = Expr(ORFLAGS_Z, [reg, op])
      return st

    def chain_flags_shl(st, reg, res):
      st1 = SSAStatement(SSADef(ctx, 'N'), ASGN)
      st.chain(ctx, st1)
      st1.expr = Expr(SHFLAGS_N, [res])
      st2 = SSAStatement(SSADef(ctx, 'Z'), ASGN)
      st1.chain(ctx, st2)
      st2.expr = Expr(NOT, [res])
      st3 = SSAStatement(SSADef(ctx, 'C'), ASGN)
      st2.chain(ctx, st3)
      st3.expr = Expr(SHLFLAGS_C, [reg])
      return st3

    def chain_flags_shr(st, reg, res):
      st1 = SSAStatement(SSADef(ctx, 'N'), ASGN)
      st.chain(ctx, st1)
      st1.expr = Expr(SHFLAGS_N, [res])
      st2 = SSAStatement(SSADef(ctx, 'Z'), ASGN)
      st1.chain(ctx, st2)
      st2.expr = Expr(NOT, [res])
      st3 = SSAStatement(SSADef(ctx, 'C'), ASGN)
      st2.chain(ctx, st3)
      st3.expr = Expr(AND, [reg, 1])
      return st3

    def chain_flags_and(st, reg, op):
      st1 = SSAStatement(SSADef(ctx, 'N'), ASGN, Expr(ANDFLAGS_N, [reg, op]))
      st.chain(ctx, st1)
      st2 = SSAStatement(SSADef(ctx, 'Z'), ASGN, Expr(ANDFLAGS_Z, [reg, op]))
      st1.chain(ctx, st2)
      return st2

    def chain_flags_eor(st, reg, op):
      st1 = SSAStatement(SSADef(ctx, 'N'), ASGN, Expr(EORFLAGS_N, [reg, op]))
      st.chain(ctx, st1)
      st2 = SSAStatement(SSADef(ctx, 'Z'), ASGN, Expr(EORFLAGS_Z, [reg, op]))
      st1.chain(ctx, st2)
      return st2

    def chain_flags_adc(st, reg1, reg2, reg3):
      st1 = SSAStatement(SSADef(ctx, 'N'), ASGN, Expr(ADCFLAGS_N, [reg1, reg2, reg3]))
      st.chain(ctx, st1)
      st2 = SSAStatement(SSADef(ctx, 'Z'), ASGN, Expr(ADCFLAGS_Z, [reg1, reg2, reg3]))
      st1.chain(ctx, st2)
      st3 = SSAStatement(SSADef(ctx, 'C'), ASGN, Expr(ADCFLAGS_C, [reg1, reg2, reg3]))
      st2.chain(ctx, st3)
      st4 = SSAStatement(SSADef(ctx, 'V'), ASGN, Expr(ADCFLAGS_V, [reg1, reg2, reg3]))
      st3.chain(ctx, st4)
      return st4

    def chain_flags_sbb(st, reg1, reg2, reg3):
      st1 = SSAStatement(SSADef(ctx, 'N'), ASGN, Expr(SBBFLAGS_N, [reg1, reg2, reg3]))
      st.chain(ctx, st1)
      st2 = SSAStatement(SSADef(ctx, 'Z'), ASGN, Expr(SBBFLAGS_Z, [reg1, reg2, reg3]))
      st1.chain(ctx, st2)
      st3 = SSAStatement(SSADef(ctx, 'C'), ASGN, Expr(SBBFLAGS_C, [reg1, reg2, reg3]))
      st2.chain(ctx, st3)
      st4 = SSAStatement(SSADef(ctx, 'V'), ASGN, Expr(SBBFLAGS_V, [reg1, reg2, reg3]))
      st3.chain(ctx, st4)
      return st4

    def chain_flags_rol(st, reg1, res):
      st1 = SSAStatement(SSADef(ctx, 'N'), ASGN, Expr(SHFLAGS_N, [res]))
      st.chain(ctx, st1)
      st2 = SSAStatement(SSADef(ctx, 'Z'), ASGN, Expr(NOT, [res]))
      st1.chain(ctx, st2)
      st3 = SSAStatement(SSADef(ctx, 'C'), ASGN, Expr(SHR, [reg1, 7]))
      st2.chain(ctx, st3)
      return st3

    def chain_flags_ror(st, reg1, res):
      st1 = SSAStatement(SSADef(ctx, 'N'), ASGN, Expr(SHFLAGS_N, [res]))
      st.chain(ctx, st1)
      st2 = SSAStatement(SSADef(ctx, 'Z'), ASGN, Expr(NOT, [res]))
      st1.chain(ctx, st2)
      st3 = SSAStatement(SSADef(ctx, 'C'), ASGN, Expr(AND, [reg1, 1]))
      st2.chain(ctx, st3)
      return st3

    def emit_flags_subimm(st, reg, imm):
      st.dest = [SSADef(ctx, 'C')]
      st.op = ASGN
      st.expr = Expr(COMPARE_GE, [SSADef.cur(ctx, reg), imm])
      st1 = SSAStatement(SSADef(ctx, 'N'), ASGN, Expr(COMPARE_LT, [SSADef.cur(ctx, reg), imm]))
      st.chain(ctx, st1)
      st2 = SSAStatement(SSADef(ctx, 'Z'), ASGN, Expr(COMPARE_EQ, [SSADef.cur(ctx, reg), imm]))
      st1.chain(ctx, st2)
      return st2

    # normally, add() will follow the flow of the machine code instructions;
    # if we know better (such as with branches with constant conditions), we
    # can put a list of successor instructions here
    next = None

    st = SSAStatement()

    opc = insn.bytes[0]

    if insn == None:
      return None
    
    st_start = st
    self.ssa_for_insn[insn] = st
    st.insn = insn

    if len(insn.comefrom) > 1:
      debug(SSA, 3, 'phiing')
      for g in ctx.local_indices.values():
        st.dest = [SSADef(ctx, g.type, g.addr)]
        st.op = ASGN
        st.expr = Expr(PHI, [g])
        for h in insn.comefrom:
          if h in self.last_ssa_for_insn:
            #print('reaching from', self.last_ssa_for_insn[h], [str(x) + '(' + repr(x) + ')' for x in self.last_ssa_for_insn[h].reaching])
            for i in self.last_ssa_for_insn[h].reaching:
              if i.type == g.type and i.addr == g.addr and not i in st.expr.ops:
                st.expr.ops += [i]
        st1 = SSAStatement()
        st.chain(ctx, st1)
        st = st1
    
    def abs():
      return insn.bytes[1] + (insn.bytes[2] << 8)
    def zp():
      return insn.bytes[1]
    def imm():
      return insn.bytes[1]

    def do_st_abs(reg):
      if self.is_io(abs()):
        st.op = IMPURE
        st.dest = []
        st.expr = Expr(IOOUT, [abs(), SSADef.cur(ctx, reg)])
        st.expr.dont_propagate = True
        st.expr.dont_eliminate = True
      else:
        st.dest = [SSADef(ctx, 'M', abs())]
        st.op = ASGN
        st.expr = Expr(VAR, [SSADef.cur(ctx, reg)])

    def do_ld_abs(reg):
      nonlocal st
      st.dest = [SSADef(ctx, reg)]
      st.op = ASGN
      if self.is_io(abs()):
        st.expr = Expr(IOIN, [abs()])
        st.expr.dont_propagate = True
        st.expr.dont_eliminate = True
      else:
        st.expr = Expr(VAR, [SSADef.cur(ctx, 'M', abs())])
      st = chain_flags_ld(st, reg)

    def do_st_xy(src, addr, reg):
      st.dest = []
      st.op = IMPURE
      if self.is_io(addr):
        st.expr = Expr(IOOUT, [Expr(ADD, [addr, SSADef.cur(ctx, reg)]), SSADef.cur(ctx, src)])
        st.expr.dont_propagate = True
        st.expr.dont_eliminate = True
      else:
        st.expr = Expr(STORE, [SSADef.cur(ctx, src), addr, SSADef.cur(ctx, reg)])

    def do_ld_xy(dst, addr, reg):
      nonlocal st
      st.dest = [SSADef(ctx, dst)]
      st.op = ASGN
      if self.is_io(addr):
        st.expr = Expr(IOIN, [Expr(ADD, [addr, SSADef.cur(ctx, reg)])])
        st.expr.dont_propagate = True
        st.expr.dont_eliminate = True
      else:
        st.expr = Expr(LOAD, [addr, SSADef.cur(ctx, reg)])
      st = chain_flags_ld(st, dst)

    def do_branch(flag, positive):
      nonlocal next, st
      if insn.fake_branch >= 0:
        next = [insn.next[insn.fake_branch]]
        st.op = ASGN
        st.expr = Expr(NOP, [0])
      else:
        st.op = BRANCH_COND
        st.expr = Expr(VAR if positive else NOT, [SSADef.cur(ctx, flag)])
      st.dest = []
    
    if opc == 0x00:	# BRK
      st.dest = []
      st.op = IMPURE
      st.expr = Expr(INTRINSIC, ['brk', imm()])
    elif opc == 0x01:	# ORA (zp,X)
      addr = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
      current_mem = Expr(LOAD, [addr, 0])
      current_a = SSADef.cur(ctx, 'A')
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(OR, [current_a, current_mem])
      st = chain_flags_or(st, current_a, current_mem)
    elif opc == 0x05:	# ORA zp
      current_a = SSADef.cur(ctx, 'A')
      st.op = ASGN
      st.expr = Expr(OR, [current_a, SSADef.cur(ctx, 'M', zp())])
      st.dest = [SSADef(ctx, 'A')]
      st = chain_flags_or(st, current_a, SSADef.cur(ctx, 'M', zp()))
    elif opc == 0x06:	# ASL zp
      current_mem = SSADef.cur(ctx, 'M', zp())
      st.op = ASGN
      st.expr = Expr(SHL, [current_mem, 1])
      st.dest = [SSADef(ctx, 'M', zp())]
      st = chain_flags_shl(st, current_mem, st.expr)
    elif opc == 0x08:	# PHP
      st.dest = [SSADef(ctx, 's', sp)]
      sp -= 1
      st.op = ASGN
      st.expr = Expr(FLAGS, [SSADef.cur(ctx, 'C'),SSADef.cur(ctx, 'Z'),SSADef.cur(ctx, 'N'),SSADef.cur(ctx, 'V')])
    elif opc == 0x09:	# ORA imm
      current_a = SSADef.cur(ctx, 'A')
      st.op = ASGN
      st.expr = Expr(OR, [current_a, imm()])
      st.dest = [SSADef(ctx, 'A')]
      st = chain_flags_or(st, current_a, imm())
    elif opc == 0x0a:	# ASL A
      current_a = SSADef.cur(ctx, 'A')
      st.op = ASGN
      st.expr = Expr(SHL, [current_a, 1])
      st.dest = [SSADef(ctx, 'A')]
      st = chain_flags_shl(st, current_a, st.expr)
    elif opc == 0x0d:	# ORA abs
      current_a = SSADef.cur(ctx, 'A')
      st.op = ASGN
      st.expr = Expr(OR, [current_a, SSADef.cur(ctx, 'M', abs())])
      st.dest = [SSADef(ctx, 'A')]
      st = chain_flags_or(st, current_a, SSADef.cur(ctx, 'M', abs()))
    elif opc == 0x0e:	# ASL abs
      current_mem = SSADef.cur(ctx, 'M', abs())
      st.op = ASGN
      st.expr = Expr(SHL, [current_mem, 1])
      st.dest = [SSADef(ctx, 'M', abs())]
      st = chain_flags_shl(st, current_mem, st.expr)
    elif opc == 0x10:	# BPL dd
      do_branch('N', False)
    elif opc == 0x11:	# ORA (zp),Y
      current_a = SSADef.cur(ctx, 'A')
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      operand = Expr(LOAD, [SSADef.cur(ctx, 'M', zp()), SSADef.cur(ctx, 'Y')])
      st.expr = Expr(OR, [current_a, operand])
      st = chain_flags_or(st, current_a, operand)
    elif opc == 0x15:	# ORA zp,X
      current_a = SSADef.cur(ctx, 'A')
      current_mem = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
      st.expr = Expr(OR, [current_a, current_mem])
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st = chain_flags_or(st, current_a, current_mem)
    elif opc == 0x16:	# ASL zp,X
      current_mem = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
      shlex = Expr(SHL, [current_mem, 1])
      st.dest = []
      st.op = IMPURE
      st.expr = Expr(STORE, [shlex, zp(), SSADef.cur(ctx, 'X')])
      st = chain_flags_shl(st, current_mem, shlex)
    elif opc == 0x18:	# CLC
      st.dest = [SSADef(ctx, 'C')]
      st.expr = Expr(CONST, [0])
      st.op = ASGN
    elif opc == 0x19:	# ORA abs,Y
      current_a = SSADef.cur(ctx, 'A')
      current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'Y')])
      st.expr = Expr(OR, [current_a, current_mem])
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st = chain_flags_or(st, current_a, current_mem)
    elif opc == 0x1d:	# ORA abs,X
      current_a = SSADef.cur(ctx, 'A')
      current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'X')])
      st.expr = Expr(OR, [current_a, current_mem])
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st = chain_flags_or(st, current_a, current_mem)
    elif opc == 0x1e:	# ASL abs,X
      current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'X')])
      shlex = Expr(SHL, [current_mem, 1])
      st.dest = []
      st.op = IMPURE
      st.expr = Expr(STORE, [shlex, abs(), SSADef.cur(ctx, 'X')])
      st = chain_flags_shl(st, current_mem, shlex)
    elif opc == 0x20:	# JSR abs
      st.expr = Expr(ARGS, [abs()] + self.fun_args(ctx, insn.next[1], st))
      st.dest = self.fun_returns(ctx, insn.next[1], st)
      st.op = CALL
    elif opc == 0x21:	# AND (zp,X)
      addr = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
      current_mem = Expr(LOAD, [addr, 0])
      current_a = SSADef.cur(ctx, 'A')
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(AND, [current_a, current_mem])
      st = chain_flags_and(st, current_a, current_mem)
    elif opc == 0x24:	# BIT zp
      st.expr = Expr(COMPARE_EQ, [Expr(AND, [SSADef.cur(ctx, 'A'), SSADef.cur(ctx, 'M', zp())]), 0])
      st.dest = [SSADef(ctx, 'Z')]
      st.op = ASGN
      st = chain_flags_bit(st, zp())
    elif opc == 0x25:	# AND zp
      current_a = SSADef.cur(ctx, 'A')
      current_mem = SSADef.cur(ctx, 'M', zp())
      st.expr = Expr(AND, [current_a, current_mem])
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st = chain_flags_and(st, current_a, current_mem)
    elif opc == 0x26:	# ROL zp
      current_mem = SSADef.cur(ctx, 'M', zp())
      current_c = SSADef.cur(ctx, 'C')
      st.op = ASGN
      st.expr = Expr(OR, [Expr(SHL, [current_mem, 1]), current_c])
      st.expr.dont_propagate = True
      st.dest = [SSADef(ctx, 'M', zp())]
      st = chain_flags_rol(st, current_mem, st.expr)
    elif opc == 0x28:	# PLP
      sp += 1
      flags = SSADef.cur(ctx, 's', sp)
      for i in [('C', DEFLAGS_C), ('Z', DEFLAGS_Z), ('N', DEFLAGS_N), ('V', DEFLAGS_V)]:
        st.op = ASGN
        st.dest = [SSADef(ctx, i[0])]
        st.expr = Expr(i[1], [flags])
        if i[0] != 'V':
          st1 = SSAStatement()
          st.chain(ctx, st1)
          st = st1
    elif opc == 0x29:	# AND imm
      current_a = SSADef.cur(ctx, 'A')
      st.op = ASGN
      st.expr = Expr(AND, [current_a, imm()])
      st.dest = [SSADef(ctx, 'A')]
      st = chain_flags_and(st, current_a, imm())
    elif opc == 0x2a:	# ROL A
      current_a = SSADef.cur(ctx, 'A')
      current_c = SSADef.cur(ctx, 'C')
      st.op = ASGN
      st.expr = Expr(OR, [Expr(SHL, [current_a, 1]), current_c])
      st.expr.dont_propagate = True
      st.dest = [SSADef(ctx, 'A')]
      st = chain_flags_rol(st, current_a, st.expr)
    elif opc == 0x2c:	# BIT abs
      st.expr = Expr(COMPARE_EQ, [Expr(AND, [SSADef.cur(ctx, 'A'), SSADef.cur(ctx, 'M', abs())]), 0])
      st.dest = [SSADef(ctx, 'Z')]
      st.op = ASGN
      st = chain_flags_bit(st, abs())
    elif opc == 0x2d:	# AND abs
      current_a = SSADef.cur(ctx, 'A')
      current_mem = SSADef.cur(ctx, 'M', abs())
      st.expr = Expr(AND, [current_a, current_mem])
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st = chain_flags_and(st, current_a, current_mem)
    elif opc == 0x2e:	# ROL abs
      current_mem = SSADef.cur(ctx, 'M', abs())
      current_c = SSADef.cur(ctx, 'C')
      st.op = ASGN
      st.expr = Expr(OR, [Expr(SHL, [current_mem, 1]), current_c])
      st.expr.dont_propagate = True
      st.dest = [SSADef(ctx, 'M', abs())]
      st = chain_flags_rol(st, current_mem, st.expr)
    elif opc == 0x30:	# BMI dd
      do_branch('N', True)
    elif opc == 0x31:	# AND (zp),Y
      current_mem = Expr(LOAD, [SSADef.cur(ctx, 'M', zp()), SSADef.cur(ctx, 'Y')])
      current_a = SSADef.cur(ctx, 'A')
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(AND, [current_a, current_mem])
      st = chain_flags_and(st, current_a, current_mem)
    elif opc == 0x35:	# AND zp,X
      current_a = SSADef.cur(ctx, 'A')
      current_mem = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
      st.expr = Expr(AND, [current_a, current_mem])
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st = chain_flags_and(st, current_a, current_mem)
    elif opc == 0x36:	# ROL zp,X
      current_mem = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
      current_c = SSADef.cur(ctx, 'C')
      st.op = IMPURE
      rolex = Expr(OR, [Expr(SHL, [current_mem, 1]), current_c])
      rolex.dont_propagate = True
      st.dest = []
      st.expr = Expr(STORE, [rolex, zp(), SSADef.cur(ctx, 'X')])
      st = chain_flags_rol(st, current_mem, rolex)
    elif opc == 0x38:	# SEC
      st.dest = [SSADef(ctx, 'C')]
      st.op = ASGN
      st.expr = Expr(CONST, [1])
    elif opc == 0x39:	# AND abs,Y
      current_a = SSADef.cur(ctx, 'A')
      current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'Y')])
      st.expr = Expr(AND, [current_a, current_mem])
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st = chain_flags_and(st, current_a, current_mem)
    elif opc == 0x3d:	# AND abs,X
      current_a = SSADef.cur(ctx, 'A')
      current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'X')])
      st.expr = Expr(AND, [current_a, current_mem])
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st = chain_flags_and(st, current_a, current_mem)
    elif opc == 0x3e:	# ROL abs,X
      current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'X')])
      current_c = SSADef.cur(ctx, 'C')
      st.op = IMPURE
      rolex = Expr(OR, [Expr(SHL, [current_mem, 1]), current_c])
      rolex.dont_propagate = True
      st.dest = []
      st.expr = Expr(STORE, [rolex, abs(), SSADef.cur(ctx, 'X')])
      st = chain_flags_rol(st, current_mem, rolex)
    elif opc == 0x40:	# RTI
      st.dest = []
      st.op = RETURN
      st.expr = None
      st.add_comment('RTI')
    elif opc == 0x41:	# EOR (zp,X)
      addr = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
      current_mem = Expr(LOAD, [addr, 0])
      current_a = SSADef.cur(ctx, 'A')
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(EOR, [current_a, current_mem])
      st = chain_flags_eor(st, current_a, current_mem)
    elif opc == 0x45:	# EOR zp
      current_a = SSADef.cur(ctx, 'A')
      current_mem = SSADef.cur(ctx, 'M', zp())
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(EOR, [current_a, current_mem])
      st = chain_flags_eor(st, current_a, current_mem)
    elif opc == 0x46:	# LSR zp
      current_mem = SSADef.cur(ctx, 'M', zp())
      st.op = ASGN
      st.expr = Expr(SHR, [current_mem, 1])
      st.dest = [SSADef(ctx, 'M', zp())]
      st = chain_flags_shr(st, current_mem, st.expr)
    elif opc == 0x48:	# PHA
      st.dest = [SSADef(ctx, 's', sp)]
      sp -= 1
      st.op = ASGN
      st.expr = Expr(VAR, [SSADef.cur(ctx, 'A')])
    elif opc == 0x49:	# EOR imm
      current_a = SSADef.cur(ctx, 'A')
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(EOR, [current_a, imm()])
      st = chain_flags_eor(st, current_a, imm())
    elif opc == 0x4a:	# LSR A
      current_a = SSADef.cur(ctx, 'A')
      st.op = ASGN
      st.expr = Expr(SHR, [current_a, 1])
      st.dest = [SSADef(ctx, 'A')]
      st = chain_flags_shr(st, current_a, st.expr)
    elif opc == 0x4c:	# JMP
      if insn.next[0] == insn:
        st.op = ENDLESS_LOOP
        st.expr = None
        st.dest = []
      elif insn.next[0].sym != None:
        # tail call
        if insn.next[0] == ctx.graph.first_insn:
          debug(SSA, 2, 'tail recursion at', insn)
          # recursion causes us grief with args/rets, so we avoid it if
          # possible; here, we can just let the jmp run its course
          st.op = ASGN
          st.dest = []
          st.expr = Expr(NOP, [0])
        else:
          debug(SSA, 2, 'tail call at', insn)
          st.expr = Expr(ARGS, [abs()] + self.fun_args(ctx, insn.next[0], st))
          st.dest = self.fun_returns(ctx, insn.next[0], st)
          st.op = CALL
          st1 = SSAStatement()
          st.chain(ctx, st1)
          st = st1
          st.dest = []
          st.op = RETURN
          st.expr = None
          next = []
      else:
        st.op = ASGN
        st.dest = []
        st.expr = Expr(NOP, [0])
    elif opc == 0x4d:	# EOR abs
      current_a = SSADef.cur(ctx, 'A')
      current_mem = SSADef.cur(ctx, 'M', abs())
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(EOR, [current_a, current_mem])
      st = chain_flags_eor(st, current_a, current_mem)
    elif opc == 0x4e:	# LSR abs
      current_mem = SSADef.cur(ctx, 'M', abs())
      st.op = ASGN
      st.expr = Expr(SHR, [current_mem, 1])
      st.dest = [SSADef(ctx, 'M', abs())]
      st = chain_flags_shr(st, current_mem, st.expr)
    elif opc == 0x50:	# BVC
      do_branch('V', False)
    elif opc == 0x51:	# EOR (zp),Y
      current_a = SSADef.cur(ctx, 'A')
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      operand = Expr(LOAD, [SSADef.cur(ctx, 'M', zp()), SSADef.cur(ctx, 'Y')])
      st.expr = Expr(EOR, [current_a, operand])
      st = chain_flags_eor(st, current_a, operand)
    elif opc == 0x55:	# EOR zp,X
      current_a = SSADef.cur(ctx, 'A')
      current_mem = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
      st.expr = Expr(EOR, [current_a, current_mem])
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st = chain_flags_eor(st, current_a, current_mem)
    elif opc == 0x56:	# LSR zp,X
      current_mem = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
      shrex = Expr(SHR, [current_mem, 1])
      st.dest = []
      st.op = IMPURE
      st.expr = Expr(STORE, [shrex, zp(), SSADef.cur(ctx, 'X')])
      st = chain_flags_shr(st, current_mem, shrex)
    elif opc == 0x58:	# CLI
      st.dest = []
      st.op = IMPURE
      st.expr = Expr(INTRINSIC, ['cli'])
    elif opc == 0x59:	# EOR abs,Y
      current_a = SSADef.cur(ctx, 'A')
      current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'Y')])
      st.expr = Expr(EOR, [current_a, current_mem])
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st = chain_flags_eor(st, current_a, current_mem)
    elif opc == 0x5d:	# EOR abs,X
      current_a = SSADef.cur(ctx, 'A')
      current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'X')])
      st.expr = Expr(EOR, [current_a, current_mem])
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st = chain_flags_eor(st, current_a, current_mem)
    elif opc == 0x5e:	# LSR abs,X
      current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'X')])
      shrex = Expr(SHR, [current_mem, 1])
      st.dest = []
      st.op = IMPURE
      st.expr = Expr(STORE, [shrex, abs(), SSADef.cur(ctx, 'X')])
      st = chain_flags_shr(st, current_mem, shrex)
    elif opc == 0x60:	# RTS
      st.dest = []
      st.op = RETURN
      st.expr = None
    elif opc == 0x61:	# ADC (zp,X)
      addr = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
      current_a = SSADef.cur(ctx, 'A')
      current_mem = Expr(LOAD, [addr, 0])
      current_c = SSADef.cur(ctx, 'C')
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(ADD, [current_a, current_mem, current_c])
      st = chain_flags_adc(st, current_a, current_mem, current_c)
    elif opc == 0x65:	# ADC zp
      current_a = SSADef.cur(ctx, 'A')
      current_mem = SSADef.cur(ctx, 'M', zp())
      current_c = SSADef.cur(ctx, 'C')
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(ADD, [current_a, current_mem, current_c])
      st = chain_flags_adc(st, current_a, current_mem, current_c)
    elif opc == 0x66:	# ROR zp
      current_mem = SSADef.cur(ctx, 'M', zp())
      current_c = SSADef.cur(ctx, 'C')
      st.op = ASGN
      st.expr = Expr(OR, [Expr(SHR, [current_mem, 1]), Expr(SHL, [current_c, 7])])
      st.expr.dont_propagate = True
      st.dest = [SSADef(ctx, 'M', zp())]
      st = chain_flags_ror(st, current_mem, st.expr)
    elif opc == 0x68:	# PLA
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      sp += 1
      st.expr = Expr(VAR, [SSADef.cur(ctx, 's', sp)])
      st = chain_flags_ld(st, 'A')
    elif opc == 0x69:	# ADC imm
      current_a = SSADef.cur(ctx, 'A')
      current_c = SSADef.cur(ctx, 'C')
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(ADD, [current_a, imm(), current_c])
      st = chain_flags_adc(st, current_a, imm(), current_c)
    elif opc == 0x6a:	# ROR A
      current_a = SSADef.cur(ctx, 'A')
      current_c = SSADef.cur(ctx, 'C')
      st.op = ASGN
      st.expr = Expr(OR, [Expr(SHR, [current_a, 1]), Expr(SHL, [current_c, 7])])
      st.expr.dont_propagate = True
      st.dest = [SSADef(ctx, 'A')]
      st = chain_flags_ror(st, current_a, st.expr)
    elif opc == 0x6c:	# JMP ind
      st.dest = []
      st.op = IMPURE
      st.expr = Expr(INTRINSIC, ['jmp', SSADef.cur(ctx, 'M', abs())])
      st.add_comment('XXX: indirect jump not implemented yet')
    elif opc == 0x6d:	# ADC abs
      current_a = SSADef.cur(ctx, 'A')
      current_mem = SSADef.cur(ctx, 'M', abs())
      current_c = SSADef.cur(ctx, 'C')
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(ADD, [current_a, current_mem, current_c])
      st = chain_flags_adc(st, current_a, current_mem, current_c)
    elif opc == 0x6e:	# ROR abs
      current_mem = SSADef.cur(ctx, 'M', abs())
      current_c = SSADef.cur(ctx, 'C')
      st.op = ASGN
      st.expr = Expr(OR, [Expr(SHR, [current_mem, 1]), Expr(SHL, [current_c, 7])])
      st.expr.dont_propagate = True
      st.dest = [SSADef(ctx, 'M', abs())]
      st = chain_flags_ror(st, current_mem, st.expr)
    elif opc == 0x70:	# BVS dd
      do_branch('V', True)
    elif opc == 0x71:	# ADC (zp),Y
      current_a = SSADef.cur(ctx, 'A')
      current_c = SSADef.cur(ctx, 'C')
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      operand = Expr(LOAD, [SSADef.cur(ctx, 'M', zp()), SSADef.cur(ctx, 'Y')])
      st.expr = Expr(ADD, [current_a, operand, current_c])
      st = chain_flags_adc(st, current_a, operand, current_c)
    elif opc == 0x75:	# ADC zp,X
      current_a = SSADef.cur(ctx, 'A')
      current_mem = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
      current_c = SSADef.cur(ctx, 'C')
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(ADD, [current_a, current_mem, current_c])
      st = chain_flags_adc(st, current_a, current_mem, current_c)
    elif opc == 0x76:	# ROR zp,X
      current_mem = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
      current_c = SSADef.cur(ctx, 'C')
      st.op = IMPURE
      rorex = Expr(OR, [Expr(SHR, [current_mem, 1]), Expr(SHL, [current_c, 7])])
      rorex.dont_propagate = True
      st.dest = []
      st.expr = Expr(STORE, [rorex, zp(), SSADef.cur(ctx, 'X')])
      st = chain_flags_ror(st, current_mem, rorex)
    elif opc == 0x78: 	# SEI
      st.dest = []
      st.op = IMPURE
      st.expr = Expr(INTRINSIC, ['sei'])
    elif opc == 0x79:	# ADC abs,Y
      current_a = SSADef.cur(ctx, 'A')
      current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'Y')])
      current_c = SSADef.cur(ctx, 'C')
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(ADD, [current_a, current_mem, current_c])
      st = chain_flags_adc(st, current_a, current_mem, current_c)
    elif opc == 0x7d:	# ADC abs,X
      current_a = SSADef.cur(ctx, 'A')
      current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'X')])
      current_c = SSADef.cur(ctx, 'C')
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(ADD, [current_a, current_mem, current_c])
      st = chain_flags_adc(st, current_a, current_mem, current_c)
    elif opc == 0x7e:	# ROR abs,X
      current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'X')])
      current_c = SSADef.cur(ctx, 'C')
      st.op = IMPURE
      rorex = Expr(OR, [Expr(SHR, [current_mem, 1]), Expr(SHL, [current_c, 7])])
      rorex.dont_propagate = True
      st.dest = []
      st.expr = Expr(STORE, [rorex, abs(), SSADef.cur(ctx, 'X')])
      st = chain_flags_ror(st, current_mem, rorex)
    elif opc == 0x81:	# STA (zp,X)
      addr = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
      st.op = IMPURE
      st.dest = []
      st.expr = Expr(STORE, [SSADef.cur(ctx, 'A'), addr, 0])
    elif opc == 0x84:	# STY zp
      st.dest = [SSADef(ctx, 'M', zp())]
      st.op = ASGN
      st.expr = Expr(VAR, [SSADef.cur(ctx, 'Y')])
    elif opc == 0x85:	# STA zp
      st.dest = [SSADef(ctx, 'M', zp())]
      st.op = ASGN
      st.expr = Expr(VAR, [SSADef.cur(ctx, 'A')])
    elif opc == 0x86:	# STX zp
      st.dest = [SSADef(ctx, 'M', zp())]
      st.op = ASGN
      st.expr = Expr(VAR, [SSADef.cur(ctx, 'X')])
    elif opc == 0x88:	# DEY
      st.expr = Expr(SUB, [SSADef.cur(ctx, 'Y'), 1])
      st.dest = [SSADef(ctx, 'Y')]
      st.op = ASGN
      st = chain_flags_incdec(st, SSADef.cur(ctx, 'Y'))
    elif opc == 0x8a:	# TXA
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(VAR, [SSADef.cur(ctx, 'X')])
      st = chain_flags_ld(st, 'A')
    elif opc == 0x8c:	# STY abs
      do_st_abs('Y')
    elif opc == 0x8d:	# STA abs
      do_st_abs('A')
    elif opc == 0x8e:	# STX abs
      do_st_abs('X')
    elif opc == 0x90:	# BCC dd
      do_branch('C', False)
    elif opc == 0x91:	# STA (zp),Y
      current_ind = SSADef.cur(ctx, 'M', zp())
      st.dest = []
      st.op = IMPURE
      st.expr = Expr(STORE, [SSADef.cur(ctx, 'A'), current_ind, SSADef.cur(ctx, 'Y')])
    elif opc == 0x94:	# STY zp,X
      do_st_xy('Y', zp(), 'X')
    elif opc == 0x95:	# STA zp,X
      do_st_xy('A', zp(), 'X')
    elif opc == 0x96:	# STX zp,Y
      do_st_xy('X', zp(), 'Y')
    elif opc == 0x98:	# TYA
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(VAR, [SSADef.cur(ctx, 'Y')])
      st = chain_flags_ld(st, 'A')
    elif opc == 0x99:	# STA abs,Y
      do_st_xy('A', abs(), 'Y')
    elif opc == 0x9a:	# TXS
      st.dest = []
      st.op = IMPURE
      st.expr = Expr(INTRINSIC, ['setsp', SSADef.cur(ctx, 'X')])
    elif opc == 0x9d:	# STA abs,X
      do_st_xy('A', abs(), 'X')
    elif opc == 0xa0:	# LDY imm
      st.dest = [SSADef(ctx, 'Y')]
      st.op = ASGN
      st.expr = Expr(CONST, [imm()])
      st = chain_flags_ldimm(st, imm())
    elif opc == 0xa1:	# LDA (zp,X)
      addr = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(VAR, [Expr(LOAD, [addr, 0])])
      st = chain_flags_ld(st, 'A')
    elif opc == 0xa2:	# LDX imm
      st.dest = [SSADef(ctx, 'X')]
      st.op = ASGN
      st.expr = Expr(CONST, [imm()])
      st = chain_flags_ldimm(st, imm())
    elif opc == 0xa4:	# LDY zp
      st.dest = [SSADef(ctx, 'Y')]
      st.op = ASGN
      st.expr = Expr(VAR, [SSADef.cur(ctx, 'M', zp())])
      st = chain_flags_ld(st, 'Y')
    elif opc == 0xa5:	# LDA zp
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(VAR, [SSADef.cur(ctx, 'M', zp())])
      st = chain_flags_ld(st, 'A')
    elif opc == 0xa6:	# LDX zp
      st.dest = [SSADef(ctx, 'X')]
      st.op = ASGN
      st.expr = Expr(VAR, [SSADef.cur(ctx, 'M', zp())])
      st = chain_flags_ld(st, 'X')
    elif opc == 0xa8:	# TAY
      st.dest = [SSADef(ctx, 'Y')]
      st.op = ASGN
      st.expr = Expr(VAR, [SSADef.cur(ctx, 'A')])
      st = chain_flags_ld(st, 'Y')
    elif opc == 0xa9:	# LDA imm
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(CONST, [imm()])
      st = chain_flags_ldimm(st, imm())
    elif opc == 0xaa:	# TAX
      st.dest = [SSADef(ctx, 'X')]
      st.op = ASGN
      st.expr = Expr(VAR, [SSADef.cur(ctx, 'A')])
      st = chain_flags_ld(st, 'X')
    elif opc == 0xac:	# LDY abs
      do_ld_abs('Y')
    elif opc == 0xad:	# LDA abs
      do_ld_abs('A')
    elif opc == 0xae:	# LDX abs
      do_ld_abs('X')
    elif opc == 0xb0:	# BCS dd
      do_branch('C', True)
    elif opc == 0xb1:	# LDA (zp),Y
      current_ind = SSADef.cur(ctx, 'M', zp())
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(LOAD, [current_ind, SSADef.cur(ctx, 'Y')])
      st = chain_flags_ld(st, 'A')
    elif opc == 0xb4:	# LDY zp,X
      do_ld_xy('Y', zp(), 'X')
    elif opc == 0xb5:	# LDA zp,X
      do_ld_xy('A', zp(), 'X')
    elif opc == 0xb6:	# LDX zp,Y
      do_ld_xy('X', zp(), 'Y')
    elif opc == 0xb8:	# CLV
      st.op = ASGN
      st.dest = [SSADef(ctx, 'V')]
      st.expr = Expr(CONST, [0])
    elif opc == 0xb9:	# LDA abs,Y
      do_ld_xy('A', abs(), 'Y')
    elif opc == 0xba:	# TSX
      st.dest = [SSADef(ctx, 'X')]
      st.op = ASGN
      st.expr = Expr(INTRINSIC, ['getsp'])
    elif opc == 0xbc:	# LDY abs,X
      do_ld_xy('Y', abs(), 'X')
    elif opc == 0xbd:	# LDA abs,X
      do_ld_xy('A', abs(), 'X')
    elif opc == 0xbe:	# LDX abs,Y
      do_ld_xy('X', abs(), 'Y')
    elif opc == 0xc0:	# CPY imm
      st = emit_flags_subimm(st, 'Y', imm())
    elif opc == 0xc1:	# CMP (zp,X)
      addr = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
      st = emit_flags_subimm(st, 'A', Expr(LOAD, [addr, 0]))
    elif opc == 0xc4:	# CPY zp
      st = emit_flags_subimm(st, 'Y', SSADef.cur(ctx, 'M', zp()))
    elif opc == 0xc5:	# CMP zp
      st = emit_flags_subimm(st, 'A', SSADef.cur(ctx, 'M', zp()))
    elif opc == 0xc6:	# DEC zp
      current_mem = SSADef.cur(ctx, 'M', zp())
      st.expr = Expr(SUB, [current_mem, 1])
      st.dest = [SSADef(ctx, 'M', zp())]
      st.op = ASGN
      st = chain_flags_incdec(st, SSADef.cur(ctx, 'M', zp()))
    elif opc == 0xc8:	# INY
      st.expr = Expr(ADD, [SSADef.cur(ctx, 'Y'), 1])
      st.dest = [SSADef(ctx, 'Y')]
      st.op = ASGN
      st = chain_flags_incdec(st, SSADef.cur(ctx, 'Y'))
    elif opc == 0xc9:	# CMP imm
      st = emit_flags_subimm(st, 'A', imm())
    elif opc == 0xca:	# DEX
      current_x = SSADef.cur(ctx, 'X')
      st.expr = Expr(SUB, [current_x, 1])
      st.dest = [SSADef(ctx, 'X')]
      st.op = ASGN
      st = chain_flags_incdec(st, SSADef.cur(ctx, 'X'))
    elif opc == 0xcc:	# CPY abs
      st = emit_flags_subimm(st, 'Y', SSADef.cur(ctx, 'M', abs()))
    elif opc == 0xcd:	# CMP abs
      st = emit_flags_subimm(st, 'A', SSADef.cur(ctx, 'M', abs()))
    elif opc == 0xce:	# DEC abs
      current_mem = SSADef.cur(ctx, 'M', abs())
      st.expr = Expr(SUB, [current_mem, 1])
      st.dest = [SSADef(ctx, 'M', abs())]
      st.op = ASGN
      st = chain_flags_incdec(st, SSADef.cur(ctx, 'M', abs()))
    elif opc == 0xd0:	# BNE dd
      do_branch('Z', False)
    elif opc == 0xd1:	# CMP (zp),Y
      operand = Expr(LOAD, [SSADef.cur(ctx, 'M', zp()), SSADef.cur(ctx, 'Y')])
      st = emit_flags_subimm(st, 'A', operand)
    elif opc == 0xd5:	# CMP zp,X
      st = emit_flags_subimm(st, 'A', Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')]))
    elif opc == 0xd6:	# DEC zp,X
      current_mem = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
      subex = Expr(SUB, [current_mem, 1])
      st.dest = []
      st.op = IMPURE
      st.expr = Expr(STORE, [subex, zp(), SSADef.cur(ctx, 'X')])
      st = chain_flags_incdec(st, subex)
    elif opc == 0xd8:	# CLD
      st.dest = []
      st.op = IMPURE
      st.expr = Expr(INTRINSIC, ['cld'])
      st.add_comment('XXX: CLD unimplemented')
    elif opc == 0xd9:	# CMP abs,Y
      st = emit_flags_subimm(st, 'A', Expr(LOAD, [abs(), SSADef.cur(ctx, 'Y')]))
    elif opc == 0xdd:	# CMP abs,X
      st = emit_flags_subimm(st, 'A', Expr(LOAD, [abs(), SSADef.cur(ctx, 'X')]))
    elif opc == 0xde:	# DEC abs,X
      current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'X')])
      subex = Expr(SUB, [current_mem, 1])
      st.dest = []
      st.op = IMPURE
      st.expr = Expr(STORE, [subex, abs(), SSADef.cur(ctx, 'X')])
      st = chain_flags_incdec(st, subex)
    elif opc == 0xe0:	# CPX imm
      st = emit_flags_subimm(st, 'X', imm())
    elif opc == 0xe1:	# SBC (zp,X)
      addr = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
      current_a = SSADef.cur(ctx, 'A')
      current_mem = Expr(LOAD, [addr, 0])
      current_borrow = Expr(SUB, [1, SSADef.cur(ctx, 'C')])
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(SUB, [current_a, current_mem, current_borrow])
      st = chain_flags_sbb(st, current_a, current_mem, current_borrow)
    elif opc == 0xe4:	# CPX zp
      st = emit_flags_subimm(st, 'X', SSADef.cur(ctx, 'M', zp()))
    elif opc == 0xe5:	# SBC zp
      current_a = SSADef.cur(ctx, 'A')
      current_mem = SSADef.cur(ctx, 'M', zp())
      current_borrow = Expr(SUB, [1, SSADef.cur(ctx, 'C')])
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(SUB, [current_a, current_mem, current_borrow])
      st = chain_flags_sbb(st, current_a, current_mem, current_borrow)
    elif opc == 0xe6:	# INC zp
      current_mem = SSADef.cur(ctx, 'M', zp())
      st.expr = Expr(ADD, [current_mem, 1])
      st.dest = [SSADef(ctx, 'M', zp())]
      st.op = ASGN
      st = chain_flags_incdec(st, SSADef.cur(ctx, 'M', zp()))
    elif opc == 0xe8:	# INX
      current_x = SSADef.cur(ctx, 'X')
      st.expr = Expr(ADD, [current_x, 1])
      st.dest = [SSADef(ctx, 'X')]
      st.op = ASGN
      st = chain_flags_incdec(st, SSADef.cur(ctx, 'X'))
    elif opc == 0xe9:	# SBC imm
      current_a = SSADef.cur(ctx, 'A')
      current_borrow = Expr(SUB, [1, SSADef.cur(ctx, 'C')])
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(SUB, [current_a, imm(), current_borrow])
      st = chain_flags_sbb(st, current_a, imm(), current_borrow)
    elif opc == 0xea:	# NOP
      st.op = ASGN
      st.dest = []
      st.expr = Expr(NOP, [0])
    elif opc == 0xec:	# CPX abs
      st = emit_flags_subimm(st, 'X', SSADef.cur(ctx, 'M', abs()))
    elif opc == 0xed:	# SBC abs
      current_a = SSADef.cur(ctx, 'A')
      current_mem = SSADef.cur(ctx, 'M', abs())
      current_borrow = Expr(SUB, [1, SSADef.cur(ctx, 'C')])
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(SUB, [current_a, current_mem, current_borrow])
      st = chain_flags_sbb(st, current_a, current_mem, current_borrow)
    elif opc == 0xee:	# INC abs
      current_mem = SSADef.cur(ctx, 'M', abs())
      st.expr = Expr(ADD, [current_mem, 1])
      st.dest = [SSADef(ctx, 'M', abs())]
      st.op = ASGN
      st = chain_flags_incdec(st, SSADef.cur(ctx, 'M', abs()))
    elif opc == 0xf0:	# BEQ dd
      do_branch('Z', True)
    elif opc == 0xf1:	# SBC (zp),Y
      current_a = SSADef.cur(ctx, 'A')
      current_mem = Expr(LOAD, [SSADef.cur(ctx, 'M', zp()), SSADef.cur(ctx, 'Y')])
      current_borrow = Expr(SUB, [1, SSADef.cur(ctx, 'C')])
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(SUB, [current_a, current_mem, current_borrow])
      st = chain_flags_sbb(st, current_a, current_mem, current_borrow)
    elif opc == 0xf5:	# SBC zp,X
      current_a = SSADef.cur(ctx, 'A')
      current_mem = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
      current_borrow = Expr(SUB, [1, SSADef.cur(ctx, 'C')])
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(SUB, [current_a, current_mem, current_borrow])
      st = chain_flags_sbb(st, current_a, current_mem, current_borrow)
    elif opc == 0xf6:	# INC zp,X
      current_mem = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
      result = Expr(ADD, [current_mem, 1])
      st.expr = Expr(STORE, [result, zp(), SSADef.cur(ctx, 'X')])
      st.dest = []
      st.op = IMPURE
      st = chain_flags_incdec(st, result)
    elif opc == 0xf8:	# SED
      st.dest = []
      st.op = IMPURE
      st.expr = Expr(INTRINSIC, ['sed'])
      st.add_comment('XXX: SED unimplemented')
    elif opc == 0xf9:	# SBC abs,Y
      current_a = SSADef.cur(ctx, 'A')
      current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'Y')])
      current_borrow = Expr(SUB, [1, SSADef.cur(ctx, 'C')])
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(SUB, [current_a, current_mem, current_borrow])
      st = chain_flags_sbb(st, current_a, current_mem, current_borrow)
    elif opc == 0xfd:	# SBC abs,X
      current_a = SSADef.cur(ctx, 'A')
      current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'X')])
      current_borrow = Expr(SUB, [1, SSADef.cur(ctx, 'C')])
      st.dest = [SSADef(ctx, 'A')]
      st.op = ASGN
      st.expr = Expr(SUB, [current_a, current_mem, current_borrow])
      st = chain_flags_sbb(st, current_a, current_mem, current_borrow)
    elif opc == 0xfe:	# INC abs,X
      current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'X')])
      result = Expr(ADD, [current_mem, 1])
      st.expr = Expr(STORE, [result, abs(), SSADef.cur(ctx, 'X')])
      st.dest = []
      st.op = IMPURE
      st = chain_flags_incdec(st, result)
    elif opc == OPC_OUTOFRANGE:
      st.dest = []
      st.op = IMPURE
      st.expr = Expr(INTRINSIC, ['thunk', insn.addr])
    elif opc in [      0x02, 0x03, 0x04, 0x07,             0x0b, 0x0c,       0x0f,
                       0x12, 0x13, 0x14, 0x17,       0x1a, 0x1b, 0x1c,       0x1f,
                       0x22, 0x23,       0x27,             0x2b,             0x2f,
                       0x32, 0x33, 0x34, 0x37,       0x3a, 0x3b, 0x3c,       0x3f,
                       0x42, 0x43, 0x44, 0x47,             0x4b,             0x4f,
                       0x52, 0x53, 0x54, 0x57,       0x5a, 0x5b, 0x5c,       0x5f,
                       0x62, 0x63, 0x64, 0x67,             0x6b,             0x6f,
                       0x72, 0x73, 0x74, 0x77,       0x7a, 0x7b, 0x7c,       0x7f,
                 0x80, 0x82, 0x83,       0x87, 0x89,       0x8b,             0x8f,
                       0x92, 0x93,       0x97,             0x9b, 0x9c, 0x9e, 0x9f,
                             0xa3,       0xa7,             0xab,             0xaf,
                       0xb2, 0xb3,       0xb7,             0xbb,             0xbf,
                       0xc2, 0xc3,       0xc7,             0xcb,             0xcf,
                       0xd2, 0xd3, 0xd4, 0xd7,       0xda, 0xdb, 0xdc,       0xdf,
                       0xe2, 0xe3,       0xe7,             0xeb,             0xef,
                       0xf2, 0xf3, 0xf4, 0xf7,       0xfa, 0xfb, 0xfc,       0xff]:
      # illegal opcode
      # XXX: add switch to allow 'useful' illegal opcodes
      st.op = IMPURE
      st.expr = Expr(INTRINSIC, ['illegal', opc])
      st.dest = []
      st.add_comment('XXX: unimplemented illegal opcode')
    else:
      raise InternalError('unknown opcode ' + hex(opc))

    # all current indices are reaching, with the exception of anything
    # below the stack pointer
    st.reaching = []
    for i in ctx.local_indices.values():
      if i.type != 's':# or i.addr > sp:
        st.reaching += [i]

    self.last_ssa_for_insn[insn] = st
    return (st_start, st, sp, next)

  def getall(self, st = None, got = None, all = None):
    if st == None:
      st = self.start
      got = dict()
      all = []

    all += [st]
    got[st] = True
    
    while st.next and len(st.next) == 1 and not st.next[0] in got:
      st = st.next[0]
      all += [st]
      got[st] = True
      
    if st.next:
      for i in st.next:
        if not i in got:
          self.getall(i, got, all)
    return all

  def dce(self):
    eliminated = True
    while eliminated:
      if self.actual_returns != None:
        definitions = self.actual_returns
      else:
        definitions = self.definitions
      
      alluses = []
      use_statements = dict()
      all = self.getall()
      for i in all:
        if i.expr:
          uses = i.expr.getallops()
          for j in uses:
            if isinstance(j, SSADef):
              alluses += [j]
              if j in use_statements:
                use_statements[j] += [i]
              else:
                use_statements[j] = [i]

      alluses += definitions
      
      debug(SSA, 3, len(alluses))
      alluses = set(alluses)
      debug(SSA, 3, len(alluses))
      
      #print('DCE uses', [str(x) for x in alluses])
      eliminated = False
      for i in all:
        if i.op == ASGN and \
           ((not i.desthasmem()) or i.expr.type == PHI) and \
           len(set(i.dest) & alluses) == 0 and \
           len(set(i.dest) & set(definitions)) == 0 and \
           not i in i.next and not i.expr.dont_eliminate:
          debug(SSA, 4, 'eliminate', i.num)
          eliminated = True
          assert(len(i.next) == 1)
          if len(i.comefrom) > 0:
            # replace us with our successor in predecessors' next
            for j in i.comefrom:
              j.next = [i.next[0] if x == i else x for x in j.next]
          # remove ourselves from successor's comefrom
          if i in i.next[0].comefrom:
            i.next[0].comefrom.remove(i)
          # add our predecessors to successor's comefrom
          for j in i.comefrom:
            if not j in i.next[0].comefrom:
              i.next[0].comefrom += [j]
          if self.start == i:
            self.start = i.next[0]
        elif i.op == ASGN and i.expr.type == PHI and i.dest[0] in use_statements and len(set(i.dest) & set(definitions)) == 0:
          # eliminate phi loops
          # this function checks if a phi definition is used in any non-phi expression
          def has_non_phi_uses(df, done = None):
            if done == None:
              done = dict()
            if df in done:
              #print('already checked', df)
              return done[df]
            done[df] = False
            if not df in use_statements:
              #print('no uses found for', df)
              done[df] = False
              return False
            for j in use_statements[df]:
              #print('phicheck', j)
              if j.op != ASGN or (j.expr and j.expr.type != PHI):
                done[df] = True
                return True
              elif has_non_phi_uses(j.dest[0], done):
                  done[df] = True
                  return True
            done[df] = False
            return False

          if not has_non_phi_uses(i.dest[0]):
            debug(SSA, 4, 'eliminate phi-only', i.num)

            for j in use_statements[i.dest[0]]:
              # Remove the definition from all phi expressions it is used in.
              debug(SSA, 6, 'removing it from', j)
              j.expr.ops.remove(i.dest[0])
              # Doing this frequently produces empty phi functions without
              # any operands. These expressions make no sense, but are
              # expected to be eliminated in this or subsequent DCE runs.
              # It is, however, possible that propagation is performed
              # before that happens, and it would consider all such
              # definitions equivalent, messing the program up completely.
              if len(j.expr.ops) == 0:
                j.expr.dont_propagate = True

            eliminated = True
            i.dest = []
            i.expr.type = NOP
            i.expr.ops = [0]

        elif i.op == CALL:
          i.call_uses = []
          for j in i.dest:
            if j in alluses:
              i.call_uses += [j]
        
      #self.dump()
  
  def find_definitions(self, st = None, done = None):
    self.definitions = []
    for i in self.getall():
      if i.op == RETURN:
        for j in i.reaching:
          if not j in self.definitions:
            self.definitions += [j]

  def find_args(self):
    args = []
    for i in self.getall():
      if i.expr:
        for j in i.expr.getallops():
          if isinstance(j, SSADef) and j.idx == 0 and not j in args:
            args += [j]
    args.sort(key = attrgetter('type'))
    debug(ARGRET, 1, 'args:', [str(x) for x in args])
    fun_args_d[self.first_insn] = args
  
  def find_rets(self):
    if self.actual_returns != None:
      definitions = self.actual_returns
    else:
      definitions = self.definitions
    debug(ARGRET, 1, 'rets:', [str(x) for x in definitions])
    debug(ARGRET, 4, 'adding', self.first_insn, 'for', self, 'to fun_returns_d')
    fun_returns_d[self.first_insn] = definitions
  
  def dereach(self):
    for i in self.getall():
      if i.reaching and i.op != RETURN:
        i.reaching = None
  
  #@profile
  def propagate(self):
    uses = dict()
    uses_defs = dict()
    for k in self.getall():
      # get all expression operands
      if isinstance(k.expr, Expr):
        for l in k.expr.getallops():
          if isinstance(l, SSADef):
            #print('deeping', m, 'in', k)
            if l in uses:
              uses[l] += [k]
            else:
              uses[l] = [k]
      # get all dests
      for l in k.dest:
        if isinstance(l, SSADef):
          #print('deeping', m, 'in', k)
          if l in uses:
            uses[l] += [k]
          else:
            uses[l] = [k]
      # get all reachings
      if k.reaching != None:
        for l in k.reaching:
          if isinstance(l, SSADef):
            if l in uses_defs:
              uses_defs[l] += [k]
            else:
              uses_defs[l] = [k]

    for i in self.getall():
      # link to defining statement
      for j in i.dest:
        j.define_statement = i
      
      # remove duplicate args in phi functions
      if isinstance(i.expr, Expr) and i.expr.type == PHI and len(set(i.expr.ops)) != len(i.expr.ops):
        nops = []
        for j in i.expr.ops:
          if not j in nops:
            nops += [j]
        i.expr.ops = nops
      
      # eliminate phi functions with only one operand
      if isinstance(i.expr, Expr) and i.expr.type == PHI and len(i.expr.ops) == 1:
        debug(SSA, 3, 'dephiing', i)
        i.expr.type = NOP
        # rename uses of i.dest
        if i.dest[0] in uses:
          for k in uses[i.dest[0]]:
            # operands
            if isinstance(k.expr, Expr):
              if k.expr.type == PHI and k.dest[0] == i.expr.ops[0]:
                debug(SSA, 6, 'remove', i.dest[0], 'from phi', k)
                k.expr.remove(i.dest[0])
              else:
                k.expr.substitute(i.dest[0], i.expr.ops[0])
                debug(SSA, 6, 'subbing', i.dest[0], 'for', i.expr.ops[0], 'in', k)
                # Make sure to add the new definition to uses so it
                # can itself be replaced if necessary.
                if i.expr.ops[0] in uses:
                  uses[i.expr.ops[0]].append(k)
                else:
                  uses[i.expr.ops[0]] = [k]
        if i.dest[0] in uses_defs:
          for k in uses_defs[i.dest[0]]:
            # reachings
            if k.reaching and k.reaching != []:
              debug(SSA, 4, 'rereaching', i.dest[0], 'to', i.expr.ops[0], 'in', k)
              k.reaching = [x if x != i.dest[0] else i.expr.ops[0] for x in k.reaching]

              # Make sure to add the new definition to uses_defs so it
              # can itself be rereached if necessary.
              if i.expr.ops[0] in uses_defs:
                uses_defs[i.expr.ops[0]].append(k)
              else:
                uses_defs[i.expr.ops[0]] = [k]
              # XXX: It would feel right to remove k from uses_defs of
              # i.dest[0] here, but that leads to problems with missing
              # dessa names, so we don't do it. In the worst case, that
              # should cause a few redundant rereachings.

              #print('reaching now', [str(x) for x in k.reaching])
          # rereach definitions
          if i.dest[0] in self.definitions:
            self.definitions = [x if x != i.dest[0] else i.expr.ops[0] for x in self.definitions]
          if self.actual_returns != None:
            self.actual_returns = [x if x != i.dest[0] else i.expr.ops[0] for x in self.actual_returns]
        
        i.dest = []
        i.expr.ops = [0]
        
    propped = True
    while propped:
      propped = False
      for i in self.getall():
        # prop to expressions, but leave phi functions as they are
        if isinstance(i.expr, Expr) and not i.expr.type == PHI:
          for j in i.expr.getallops():
            # the operand must be an SSADef and have a link to its definition, which must only define
            # this single operand
            if isinstance(j, SSADef) and j.define_statement != None and len(j.define_statement.dest) == 1:
              # propagate everything except phi functions
              if (not isinstance(j.define_statement.expr, Expr) or j.define_statement.expr.type != PHI) and \
                 not j.define_statement.expr.dont_propagate:
                if len(j.define_statement.expr.getallops()) > 10:
                  debug(SSA, 4, 'not propping', i.expr, 'to complex expression', j.define_statement.expr)
                else:
                  debug(SSA, 4, 'propping', i.expr, 'to', j.define_statement.expr)
                  i.expr.substitute(j, j.define_statement.expr)
                  propped = True

  def depropagate(self):
    for i in self.getall():
      if isinstance(i.expr, Expr) and i.expr.type != CONST:
        # search predecessors for definitions that can be used instead of
        # i.expr
        cf = i
        # we give up when encountering a fork; not optimal, but easy to
        # implement
        visited = set()
        while len(cf.comefrom) == 1 and cf.comefrom[0] not in visited:
          cf = cf.comefrom[0]
          visited.add(cf)
          # Expressions that have dont_propagate set are supposed to be left
          # in place, making it illegal to depropagate them as well.
          if cf.op == ASGN and len(cf.dest) == 1 and not cf.expr.dont_propagate:
            if cf.expr.equals(i.expr) and cf.expr is not i.expr:
              debug(SSA, 4, 'depropping', i, 'to', cf)
              i.expr = Expr(VAR, [cf.dest[0]])
            else:
              i.expr.substitute_expr(cf.expr, cf.dest[0])

  def simplify(self, _pass = 1):
    for i in self.getall():
      if isinstance(i.expr, Expr):
        i.expr.simplify()
      if _pass == 1 and i.op == BRANCH_COND and i.expr.type == CONST:
        if i.expr.type == CONST:
          debug(SSA, 3, 'pruning', i)
          if i.expr.ops[0] == 0:
            # never branch
            i.insn.fake_branch = 0
          else:
            # always branch
            i.insn.fake_branch = 1

  def is_io(self, addr):
    for i in self.iomap:
      if isinstance(i, tuple):
        if addr >= i[0] and addr < i[1]:
          return True
      elif addr == i:
        return True
    return False

  # de-SSA works by dumping the indices of definitions if their live ranges
  # do not overlap; if they do, it will rename the definition if it is not
  # used outside this block or create a temporary copy if it is
  def dessa(self):
    done = set()
    tmp_index = 0
    temps = dict()
    def do_dessa(st, defs = None):
      if defs == None:
        defs = dict()
      nonlocal tmp_index
      done.add(st)
      debug(DESSA, 3, 'starting dessa at', st)
      if isinstance(st.expr, Expr):
        # check all uses if they are the latest definition
        # if not, we have to keep a copy of the use before
        # it is overwritten
        for i in st.expr.getallops():
          if isinstance(i, SSADef):
            # implicit definitions with 0 as index are not named in the loop
            # below, so we do it here instead
            if i.dessa_name == None and i.idx == 0:
              i.dessa_name = type2dessaname(i.type)
              debug(DESSA, 4, 'bnamed', i, object.__str__(i), 'to', i.dessa_name)

            key = (i.type, i.addr)
            # check if this is the current (most recent) definition
            # we ignore the following cases:
            # - temps: no need to copy what already is a copy
            # - phi functions: designed from the outset to only use current
            #   definitions
            if key in defs and defs[key] != i and not i.is_dessa_tmp and st.expr.type not in [PHI, EXPLICIT_PHI]:
              # use of a non-current definition
              debug(DESSA, 4, 'old definition', i, 'used, current', defs[key])
              def_st = i.define_statement
              if i in temps:
                st.expr = st.expr.substitute(i, temps[i], dup = True)
              elif def_st == None:
                # no defining statement; this is a function argument
                debug(DESSA, 4, 'need to copy argument', i)
                assert(i.idx == 0)
                # we need to make a copy at the start of the function
                old_start = self.start
                nst = SSAStatement()
                nst.op = ASGN
                nst.dest = [SSADef(None, 'TMP', idx=tmp_index, dessa_tmp=True)]
                nst.dest[0].dessa_name = 'old_' + i.dessa_name #'tmp' + str(tmp_index)
                nst.dest[0].addr = i.addr
                tmp_index += 1
                nst.expr = Expr(VAR, [i])
                nst.next = [old_start]
                nst.insn = old_start.insn
                old_start.comefrom += [nst]
                self.start = nst
                st.expr = st.expr.substitute(i, nst.dest[0], dup = True)
                temps[i] = nst.dest[0]
                debug(DESSA, 4, 'argtmp', i, nst.dest[0], st)
              else:
                if def_st.expr.type == PHI:
                  # the definition used is defined as a phi function
                  # making it explicit is sufficient to create a copy
                  def_st.dest[0].dessa_name = type2dessaname(def_st.dest[0].type) + str(def_st.dest[0].idx)
                  def_st.expr.type = EXPLICIT_PHI
                  temps[i] = def_st.dest[0]
                  def_st.dest[0].is_dessa_tmp = True
                else:
                  # create an additional copy when at the point of definition
                  new_def = SSADef(None, 'TMP', idx=tmp_index, dessa_tmp=True)
                  new_def.dessa_name = 'tmp' + str(tmp_index)
                  tmp_index += 1
                  if def_st.op == ASGN:
                    def_st.dest += [new_def]
                    debug(DESSA, 4, 'copytmp', def_st)
                  elif def_st.op == CALL:
                    new_st = SSAStatement()
                    new_st.dest = [new_def]
                    new_st.op = ASGN
                    new_st.expr = Expr(VAR, [i])
                    new_st.insn = def_st.insn
                    new_st.next = def_st.next
                    for j in def_st.next:
                      j.comefrom.remove(def_st)
                      j.comefrom.append(new_st)
                    def_st.next = [new_st]
                    new_st.comefrom = [def_st]
                    debug(DESSA, 4, 'duptmp', new_st)
                  temps[i] = new_def
                  st.expr = st.expr.substitute(i, new_def, dup = True)
                  debug(DESSA, 4, 'duped', st.expr)
      # collect all definitions and give them a default name
      for d in st.dest:
        key = (d.type, d.addr)
        defs[key] = d
        if d.dessa_name == None:
          d.dessa_name = type2dessaname(d.type)
          debug(DESSA, 4, 'named', d, object.__str__(d), 'to', d.dessa_name)
      for i in st.next:
        if not i in done:
          do_dessa(i, defs.copy())
    do_dessa(self.start)

def ssaify(insn, symbol, iomap):
  if insn.addr in ssacache:
    debug(SSA, 2, 'serving', insn, 'from SSA cache')
    ret = ssacache[insn.addr]
    ret.symbol = symbol
    return ret

  debug(SSA, 1, '--- START', insn)
  for _pass in [1, 2]:
    debug(SSA, 1, '--- PASS', _pass)
    ssag = SSAGraph(iomap, _pass)
    ssag.origin = insn.addr
    ssag.symbol = symbol
    ssa_in_progress.add(insn)
    debug(SSA, 5, 'progress in', hex(insn.addr), [hex(x.addr) for x in ssa_in_progress])
    ssag.add(insn)
    debug(SSA, 5, 'progress out', hex(insn.addr), [hex(x.addr) for x in ssa_in_progress])
    ssa_in_progress.remove(insn)
    ssag.dump(2)
    ssag.find_definitions()
    ssag.dce()
    ssag.dump(4)
    ssag.dereach()
    ssag.propagate()
    ssag.dump(4)
    ssag.dce()
    #ssag.dump()
    ssag.simplify(_pass)
  debug(SSA, 1, '--- FINAL', insn)
  ssag.dump(2)
  # propagation may have redefined reachings
  ssag.find_definitions()
  ssag.find_args()
  ssag.find_rets()
  debug(SSA, 1, '--- DONE', insn)
  debug(ARGRET, 4, 'adding', ssag, 'for insn', insn, 'to ssacache')
  ssacache[insn.addr] = ssag
  return ssag

def identifyreturns(graphs):
  done = []
  for g in graphs:
    debug(ARGRET, 2, '-- IDENTIRET', hex(g.origin))
    uses = []
    for call in g.callers_st:
      debug(ARGRET, 5, 'uses from', call)
      for j in call.call_uses:
        if not j in uses:
          uses += [j]
    debug(ARGRET, 2, 'definitions', [str(x) for x in g.definitions])
    debug(ARGRET, 2, 'actual uses', [str(x) for x in uses])
    callee_context_uses = []
    for u in uses:
      for d in g.definitions:
        if u.type == d.type and u.addr == d.addr and not d in callee_context_uses:
          callee_context_uses += [d]
    debug(ARGRET, 2, 'callee uses', [str(x) for x in callee_context_uses])
    g.actual_returns = callee_context_uses
    g.find_rets()
    g.dce()
    g.dump(4)
    for h in g.callee_graphs:
      if h in done:
        debug(ARGRET, 2, 'redoing', h)
        identifyreturns([h])
    done += [g]

def type2dessaname(type):
  if type == 'M':
    return 'mem'
  else:
    return type.lower()
