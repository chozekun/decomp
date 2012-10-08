# code.py
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

import block
from ssa import SSADef, CALL, RETURN, LOAD, STORE, ASGN, BRANCH_COND, IMPURE, ENDLESS_LOOP, type2dessaname
import ssa
from expr import *
from util import *
from debug import *

sym_dict = dict()
graph_dict = dict()

# hack to allow adding comments from expression processing
current_statement = None

def ind(num):
  return ' ' * num

def block_comment(indent, comment):
  s = ind(indent) + '/* '
  s += ('\n' + ind(indent)).join(comment.split('\n'))
  s += ' */\n'
  return s

def label(blk):
  if blk.start_st.op == RETURN or (blk.end_st and blk.end_st.op == RETURN):
    l = 'ret_'
  else:
    l = 'label_'
  return l + zhex(blk.start_st.insn.addr)

def any2c(any, prio = 19, preferhex=False, implicit_global=False):
  if isinstance(any, int):
    if preferhex:
      return hex(any)
    else:
      return str(any)
  elif isinstance(any, Expr):
    return expr2c(any, prio, preferhex)
  elif isinstance(any, SSADef):
    return def2c(any, prio, implicit_global)
  raise InternalError('unknown operand ' + str(any) + ' of type ' + str(type(any)))

def def2c(ssad, prio = 19, implicit_global=False):
  global declare_locals, declare_globals
  if isinstance(ssad.addr, int):
    if ssad.dessa_name == None:
      raise InternalError('no dessa_name in ' + str(ssad) + '(' + repr(ssad) + '), defined in ' + str(ssad.define_statement))
    s = ssad.dessa_name + '_' + zhex(ssad.addr)
  else:
    assert(ssad.addr == None)
    assert(ssad.dessa_name != None)
    s = ssad.dessa_name
  if not implicit_global and ssad.type == 'M' and not ssad.is_dessa_tmp and s not in declare_globals:
    declare_globals[s] = 'uint8_t'
  elif (ssad.type != 'M' or ssad.is_dessa_tmp) and s not in declare_locals:
    if ssad.type == 's':
      declare_locals[s] = ('uint8_t', '__sp[' + str(ssad.addr) + ']')
    else:
      declare_locals[s] = ('uint8_t', None)
  if ssad.type == 's' and ssad.addr in [1,2]:
    current_statement.add_comment('XXX: stacked return address accessed')
  return s

def expr2c(ex, prio = 19, preferhex=False):
  global declare_arrays
  myprio = 18

  def unop(operator):
    assert(len(ex.ops) == 1)
    return operator + any2c(ex.ops[0], myprio, preferhex)
  def binop(operator):
    assert(len(ex.ops) == 2)
    return any2c(ex.ops[0], myprio, preferhex) + ' ' + operator + ' ' + any2c(ex.ops[1], myprio, preferhex)
  def nadicop(operator):
    assert(len(ex.ops) >= 2)
    return (' ' + operator + ' ').join([any2c(x, myprio, preferhex) for x in ex.ops])

  if ex.type == EXPLICIT_PHI:
    debug(CODE, 4, 'coding exphi', ex)
    dessa_name = ex.ops[0].dessa_name
    for i in ex.getallops()[1:]:
      debug(CODE, 4, 'is', i.dessa_name, '==', dessa_name, '?')
      #assert(i.dessa_name == dessa_name and i.addr == ex.ops[0].addr)
      assert(i.dessa_name[0] == dessa_name[0] and i.addr == ex.ops[0].addr)
    ret = def2c(ex.ops[0])
  elif ex.type == VAR:
    assert(len(ex.ops) == 1)
    ret = any2c(ex.ops[0])
  elif ex.type == CONST:
    assert(len(ex.ops) == 1)
    ret = any2c(ex.ops[0])
  elif ex.type == ARGS:
    #print(ex.ops[0], type(ex.ops[0]))
    sym = sym_dict[ex.ops[0]]
    graph = graph_dict[ex.ops[0]]
    ret = sym.name + '('
    reg_args = []
    mem_args = []
    # number of arguments should equal number of callee parameters
    assert(graph.origin in ssa.fun_args_tentative or len(ex.ops) - 1 == len(ssa.fun_args_d[graph.first_insn]))
    if graph.origin in ssa.fun_args_tentative:
      current_statement.add_comment('args/rets may be incorrect')
    for i in range(0, len(ex.ops) - 1):
      # distinguish between memory parameters (implicit) and register
      # parameters (explicit)
      if ssa.fun_args_d[graph.first_insn][i].type not in ['M', 's']:
        # for registers, we want 'our' (the caller's) name
        reg_args += [ex.ops[1 + i]]
      elif ssa.fun_args_d[graph.first_insn][i].type == 'M':
        # for memory parameters, we want both names; this is because
        # in our scope, we may just have a constant or a register, which
        # is not very meaningful outside our context
        mem_args += [(ssa.fun_args_d[graph.first_insn][i], ex.ops[1 + i])]
      # ignore stack arguments
    ret += ', '.join([any2c(i) for i in reg_args]) + ')'
    if debug_level >= 2 and len(mem_args) > 0:
      # emit memory arguments as a comment
      comment = 'uses '
      count = 0
      for i in mem_args:
        # workaround: because no argument pruning is done after return
        # identification, we may see arguments that are not actually
        # used by the callee and thus don't have a dessa_name;
        # we ignore those for now
        if i[0].dessa_name != None:
          def0 = def2c(i[0], implicit_global=True)
          def1 = any2c(i[1], implicit_global=True)
          comment += def0
          if def0 != def1:
            comment += ' (' + def1 + ')'
          comment += ', '
          count += 1
          if count >= 3:
            comment += '...'
            break
      comment = comment.rstrip(', ')
      current_statement.add_comment(comment)
  elif ex.type == LOAD:
    assert(len(ex.ops) == 2)
    myprio = 2
    if isinstance(ex.ops[0], int):
      ret = 'arr_' + zhex(ex.ops[0])
      declare_arrays[ret] = 'uint8_t'
    else:
      ret = '((uint8_t *)' + any2c(ex.ops[0]) + ')'
    ret += '[' + any2c(ex.ops[1]) + ']'
  elif ex.type == STORE:
    assert(len(ex.ops) == 3)
    myprio = 2
    if isinstance(ex.ops[1], int):
      ret = 'arr_' + zhex(ex.ops[1])
      declare_arrays[ret] = 'uint8_t'
    else:
      ret = '((uint8_t *)' + any2c(ex.ops[1]) + ')'
    ret += '[' + any2c(ex.ops[2]) + '] = ' + any2c(ex.ops[0])
  elif ex.type == IOIN:
    assert(len(ex.ops) == 1)
    ret = 'inb(' + any2c(ex.ops[0], preferhex=True) + ')'
    myprio = 1
  elif ex.type == IOOUT:
    assert(len(ex.ops) == 2)
    ret = 'outb(' + any2c(ex.ops[0], preferhex = True) + ', ' + any2c(ex.ops[1], preferhex = True) + ')'
    myprio = 1
  elif ex.type == SHR:
    myprio = 7
    ret = binop('>>')
  elif ex.type == SHL:
    myprio = 7
    ret = binop('<<')
  elif ex.type == COMPARE_EQ:
    assert(len(ex.ops) == 2)
    myprio = 7
    ret = binop('==')
  elif ex.type == COMPARE_NE:
    assert(len(ex.ops) == 2)
    myprio = 9
    ret = binop('!=')
  elif ex.type == COMPARE_LT:
    myprio = 8
    ret = binop('<')
  elif ex.type == COMPARE_GE:
    myprio = 8
    ret = binop('>=')
  elif ex.type == ADD:
    myprio = 6
    ret = nadicop('+')
  elif ex.type == SUB:
    myprio = 6
    ret = nadicop('-')
  elif ex.type == NOT:
    myprio = 3
    ret = unop('!')
  elif ex.type == AND:
    myprio = 10
    ret = binop('&')
  elif ex.type == OR:
    myprio = 12
    ret = binop('|')
  elif ex.type == EOR:
    myprio = 11
    ret = binop('^')
  elif ex.type == ANDFLAGS_Z:
    myprio = 10 # & operator
    ret = '!(' + binop('&') + ')'
    myprio = 3 # ! operator
  elif ex.type == ANDFLAGS_NOTZ:
    myprio = 10 # & operator
    ret = '(' + binop('&') + ') != 0'
    myprio = 9 # == operator
  elif ex.type == ANDFLAGS_N:
    myprio = 10 # & operator
    ret = '(' + binop('&') + ') >= 128'
    myprio = 8 # >= operator
  elif ex.type == SHLFLAGS_C:
    myprio = 10 # & operator
    ret = '(' + any2c(ex.ops[0]) + ' & 0x80) == 0'
    myprio = 9 # == operator
  elif ex.type == SHFLAGS_N:
    myprio = 8
    ret = any2c(ex.ops[0], 8) + ' >= 128'
  elif ex.type == INTRINSIC:
    ret = '__' + ex.ops[0] + '(' + ', '.join([any2c(x, preferhex=True) for x in ex.ops[1:]]) + ')'
  elif ex.type == ADCFLAGS_C:
    myprio = 6 # + operator
    ret = ' + '.join([any2c(x, myprio) for x in ex.ops])
    ret += ' >= 256'
    myprio = 8 # >= operator
  elif ex.type == ADCFLAGS_N:
    myprio = 6 # + operator
    ret = ' + '.join([any2c(x, myprio) for x in ex.ops])
    ret += ' >= 128'
    myprio = 8 # < operator
  elif ex.type == ADCFLAGS_Z:
    myprio = 6 # + operator
    ret = ' + '.join([any2c(x, myprio) for x in ex.ops])
    ret += ' == 0'
    myprio = 9 # == operator
  elif ex.type == ADCFLAGS_V:
    myprio = 6 # + operator
    sum = '(int8_t)' + ' + (int8_t)'.join([any2c(x, myprio) for x in ex.ops])
    ret = '(' + sum + ' >= 128) || (' + sum + ' < -128)'
    myprio = 14 # || operator
  elif ex.type == SBBFLAGS_C:
    # While we internally use a borrow flag, the result of this must be a carry,
    # i.e. the condition is inverted (>= instead of <).
    assert(len(ex.ops) >= 2)
    ret = any2c(ex.ops[0], 8) + ' >= ' + ' + '.join([any2c(x, 6) for x in ex.ops[1:]])
    myprio = 8 # >= operator
  elif ex.type == SBBFLAGS_N:
    ret = ' - '.join([any2c(x, 6) for x in ex.ops]) + ' >= 128'
    myprio = 8	# >= operator
  elif ex.type == SBBFLAGS_Z:
    ret = ' - '.join([any2c(x, 6) for x in ex.ops]) + ' == 0'
    myprio = 9	# == operator
  elif ex.type == SBBFLAGS_V:
    myprio = 6 # + operator
    diff = '(int8_t)' + ' - (int8_t)'.join([any2c(x, myprio) for x in ex.ops])
    ret = '(' + diff + ' >= 128) || (' + diff + ' < -128)'
    myprio = 14 # || operator
  elif ex.type == ORFLAGS_N:
    myprio = 12 # | operator
    ret = '(' + binop('|') + ') >= 128'
    myprio = 8 # >= operator
  elif ex.type == ORFLAGS_Z:
    myprio = 12 # | operator
    ret = '(' + binop('|') + ') == 0'
    myprio = 9 # == operator
  elif ex.type == EORFLAGS_Z:
    myprio = 11 # ^ operator
    ret = '(' + binop('^') + ') == 0'
    myprio = 9 # == operator
  elif ex.type == EORFLAGS_N:
    myprio = 11 # ^ operator
    ret = '(' + binop('^') + ') >= 128'
    myprio = 8 # < operator
  elif ex.type == EORFLAGS_NOTN:
    myprio = 11 # ^ operator
    ret = '(' + binop('^') + ') < 128'
    myprio = 8 # < operator
  elif ex.type in [DEFLAGS_V, BITFLAGS_V]:
    # The parens are not necessary, but it feels weird without them.
    ret = '(' + any2c(ex.ops[0], 7) + ' >> 6) & 1'
    myprio = 10 # & operator
  elif ex.type in [DEFLAGS_N, BITFLAGS_N]:
    myprio = 7	# >> operator
    ret = any2c(ex.ops[0], myprio) + ' >> 7'
  elif ex.type == DEFLAGS_C:
    myprio = 10 # & operator
    ret = any2c(ex.ops[0], myprio) + ' & 1'
  elif ex.type == DEFLAGS_Z:
    # The parens are not necessary, but it feels weird without them.
    ret = '(' + any2c(ex.ops[0], 7) + ' >> 1) & 1'
    myprio = 10 # & operator
  elif ex.type == FLAGS:
    ret = '__flags(' + ', '.join([any2c(x, 18) for x in ex.ops]) + ')'
    myprio = 2	# function call
  else:
    ret = 'RAW ' + str(ex)
  if myprio >= prio:
    ret = '(' + ret + ')'
  #ret = '( /* ' + str(myprio) + '/' + str(prio) + ' */ ' + ret + ')'
  return ret

def get_returns(actual_returns):
  # XXX: We should really use a function like ssa.fun_returns().
  rets = []
  rets_d = []
  mrets = []
  mrets_d = []
  for i in sorted(actual_returns, key = attrgetter('type')):
    if i.idx == 0:
      continue
    cdef = any2c(i, implicit_global=True)
    if i.type not in ['M', 's'] and not cdef in rets:
      assert(isinstance(cdef, str))
      rets += [cdef]
      rets_d += [i]
    elif i.type == 'M' and not cdef in mrets:
      mrets += [cdef]
      mrets_d += [i]
  return rets_d, mrets_d

def rets2struct(rets):
  return 'struct ret_' + ''.join([type2dessaname(x.type) for x in rets])

ret_struct_count = 0

declare_locals = dict()
declare_globals = dict()
declare_arrays = dict()

def statement2c(st, indent, graph, bare = False):
  global current_statement
  current_statement = st
  if isinstance(st.expr, Expr) and st.expr.type == PHI:
    return ''
  semi = '' if bare else ';'
  line = ind(indent)
  if st.op == ASGN:
    if len(st.dest) >= 1:
      line += ' = '.join([def2c(x) for x in st.dest]) + ' = ' + expr2c(st.expr) + semi
    elif len(st.dest) == 0:
      if (st.expr.type == NOP):
        line += '/* do nothing */'
      else:
        line += expr2c(st.expr) + semi
    else:
      line += str(st)
  elif st.op == CALL:
    # code assignment of return value(s)
    callee_rets, callee_mrets = get_returns(graph_dict[st.expr.ops[0]].actual_returns)
    rets = []
    mrets = []
    if len(st.call_uses) > 0:
      # distinguish between explicit (register) returns and implicit (memory)
      # returns
      for i in st.call_uses:
        r = def2c(i, implicit_global=True)
        if i.type not in ['M', 's'] and not i.is_dessa_tmp:
          rets += [r]
        elif i.type == 'M':
          mrets += [r]
        # ignore stack returns
      # sorting is required to get a canonical return struct name
      # (for memory parameters it's just beautification)
      rets.sort()
      mrets.sort()
      if len(callee_rets) > 1 and len(rets) > 0:
        # we need a return structure
        global ret_struct_count
        rname = 'ret' + str(ret_struct_count)
        ret_struct_count += 1
        line += rets2struct(callee_rets) + ' ' + rname + ' = '
      elif len(callee_rets) == 1 and len(rets) == 1:
        # direct assignment to register variable
        line += rets[0] + ' = '
    line += expr2c(st.expr) + semi
    if debug_level >= 2 and len(mrets) > 0:	# XXX: or callee_mrets?
      # emit memory parameters as a comment
      comment = 'modifies ' + ', '.join(mrets[:3])
      if len(mrets) > 3:
        comment += ', ...'
      st.add_comment(comment)
    assert(len(callee_rets) >= len(rets))
    if len(rets) >= 1 and len(callee_rets) > 1:
      # if we have used a return struct, we have to assign its members to
      # the corresponding register variables
      for i in rets:
        line += '\n' + ind(indent) + i + ' = ' + rname + '.' + i + ';'
  elif st.op == RETURN:
    if graph.actual_returns and len(graph.actual_returns) > 0:
      rets, mrets = get_returns(graph.actual_returns)
      if len(rets) > 1:
        # return a struct
        line += rets2struct(rets) + ' ret = { ' + ', '.join([any2c(x, implicit_global=True) for x in rets]) + ' }; '
        line += 'return ret' + semi
      elif len(rets) == 1:
        line += 'return ' + any2c(rets[0], implicit_global=True) + semi
      else:
        line += 'return' + semi
      if debug_level >= 2 and len(mrets) > 0:
        line += ' /* modified ' + ', '.join([any2c(x, implicit_global=True) for x in mrets[:3]])
        if len(mrets) > 3:
          line += ', ...'
        line += ' */'
    else:
      line += 'return' + semi
  elif st.op == IMPURE:
    line += any2c(st.expr) + semi
  elif st.op == ENDLESS_LOOP:
    line += 'for (;;);'
  else:
    line += str(st)

  # comments that should always be printed
  my_comments = list(st.comment)
  # comments that should be only printed once per program
  for i in st.comment_once:
    if pull_oneshot_comment(i):
      my_comments += [i]
  if my_comments:
    max_len = 0
    for i in my_comments:
      if len(i) > max_len: max_len = len(i)
    if len(line) + max_len > 80 and not bare:
      line = ind(indent) + '/* ' + (' */\n/* ').join(my_comments).replace('\n', '\n' + ind(indent)) + ' */\n' + line
    else:
      line += ' /* ' + '; '.join(my_comments) + ' */'

  return line + ('' if bare else '\n')

def code(blk, symbol, symbols, graphs, graph):
  global sym_dict, graph_dict, ret_struct_count
  global declare_locals, declare_globals, declare_arrays

  if symbols != None:
    sym_dict = symbols
  if graphs != None:
    for i in graphs:
      graph_dict[i.first_insn.addr] = i

  c_header = ''

  if graph.origin in ssa.fun_returns_tentative or \
     graph.origin in ssa.fun_args_tentative:
    c_header += block_comment(0, 'XXX: recursion, inaccurate args/returns')

  # code function header
  rets, mrets = get_returns(graph.actual_returns)
  if len(rets) > 1:
    c_header += rets2struct(rets)
  elif len(rets) == 1:
    c_header += 'uint8_t'
  else:
    c_header += 'void'
  c_header += ' ' + symbol + '('
  # code (explicit, i.e. register) function parameters
  # XXX: code implicit (memory) parameters as a comment
  declare_arguments = []
  for i in ssa.fun_args_d[graph.first_insn]:
    # workaround for dead arguments that have not been pruned after return
    # identification
    if i.dessa_name != None and i.type not in ['M', 's'] and not i.is_dessa_tmp:
      c_header += 'uint8_t ' + i.dessa_name + ', '
      declare_arguments += [i.dessa_name]
  c_header = c_header.rstrip(', ') + ')\n'
  c_header += '{\n'
  indent = 4
  done = dict()
  gotos = []
  labels = []

  ret_struct_count = 0
  declare_locals = dict()
  declare_globals = dict()
  declare_arrays = dict()

  def do_code(blk, norecurse = False):
    global current_statement
    nonlocal labels, indent, gotos
    c_code = ''

    # We cannot emit labels for clipped basic blocks or mark them as done
    # unless we're coding them as part of an advanced block (norecurse ==
    # True)
    if not (not norecurse and blk.clipped):
      l = label(blk)
      if not l in labels:
        c_code += l + ':\n'
        labels += [l]
      done[blk] = True

    current_statement = blk.start_st

    if isinstance(blk, block.AdvancedBlock):
      if debug_enabled(2):
        c_code += ind(indent) + '/* ablock ' + str(blk) + ' */\n'
      if blk.type in [block.IF_THEN_ELSE, block.IF_THEN]:
        c_code += ind(indent) + 'if (' + any2c(blk.condition) + ') {\n'
        indent += 4
        if debug_enabled(3):
          c_code += ind(indent) + '/* in IT(E) ablock ' + str(blk) + ' */\n'
        if not blk.blocks[0] in done:
          c_code += do_code(blk.blocks[0], norecurse = True)
        else:
          c_code += ind(indent) + 'goto ' + label(blk.blocks[0]) + ';'
          if debug_enabled(3):
            c_code += ' /* IT(E) ablock item already coded */\n'
          c_code += '\n'
          gotos += [label(blk.blocks[0])]
        indent -=4
        c_code += ind(indent) + '}\n'
        if blk.type == block.IF_THEN_ELSE:
          c_code += ind(indent) + 'else {\n'
          indent += 4
          if not blk.blocks[1] in done:
            c_code += do_code(blk.blocks[1], norecurse = True)
          else:
            c_code += ind(indent) + 'goto ' + label(blk.blocks[1]) + ';'
            if debug_enabled(3):
              c_code += ' /* ITE ablock item already coded */'
            c_code += '\n'
            gotos += [label(blk.blocks[1])]
          indent -= 4
          c_code += ind(indent) + '}\n'
      elif blk.type in [block.POST_LOOP, block.EMPTY_LOOP]:
        c_code += ind(indent) + 'do {\n'
        if blk.type == block.POST_LOOP:
          indent += 4
          if not blk.blocks[0] in done:
            for i in blk.blocks:
              assert(i not in done)
              if debug_enabled(2):
                c_code += ind(indent) + '/* post loop block */\n'
              c_code += do_code(i, norecurse = True)
          else:
            c_code += ind(indent) + 'goto ' + label(blk.blocks[0]) + ';'
            if debug_enabled(3):
              c_code += ' /* post loop ablock item already coded */'
            c_code += '\n'
            gotos += [label(blk.blocks[0])]
          indent -=4
        c_code += ind(indent) + '} while (' + expr2c(blk.condition) + ');\n'
      elif blk.type == block.PRE_LOOP:
        c_code += ind(indent) + 'while ('
        if blk.prolog:
          # statements that are executed before every loop iteration _and_
          # before the test; an alternative would be to code this prolog and
          # repeat it in the iteration step of a for() loop
          # this would also make it easier to declare lvalues properly
          for i in blk.prolog:
            st_code = statement2c(i, 0, graph, bare=True)
            if st_code != '': c_code += st_code + ', '
        c_code += any2c(blk.condition) + ') {\n'

        indent += 4
        if not blk.blocks[0] in done:
          c_code += do_code(blk.blocks[0], norecurse = True)
        else:
          c_code += ind(indent) + 'goto ' + label(blk.blocks[0]) + ';'
          if debug_enabled(3):
            c_code += ' /* pre loop ablock item already coded */'
          c_code += '\n'
          gotos += [label(blk.blocks[0])]
        indent -=4

        c_code += ind(indent) + '}\n'
      else:
        for b in blk.blocks:
          if debug_enabled(3):
            c_code += ind(indent) + '/* in ablock ' + str(blk) + ' */\n'
          if not b in done:
            c_code += do_code(b, norecurse = True)
          else:
            c_code += ind(indent) + 'goto ' + label(b) + ';'
            if debug_enabled(3):
              c_code += ' /* ablock item already coded */'
            c_code += '\n'
            gotos += [label(b)]
            if blk.type == block.IF_THEN:
              indent -=4
              c_code += ind(indent) + '}\n'
            return c_code

      if not norecurse:
        if len(blk.next) > 0:
          if not blk.next[0] in done:
            if debug_enabled(3):
              c_code += ind(indent) + '/* from ablock ' + str(blk) + ' */\n'
            c_code += do_code(blk.next[0])
          else:
            c_code += ind(indent) + 'goto ' + label(blk.next[0]) + ';'
            if debug_enabled(3):
              c_code += ' /* from ablock ' + str(blk) + ' */'
            c_code += '\n'
            gotos += [label(blk.next[0])]
    else:
      st = blk.start_st
      if debug_enabled(2):
        c_code += ind(indent) + '/* bblock' + str(blk) + ' */\n'

      def emit_goto(_blk, _comment=None):
        nonlocal c_code, gotos
        c_code += ind(indent) + 'goto ' + label(_blk) + ';'
        if _comment != None and debug_enabled(3):
          c_code += ' /* ' + _comment + ' */'
        c_code += '\n'
        gotos += [label(_blk)]

      def emit_code(_blk, _comment=None):
        nonlocal c_code
        if _comment != None and debug_enabled(3):
          c_code += ind(indent) + '/* ' + _comment+ ' */\n'
        c_code += do_code(_blk)

      if not norecurse and blk.clipped:
        # We cannot code a clipped basic block because it's missing its
        # conditional branch at the end; since such a block is always
        # a part of an advanced block, however, we can just emit a
        # goto and rely on the block being coded as part of its
        # container.
        emit_goto(blk, 'clipped')
      else:
        # don't emit conditional branch statements at the end of blocks,
        # we deal with them later
        if st != blk.end_st or st.op != BRANCH_COND:
          c_code += statement2c(st, indent, graph)
        while st != blk.end_st:
          st = list(st.next)[0]
          if st != blk.end_st or st.op != BRANCH_COND:
            c_code += statement2c(st, indent, graph)

        if not norecurse:
          if len(blk.next) == 1:
            if blk.next[0] in done:
              emit_goto(blk.next[0], 'from bblock ' + str(blk))
            else:
              emit_code(blk.next[0], 'from bblock ' + str(blk))
          elif len(blk.next) == 2:
            assert(st.op == BRANCH_COND)
            do_done = blk.next[0] in done
            skip_done = blk.next[1] in done
            use_skip = skip_done and not do_done
            if use_skip:
              # use skip in conditional statement
              cond_expr = st.expr
            else:
              # use do in conditional statement
              cond_expr = Expr(NOT, [st.expr])
              cond_expr.simplify()
            c_code += ind(indent) + 'if (' + any2c(cond_expr) + ') {\n'
            indent += 4
            if use_skip:
              assert(skip_done)
              emit_goto(blk.next[1], 'branch taken')
            elif do_done:
              emit_goto(blk.next[0], 'branch not taken')
            else:
              assert(not do_done)
              emit_code(blk.next[0], 'from bblock ' + str(blk) + ', branch not taken')
            indent -= 4
            c_code += ind(indent) + '}\n'
            if use_skip:
              assert(not do_done)
              emit_code(blk.next[0], 'from bblock ' + str(blk) + ', branch not taken')
            else:
              if not skip_done:
                emit_code(blk.next[1], 'from bblock ' + str(blk) + ', branch taken')
              else:
                emit_goto(blk.next[1], 'branch taken')
          elif len(blk.next) == 0:
            pass	# nothing to do
          else:
            c_code += '#warning unimplemented multi-target branch\n'
            for c, i in enumerate(blk.next):
              emit_goto(i, 'from bblock ' + str(blk))
            for i in blk.next:
              if not i in done:
                emit_code(i, 'from bblock ' + str(blk))

    return c_code

  c_body = do_code(blk) + '}\n'
  for i in labels:
    if not i in gotos:
      c_body = c_body.replace(i + ':\n', '')
      #c_body = c_body.replace(i + ':\n', '/* ' + i + ': */\n')

  c_decl = ''
  c_extern = ''
  declare_stack = False
  for i, t in declare_locals.items():
    if i not in declare_arguments:
      c_decl += ind(indent) + t[0] + ' ' + i
      if t[1] != None:
        c_decl += ' = ' + t[1]
        if '__sp' in t[1] and not declare_stack:
          c_extern += 'extern uint8_t *__sp;\n'
          declare_stack = True
      c_decl += ';\n'

  for i, t in declare_globals.items():
    c_extern += 'extern ' + t + ' ' + i + ';\n'

  for i, t in declare_arrays.items():
    c_extern += 'extern ' + t + ' ' + i + '[];\n'

  return c_extern + c_header + c_decl + c_body
