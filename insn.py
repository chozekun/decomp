# insn.py
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

from util import *
from debug import *

OPC_OUTOFRANGE = 0x1000

class Insn:
  def __init__(self, addr):
    self.addr = addr
    self.bytes = []
    self.disas = '(unknown)'
    self.next = []
    self.comefrom = []
    self.sym = None
    # if analysis determines that this two-way instruction is actually
    # one-way, fake_branch can be set to the index into .next that is
    # actually taken; currently used by conditional branches
    self.fake_branch = -1
  def __str__(self):
    s = hex(self.addr) + ': ' + self.disas
    if self.next:
      s += ' -> ['
      for i in self.next:
        s += hex(i.addr) + ' '
      s += ']'
    if self.comefrom:
      s += ' <- ['
      for i in self.comefrom:
        s += hex(i.addr) + ' '
      s += ']'
    return s

class Symbol:
  def __init__(self, address, name = None):
    self.address = address
    if name == None:
      name = 'sym'
    self.name = name + '_' + zhex(address)
    self.insn = None

def bra(b):
  if b[1] > 0x7f:
    return hex(b[1] - 256)
  else:
    return '+' + hex(b[1])

def abs(b):
  return hex(b[1] + (b[2] << 8))
def aby(b):
  return abs(b) + ',Y'
def abx(b):
  return abs(b) + ',X'
def izx(b):
  return '(' + hex(b[1]) + ',X)'
def izy(b):
  return '(' + hex(b[1]) + '),Y'
def zp(b):
  return hex(b[1])
def zpx(b):
  return zp(b) + ',X'
def zpy(b):
  return zp(b) + ',Y'
def imm(b):
  return '#' + hex(b[1])
  
def disas(bytes):
  opc = bytes[0]
  if opc == 0x00:
    return 'BRK'
  elif opc == 0x01:
    return 'ORA (' + hex(bytes[1]) + ',X)'
  elif opc == 0x05:
    return 'ORA ' + zp(bytes)
  elif opc == 0x06:
    return 'ASL ' + zp(bytes)
  elif opc == 0x08:
    return 'PHP'
  elif opc == 0x09:
    return 'ORA ' + imm(bytes)
  elif opc == 0x0a:
    return 'ASL A'
  elif opc == 0x0d:
    return 'ORA ' + abs(bytes)
  elif opc == 0x0e:
    return 'ASL ' + abs(bytes)
  elif opc == 0x10:
    return 'BPL ' + bra(bytes)
  elif opc == 0x11:
    return 'ORA ' + izy(bytes)
  elif opc == 0x15:
    return 'ORA ' + zpx(bytes)
  elif opc == 0x16:
    return 'ASL ' + zpx(bytes)
  elif opc == 0x18:
    return 'CLC'
  elif opc == 0x19:
    return 'ORA ' + aby(bytes)
  elif opc == 0x1d:
    return 'ORA ' + abx(bytes)
  elif opc == 0x1e:
    return 'ASL ' + abx(bytes)
  elif opc == 0x20:
    return 'JSR ' + abs(bytes)
  elif opc == 0x21:
    return 'AND ' + izy(bytes)
  elif opc == 0x24:
    return 'BIT ' + zp(bytes)
  elif opc == 0x25:
    return 'AND ' + zp(bytes)
  elif opc == 0x26:
    return 'ROL ' + zp(bytes)
  elif opc == 0x28:
    return 'PLP'
  elif opc == 0x29:
    return 'AND ' + imm(bytes)
  elif opc == 0x2a:
    return 'ROL A'
  elif opc == 0x2c:
    return 'BIT ' + abs(bytes)
  elif opc == 0x2d:
    return 'AND ' + abs(bytes)
  elif opc == 0x2e:
    return 'ROL ' + abs(bytes)
  elif opc == 0x30:
    return 'BMI ' + bra(bytes)
  elif opc == 0x31:
    return 'AND ' + izy(bytes)
  elif opc == 0x35:
    return 'AND ' + zpx(bytes)
  elif opc == 0x36:
    return 'ROL ' + zpx(bytes)
  elif opc == 0x38:
    return 'SEC'
  elif opc == 0x39:
    return 'AND ' + aby(bytes)
  elif opc == 0x3d:
    return 'AND ' + abx(bytes)
  elif opc == 0x3e:
    return 'ROL ' + abx(bytes)
  elif opc == 0x40:
    return 'RTI'
  elif opc == 0x41:
    return 'EOR ' + izx(bytes)
  elif opc == 0x45:
    return 'EOR ' + zp(bytes)
  elif opc == 0x46:
    return 'LSR ' + zp(bytes)
  elif opc == 0x48:
    return 'PHA'
  elif opc == 0x49:
    return 'EOR ' + imm(bytes)
  elif opc == 0x4a:
    return 'LSR A'
  elif opc == 0x4c:
    return 'JMP ' + abs(bytes)
  elif opc == 0x4d:
    return 'EOR ' + abs(bytes)
  elif opc == 0x4e:
    return 'LSR ' + abs(bytes)
  elif opc == 0x50:
    return 'BVC ' + bra(bytes)
  elif opc == 0x51:
    return 'EOR ' + izy(bytes)
  elif opc == 0x55:
    return 'EOR ' + zpx(bytes)
  elif opc == 0x56:
    return 'LSR ' + zpx(bytes)
  elif opc == 0x58:
    return 'CLI'
  elif opc == 0x59:
    return 'EOR ' + aby(bytes)
  elif opc == 0x5d:
    return 'EOR ' + abx(bytes)
  elif opc == 0x5e:
    return 'LSR ' + abx(bytes)
  elif opc == 0x60:
    return 'RTS'
  elif opc == 0x61:
    return 'ADC ' + izx(bytes)
  elif opc == 0x65:
    return 'ADC ' + zp(bytes)
  elif opc == 0x66:
    return 'ROR ' + zp(bytes)
  elif opc == 0x68:
    return 'PLA'
  elif opc == 0x69:
    return 'ADC ' + imm(bytes)
  elif opc == 0x6a:
    return 'ROR A'
  elif opc == 0x6c:
    return 'JMP (' + abs(bytes) + ')'
  elif opc == 0x6d:
    return 'ADC ' + abs(bytes)
  elif opc == 0x6e:
    return 'ROR ' + abs(bytes)
  elif opc == 0x70:
    return 'BVS ' + bra(bytes)
  elif opc == 0x71:
    return 'ADC ' + izy(bytes)
  elif opc == 0x75:
    return 'ADC ' + zpx(bytes)
  elif opc == 0x76:
    return 'ROR ' + zpx(bytes)
  elif opc == 0x78:
    return 'SEI'
  elif opc == 0x79:
    return 'ADC ' + aby(bytes)
  elif opc == 0x7d:
    return 'ADC ' + abx(bytes)
  elif opc == 0x7e:
    return 'ROR ' + abx(bytes)
  elif opc == 0x81:
    return 'STA ' + izx(bytes)
  elif opc == 0x84:
    return 'STY ' + zp(bytes)
  elif opc == 0x85:
    return 'STA ' + zp(bytes)
  elif opc == 0x86:
    return 'STX ' + zp(bytes)
  elif opc == 0x88:
    return 'DEY'
  elif opc == 0x8a:
    return 'TXA'
  elif opc == 0x8c:
    return 'STY ' + abs(bytes)
  elif opc == 0x8d:
    return 'STA ' + abs(bytes)
  elif opc == 0x8e:
    return 'STX ' + abs(bytes)
  elif opc == 0x90:
    return 'BCC ' + bra(bytes)
  elif opc == 0x91:
    return 'STA ' + izy(bytes)
  elif opc == 0x94:
    return 'STY ' + zpx(bytes)
  elif opc == 0x95:
    return 'STA ' + zpx(bytes)
  elif opc == 0x96:
    return 'STX ' + zpy(bytes)
  elif opc == 0x98:
    return 'TYA'
  elif opc == 0x99:
    return 'STA ' + aby(bytes)
  elif opc == 0x9a:
    return 'TXS'
  elif opc == 0x9d:
    return 'STA ' + abx(bytes)
  elif opc == 0xa0:
    return 'LDY ' + imm(bytes)
  elif opc == 0xa1:
    return 'LDA ' + izx(bytes)
  elif opc == 0xa2:
    return 'LDX ' + imm(bytes)
  elif opc == 0xa4:
    return 'LDY ' + zp(bytes)
  elif opc == 0xa5:
    return 'LDA ' + zp(bytes)
  elif opc == 0xa6:
    return 'LDX ' + zp(bytes)
  elif opc == 0xa8:
    return 'TAY'
  elif opc == 0xa9:
    return 'LDA ' + imm(bytes)
  elif opc == 0xaa:
    return 'TAX'
  elif opc == 0xac:
    return 'LDY ' + abs(bytes)
  elif opc == 0xad:
    return 'LDA ' + abs(bytes)
  elif opc == 0xae:
    return 'LDX ' + abs(bytes)
  elif opc == 0xb0:
    return 'BCS ' + bra(bytes)
  elif opc == 0xb1:
    return 'LDA ' + izy(bytes)
  elif opc == 0xb4:
    return 'LDY ' + zpx(bytes)
  elif opc == 0xb5:
    return 'LDA ' + zpx(bytes)
  elif opc == 0xb6:
    return 'LDX ' + zpy(bytes)
  elif opc == 0xb8:
    return 'CLV'
  elif opc == 0xb9:
    return 'LDA ' + aby(bytes)
  elif opc == 0xba:
    return 'TSX'
  elif opc == 0xbc:
    return 'LDY ' + abx(bytes)
  elif opc == 0xbd:
    return 'LDA ' + abx(bytes)
  elif opc == 0xbe:
    return 'LDX ' + aby(bytes)
  elif opc == 0xc0:
    return 'CPY ' + imm(bytes)
  elif opc == 0xc1:
    return 'CMP ' + izx(bytes)
  elif opc == 0xc4:
    return 'CPX ' + zp(bytes)
  elif opc == 0xc5:
    return 'CMP ' + zp(bytes)
  elif opc == 0xc6:
    return 'DEC ' + zp(bytes)
  elif opc == 0xc8:
    return 'INY'
  elif opc == 0xc9:
    return 'CMP ' + imm(bytes)
  elif opc == 0xca:
    return 'DEX'
  elif opc == 0xcc:
    return 'CPY ' + abs(bytes)
  elif opc == 0xcd:
    return 'CMP ' + abs(bytes)
  elif opc == 0xce:
    return 'DEC ' + abs(bytes)
  elif opc == 0xd0:
    return 'BNE ' + bra(bytes)
  elif opc == 0xd1:
    return 'CMP ' + izy(bytes)
  elif opc == 0xd5:
    return 'CMP ' + zpx(bytes)
  elif opc == 0xd6:
    return 'DEC ' + zpx(bytes)
  elif opc == 0xd8:
    return 'CLD'
  elif opc == 0xd9:
    return 'CMP ' + aby(bytes)
  elif opc == 0xdd:
    return 'CMP ' + abx(bytes)
  elif opc == 0xde:
    return 'DEC ' + abx(bytes)
  elif opc == 0xe0:
    return 'CPX ' + imm(bytes)
  elif opc == 0xe1:
    return 'SBC ' + izy(bytes)
  elif opc == 0xe4:
    return 'CPX ' + zp(bytes)
  elif opc == 0xe5:
    return 'SBC ' + zp(bytes)
  elif opc == 0xe6:
    return 'INC ' + zp(bytes)
  elif opc == 0xe8:
    return 'INX'
  elif opc == 0xe9:
    return 'SBC ' + imm(bytes)
  elif opc == 0xea:
    return 'NOP'
  elif opc == 0xec:
    return 'CPX ' + abs(bytes)
  elif opc == 0xed:
    return 'SBC ' + abs(bytes)
  elif opc == 0xee:
    return 'INC ' + abs(bytes)
  elif opc == 0xf0:
    return 'BEQ ' + bra(bytes)
  elif opc == 0xf1:
    return 'SBC ' + izy(bytes)
  elif opc == 0xf5:
    return 'SBC ' + zpx(bytes)
  elif opc == 0xf6:
    return 'INC ' + zpx(bytes)
  elif opc == 0xf8:
    return 'SED'
  elif opc == 0xf9:
    return 'SBC ' + aby(bytes)
  elif opc == 0xfd:
    return 'SBC ' + abx(bytes)
  elif opc == 0xfe:
    return 'INC ' + abx(bytes)
  else:
    return 'UNKNOWN'

def insn_size(opcode):
  if opcode in [0xa8, 0xaa, 0xba, 0x98, 0x8a, 0x9a, 0x48, 0x08, 0x68, 0x28,
      0xe8, 0xc8, 0xca, 0x88, 0x0a, 0x4a, 0x2a, 0x6a, 0x40, 0x60, 0x18,
      0x58, 0xd8, 0xb8, 0x38, 0x78, 0xf8, 0xea]:
    return 1
  elif opcode in [0xa9, 0xa5, 0xb5, 0xa1, 0xb1, 0xa2, 0xa6, 0xb6, 0xa0, 0xa4,
      0xb4, 0x85, 0x95, 0x81, 0x91, 0x86, 0x96, 0x84, 0x94, 0x69, 0x65, 0x75,
      0x61, 0x71, 0xe9, 0xe5, 0xf5, 0xe1, 0xf1, 0x29, 0x25, 0x35, 0x21, 0x31,
      0x49, 0x45, 0x55, 0x41, 0x51, 0x09, 0x05, 0x15, 0x01, 0x11, 0xc9, 0xc5,
      0xd5, 0xc1, 0xd1, 0xe0, 0xe4, 0xc0, 0xc4, 0x24, 0xe6, 0xf6, 0xc6, 0xd6,
      0x06, 0x16, 0x46, 0x56, 0x26, 0x36, 0x66, 0x76, 0x10, 0x30, 0x50, 0x70,
      0x90, 0xb0, 0xd0, 0xf0, 0x00]:
    return 2
  elif opcode in [0xad, 0xbd, 0xb9, 0xae, 0xbe, 0xac, 0xbc, 0x8d, 0x9d, 0x99,
      0x8e, 0x8c, 0x6d, 0x7d, 0x79, 0xed, 0xfd, 0xf9, 0x2d, 0x3d, 0x39, 0x4d,
      0x5d, 0x59, 0x0d, 0x1d, 0x19, 0xcd, 0xdd, 0xd9, 0xec, 0xcc, 0x2c, 0xee,
      0xfe, 0xce, 0xde, 0x0e, 0x1e, 0x4e, 0x5e, 0x2e, 0x3e, 0x6e, 0x7e, 0x4c,
      0x6c, 0x20]:
    return 3
  else:
    raise InternalError('unhandled opcode ' + hex(opcode))

  
class MCodeGraph:
  def __init__(self):
    self.symbols = dict()
    self.traced = dict()
  
  def traceall(self, code, org, entries):
    for i in entries:
      self.trace(code, org, i, None, Symbol(i, 'start'))
  
  def trace(self, code, org, addr, comefrom = None, sym = None):
    def outside():
      debug(TRACE, 2, 'tracing outside available code')
      ins.bytes = [OPC_OUTOFRANGE]
      ins.next = []

    debug(TRACE, 4, 'tracing', hex(addr))
    try:
      debug(TRACE, 4, hex(code[addr - org]))
    except IndexError:
      debug(TRACE, 4, 'out of range')
    if addr in self.traced:
      # no need to trace, but we may have to add a symbol
      if sym != None and self.traced[addr].sym == None:
        sym.insn = self.traced[addr]
        self.symbols[addr] = sym
        self.traced[addr].sym = sym
      if comefrom and not comefrom in self.traced[addr].comefrom:
        self.traced[addr].comefrom += [comefrom]
      return self.traced[addr]
    ins = Insn(addr)
    if sym:
      sym.insn = ins
      self.symbols[addr] = sym
      ins.sym = sym
    self.traced[addr] = ins
    if comefrom and not comefrom in ins.comefrom:
      ins.comefrom += [comefrom]
    if addr - org >= len(code) or addr < org:
      outside()
      return ins
    opcode = code[addr - org]
    ins.bytes = [opcode]
    
    try:
      size = insn_size(opcode)
    except:
      debug(TRACE, 3, 'ILLEGAL')
      ins.next = None
      return ins
    
    if size > 1:
      if addr + 1 - org >= len(code):
        outside()
        return ins
      arg1 = code[addr + 1 - org]
      ins.bytes += [arg1]
    if size > 2:
      if addr + 2 - org >= len(code):
        outside()
        return ins
      arg2 = code[addr + 2 - org]
      ins.bytes += [arg2]
    ins.disas = disas(ins.bytes)
    debug(TRACE, 4, ins.disas)
    
    if opcode == 0x4c:
      daddr = (arg2 << 8) + arg1
      debug(TRACE, 4, 'JMP', hex(daddr))
      ins.next = [self.trace(code, org, daddr, ins)]
    elif opcode == 0x6c:
      debug(TRACE, 4, 'JMP (' + hex((arg2 << 8) + arg1) + ')')
      ins.next = None
    elif opcode in [0x6c, 0x40, 0x60]:
      debug(TRACE, 4, 'EOT')
      ins.next = None
    elif opcode == 0x20:
      daddr = (arg2 << 8) + arg1
      debug(TRACE, 4, 'JSR', hex(daddr))
      ins.next = [self.trace(code, org, addr + 3, ins), self.trace(code, org, daddr, ins, Symbol(daddr, 'fun'))]
    elif opcode in [0x10, 0x30, 0x50, 0x70, 0x90, 0xb0, 0xd0, 0xf0]:
      if arg1 > 0x7f:
        arg1 = arg1 - 256
      debug(TRACE, 4, 'Bxx', arg1, '(' + hex(addr + arg1) + ')')
      ins.next = [self.trace(code, org, addr + 2, ins), self.trace(code, org, addr + 2 + arg1, ins)]
    elif opcode in [0x9f]:
      debug(TRACE, 3, 'EOT (illegal)')
      ins.next = None
    else:
      ins.next = [self.trace(code, org, addr + insn_size(opcode), ins)]

    return ins
