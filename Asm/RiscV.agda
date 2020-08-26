{-# OPTIONS --cubical #-}
module Asm.RiscV where

open import Math.Binary hiding (add; sub)
open import Math.Dec
open import Math.Fin
open import Math.Function
open import Math.Nat
open import Math.Type

-- We want to implement most of the base RV32I integer instruction
-- set, RV32M extension (integer multiply and divide), and maybe
-- RV32F.
--
-- Types of instructions:
-- * Register-register arithmetic (R type): rd, rs1, rs2
-- * Register-immediate arithmetic (I type): rd, rs1, 12-bit immediate
-- * Register-immediate shifts (I type): rd, rs1, 5-bit shift amount
-- * Memory loads (I type): rd, r1s, 12-bit immediate
-- * Memory stores (S type): rs1, rs2, 12-bit immediate
-- * Branches (B type): rs1, rs2, 12-bit immediate
-- * Upper-immediate (U type): rd, 20-bit immediate
-- * Jumps (J type): rd, 20-bit immediate

-- RISC-V has 32 machine registers.
Reg : Type₀
Reg = Fin 32

-- The zero register.
x0 : Reg
x0 = fzero

-- A mapping of registers to values.
RegState : Type₀
RegState = Reg → Word 32

-- All registers start with value 0.
initialRegState : RegState
initialRegState = λ _ → constant 32 0

-- Updates the register state by writing a new value for a
-- register. Writes to the zero register are ignored.
setReg : Reg → Word 32 → RegState → RegState
setReg r v s r' with Fin-HasDecEq r x0
setReg r v s r' | yes r≡x0 = s r'
setReg r v s r' | no ¬r≡x0 with Fin-HasDecEq r' r
setReg r v s r' | no ¬r≡x0 | yes r'≡r = v
setReg r v s r' | no ¬r≡x0 | no ¬r'≡r = s r'

-- Some misnomers:
--   reg-reg shift ops are not shift type
--   jalr is not jump type

data RegRegOp : Type₀ where
  add   : RegRegOp
  sub   : RegRegOp
  sll   : RegRegOp
  slt   : RegRegOp
  sltu  : RegRegOp
  xor   : RegRegOp
  srl   : RegRegOp
  sra   : RegRegOp
  or    : RegRegOp
  and   : RegRegOp

RegRegOp-funct7 : RegRegOp → Word 7
RegRegOp-funct7 add  = constant 7 0b0000000
RegRegOp-funct7 sub  = constant 7 0b0100000
RegRegOp-funct7 sll  = constant 7 0b0000000
RegRegOp-funct7 slt  = constant 7 0b0000000
RegRegOp-funct7 sltu = constant 7 0b0000000
RegRegOp-funct7 xor  = constant 7 0b0000000
RegRegOp-funct7 srl  = constant 7 0b0000000
RegRegOp-funct7 sra  = constant 7 0b0100000
RegRegOp-funct7 or   = constant 7 0b0000000
RegRegOp-funct7 and  = constant 7 0b0000000

RegRegOp-funct3 : RegRegOp → Word 3
RegRegOp-funct3 add  = constant 3 0b000
RegRegOp-funct3 sub  = constant 3 0b000
RegRegOp-funct3 sll  = constant 3 0b001
RegRegOp-funct3 slt  = constant 3 0b010
RegRegOp-funct3 sltu = constant 3 0b011
RegRegOp-funct3 xor  = constant 3 0b100
RegRegOp-funct3 srl  = constant 3 0b101
RegRegOp-funct3 sra  = constant 3 0b101
RegRegOp-funct3 or   = constant 3 0b110
RegRegOp-funct3 and  = constant 3 0b111

data RegImmOp : Type₀ where
  addi  : RegImmOp
  slti  : RegImmOp
  sltiu : RegImmOp
  xori  : RegImmOp
  ori   : RegImmOp
  andi  : RegImmOp

RegImmOp-funct3 : RegImmOp → Word 3
RegImmOp-funct3 addi  = constant 3 0b000
RegImmOp-funct3 slti  = constant 3 0b010
RegImmOp-funct3 sltiu = constant 3 0b011
RegImmOp-funct3 xori  = constant 3 0b100
RegImmOp-funct3 ori   = constant 3 0b110
RegImmOp-funct3 andi  = constant 3 0b111

data ShiftImmOp : Type₀ where
  slli  : ShiftImmOp
  srli  : ShiftImmOp
  srai  : ShiftImmOp

ShiftImmOp-funct7 : ShiftImmOp → Word 7
ShiftImmOp-funct7 slli = constant 7 0b0000000
ShiftImmOp-funct7 srli = constant 7 0b0000000
ShiftImmOp-funct7 srai = constant 7 0b0100000

ShiftImmOp-funct3 : ShiftImmOp → Word 3
ShiftImmOp-funct3 slli = constant 3 0b001
ShiftImmOp-funct3 srli = constant 3 0b101
ShiftImmOp-funct3 srai = constant 3 0b101

data LoadOp : Type₀ where
  lb    : LoadOp
  lh    : LoadOp
  lw    : LoadOp
  lbu   : LoadOp
  lhu   : LoadOp

LoadOp-funct3 : LoadOp → Word 3
LoadOp-funct3 lb  = constant 3 0b000
LoadOp-funct3 lh  = constant 3 0b001
LoadOp-funct3 lw  = constant 3 0b010
LoadOp-funct3 lbu = constant 3 0b100
LoadOp-funct3 lhu = constant 3 0b101

data StoreOp : Type₀ where
  sb    : StoreOp
  sh    : StoreOp
  sw    : StoreOp

StoreOp-funct3 : StoreOp → Word 3
StoreOp-funct3 sb = constant 3 0b000
StoreOp-funct3 sh = constant 3 0b001
StoreOp-funct3 sw = constant 3 0b010

data BranchOp : Type₀ where
  beq   : BranchOp
  bne   : BranchOp
  blt   : BranchOp
  bge   : BranchOp
  bltu  : BranchOp
  bgeu  : BranchOp

BranchOp-funct3 : BranchOp → Word 3
BranchOp-funct3 beq  = constant 3 0b000
BranchOp-funct3 bne  = constant 3 0b001
BranchOp-funct3 blt  = constant 3 0b100
BranchOp-funct3 bge  = constant 3 0b101
BranchOp-funct3 bltu = constant 3 0b110
BranchOp-funct3 bgeu = constant 3 0b111

data UpperImmOp : Type₀ where
  lui   : UpperImmOp
  auipc : UpperImmOp

UpperImmOp-opcode : UpperImmOp → Word 7
UpperImmOp-opcode lui   = constant 7 0b0110111
UpperImmOp-opcode auipc = constant 7 0b0010111

data JumpOp : Type₀ where
  jal   : JumpOp

JumpOp-opcode : JumpOp → Word 7
JumpOp-opcode jal = constant 7 0b1101111

-- Instructions.
data Inst : Type₀ where
  reg-reg   : RegRegOp   → Reg → Reg → Reg → Inst
  reg-imm   : RegImmOp   → Reg → Reg → Word 12 → Inst
  shift-imm : ShiftImmOp → Reg → Reg → Fin 32 → Inst
  load      : LoadOp     → Reg → Reg → Word 12 → Inst
  store     : StoreOp    → Reg → Reg → Word 12 → Inst
  -- TODO: must be 4-byte aligned
  branch    : BranchOp   → Reg → Reg → Word 13 → Inst
  upper-imm : UpperImmOp → Reg → Word 20 → Inst
  -- TODO: must be 4-byte aligned
  jump      : JumpOp     → Reg → Word 21 → Inst

encodeReg : Reg → Word 5
encodeReg = fromUnsigned

encode : Inst → Word 32
encode (reg-reg op rd rs1 rs2) =
  RegRegOp-funct7 op ++ encodeReg rs2 ++ encodeReg rs1 ++ RegRegOp-funct3 op ++ encodeReg rd ++ constant 7 0b0110011
encode (reg-imm op rd rs1 imm) =
  imm ++ encodeReg rs1 ++ RegImmOp-funct3 op ++ encodeReg rd ++ constant 7 0b0010011
encode (shift-imm op rd rs1 shamt) =
  ShiftImmOp-funct7 op ++ fromUnsigned {n = 5} shamt ++ encodeReg rs1 ++ ShiftImmOp-funct3 op ++ encodeReg rd ++ constant 7 0b0010011
encode (load op rd rs1 imm) =
  imm ++ encodeReg rs1 ++ LoadOp-funct3 op ++ encodeReg rd ++ constant 7 0b0000011
encode (store op rs1 rs2 imm) =
  slice imm 11 5 ++ encodeReg rs2 ++ encodeReg rs1 ++ StoreOp-funct3 op ++ slice imm 4 0 ++ constant 7 0b0100011
encode (branch op rs1 rs2 imm) =
  slice imm 12 12 ++ slice imm 10 5 ++ encodeReg rs2 ++ encodeReg rs1 ++ BranchOp-funct3 op ++ slice imm 4 1 ++ slice imm 11 11 ++ constant 7 0b1100011
encode (upper-imm op rd imm) = imm ++ encodeReg rd ++ UpperImmOp-opcode op
encode (jump op rd imm) = slice imm 20 20 ++ slice imm 10 1 ++ slice imm 11 11 ++ slice imm 19 12 ++ encodeReg rd ++ JumpOp-opcode op

encode-IsInjective : IsInjective encode
encode-IsInjective = {!!}  -- good luck
