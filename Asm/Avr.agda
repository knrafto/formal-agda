{-# OPTIONS --cubical #-}
module Asm.Avr where

open import Math.Bit
open import Math.Fin
open import Math.Nat
open import Math.Type

-- A register.
Register : Type₀
Register = ℕ

-- A program address.
Address : Type₀
Address = ℕ

-- An offset for a branch or relative jump.
-- TODO: this should be ℤ.
Offset : Type₀
Offset = ℕ

-- An operation consists of an opcode and operands.
-- This is actually a bit more permissive than the instruction encoding allows.
data Operation : Type₀ where
  adiw  : Register → Word16 → Operation
  adc   : Register → Register → Operation
  andi  : Register → Word8 → Operation
  brcs  : Offset → Operation
  breq  : Offset → Operation
  brne  : Offset → Operation
  call  : Address → Operation
  cbi   : Address → Fin 8 → Operation
  cli   : Operation
  cpc   : Register → Register → Operation
  cpi   : Register → Word8 → Operation
  eor   : Register → Register → Operation
  in'   : Register → Address → Operation
  jmp   : Address → Operation
  ldi   : Register → Word8 → Operation
  lds   : Register → Address → Operation
  movw  : Register → Register → Operation
  ori   : Register → Word8 → Operation
  out   : Address → Register → Operation
  pop   : Register → Operation
  push  : Register → Operation
  reti  : Operation
  rjmp  : Offset → Operation
  sbc   : Register → Register → Operation
  sbci  : Register → Word8 → Operation
  sbi   : Address → Fin 8 → Operation
  sei   : Operation
  sub   : Register → Register → Operation
  subi  : Register → Word8 → Operation
  st-X+ : Register → Operation
  sts   : Address → Register → Operation

-- A program consists of a set of instructions, each with an operation and a unique address.
record Program : Type₁ where
  field
    Instruction : Type₀
    -- TODO: uniqueness?
    address : Instruction → Address
    operation : Instruction → Operation
