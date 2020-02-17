{-# OPTIONS --cubical #-}
module Asm.Avr where

open import Math.Bit
open import Math.Nat
open import Math.Type

-- A register.
-- TODO: define for real.
Register : Type₀
Register = ℕ

-- A program address.
ProgAddr : Type₀
ProgAddr = ℕ

-- An operation consists of an opcode and operands.
-- An operation is data, and can be encoded as a bitstring and stored in memory.
data Operation : Type₀ where

-- A program consists of a set of instructions, each with an operation and a unique address.
record Program : Type₁ where
  field
    Instruction : Type₀
    -- TODO: uniqueness?
    address : Instruction → ProgAddr
    operation : Instruction → Operation
