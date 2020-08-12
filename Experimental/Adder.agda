{-# OPTIONS --cubical #-}
module Experimental.Adder where

open import Math.Bit
open import Math.Nat
open import Math.Type

Carry : Type₀
Carry = Bit

Word-toℕ : ∀ {n} → Word n → ℕ
Word-toℕ = {!!}

Carry-toℕ : Carry → ℕ
Carry-toℕ 0₂ = 0
Carry-toℕ 1₂ = 1

addWithCarry : ∀ {n} → Word n → Word n → Carry → Word (suc n)
addWithCarry {zero} a b c = {!!}
addWithCarry {suc n} a b c = {!!}

addWithCarry-toℕ :
  ∀ {n} (a b : Word n) (c : Carry) →
  Word-toℕ (addWithCarry a b c) ≡ Word-toℕ a + Word-toℕ b + Carry-toℕ c
addWithCarry-toℕ = {!!}
