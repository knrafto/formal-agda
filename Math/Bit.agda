module Math.Bit where

open import Math.Dec
open import Math.Fin hiding (toℕ; toℕ-IsInjective)
import Math.Fin as Fin
open import Math.Function
open import Math.Nat
open import Math.Type

Bit : Type₀
Bit = Fin 2

pattern 0₂ = inl tt
pattern 1₂ = inr (inl tt)

Bit-IsSet : IsSet Bit
Bit-IsSet = Fin-IsSet

Bit-HasDecEq : HasDecEq Bit
Bit-HasDecEq = Fin-HasDecEq

and : Bit → Bit → Bit
and 0₂ _ = 0₂
and 1₂ b = b

or : Bit → Bit → Bit
or 0₂ b = b
or 1₂ _ = 1₂

xor : Bit → Bit → Bit
xor 0₂ 0₂ = 0₂
xor 0₂ 1₂ = 1₂
xor 1₂ 0₂ = 1₂
xor 1₂ 1₂ = 0₂
