{-# OPTIONS --cubical #-}
module Math.Bit where

open import Math.Fin
open import Math.Function
open import Math.Nat
open import Math.Type
open import Math.Vec

data Bit : Type₀ where
  0₂ : Bit
  1₂ : Bit

Byte : Type₀
Byte = Vec 8 Bit

toFin2 : Bit → Fin 2
toFin2 0₂ = fzero
toFin2 1₂ = fsuc fzero

toFin2-IsEquiv : IsEquiv toFin2
toFin2-IsEquiv = HasInverse→IsEquiv fromFin2 from-to to-from
  where
  fromFin2 : Fin 2 → Bit
  fromFin2 (zero , _) = 0₂
  fromFin2 (suc zero , _) = 1₂
  fromFin2 (suc (suc _) , p) = contradiction (suc-reflects-< (suc-reflects-< p)) ¬-<-zero

  from-to : (b : Bit) → fromFin2 (toFin2 b) ≡ b
  from-to 0₂ = refl
  from-to 1₂ = refl

  to-from : (i : Fin 2) → toFin2 (fromFin2 i) ≡ i
  to-from (zero , _) = toℕ-IsInjective refl
  to-from (suc zero , _) = toℕ-IsInjective refl
  to-from (suc (suc _) , p) = contradiction (suc-reflects-< (suc-reflects-< p)) ¬-<-zero

Bit-IsSet : IsSet Bit
Bit-IsSet = subst IsSet (sym (ua toFin2-IsEquiv)) Fin-IsSet

fromBits : {n : ℕ} → Vec n Bit → Fin (2 ^ n)
fromBits = fromDigits ∘ (toFin2 ∘_)

fromBits-IsEquiv : {n : ℕ} → IsEquiv (fromBits {n = n})
fromBits-IsEquiv = fromDigits-IsEquiv ∘-IsEquiv f∘-IsEquiv toFin2-IsEquiv

toBits : {n : ℕ} → Fin (2 ^ n) → Vec n Bit
toBits = inv fromBits-IsEquiv

toBits-IsEquiv : {n : ℕ} → IsEquiv (toBits {n = n})
toBits-IsEquiv = inv-IsEquiv fromBits-IsEquiv
