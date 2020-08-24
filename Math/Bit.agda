{-# OPTIONS --cubical #-}
module Math.Bit where

open import Math.Dec
open import Math.Fin hiding (toℕ; toℕ-IsInjective)
import Math.Fin as Fin
open import Math.Function
open import Math.Nat
open import Math.Type

data Bit : Type₀ where
  0₂ : Bit
  1₂ : Bit

toFin2 : Bit → Fin 2
toFin2 0₂ = fzero
toFin2 1₂ = fsuc fzero

fromFin2 : Fin 2 → Bit
fromFin2 (zero , _) = 0₂
fromFin2 (suc zero , _) = 1₂
fromFin2 (suc (suc _) , p) = contradiction (suc-reflects-< (suc-reflects-< p)) ¬-<-zero

toFin2-IsEquiv : IsEquiv toFin2
toFin2-IsEquiv = HasInverse→IsEquiv fromFin2 from-to to-from
  where
  from-to : (b : Bit) → fromFin2 (toFin2 b) ≡ b
  from-to 0₂ = refl
  from-to 1₂ = refl

  to-from : (i : Fin 2) → toFin2 (fromFin2 i) ≡ i
  to-from (zero , _) = Fin.toℕ-IsInjective refl
  to-from (suc zero , _) = Fin.toℕ-IsInjective refl
  to-from (suc (suc _) , p) = contradiction (suc-reflects-< (suc-reflects-< p)) ¬-<-zero

toℕ : Bit → ℕ
toℕ b = Fin.toℕ (toFin2 b)

toℕ-IsInjective : IsInjective toℕ
toℕ-IsInjective = IsEquiv→IsInjective toFin2-IsEquiv ∘ Fin.toℕ-IsInjective

Bit-IsSet : IsSet Bit
Bit-IsSet = subst IsSet (sym (ua toFin2 toFin2-IsEquiv)) Fin-IsSet

Bit-HasDecEq : HasDecEq Bit
Bit-HasDecEq = subst HasDecEq (sym (ua toFin2 toFin2-IsEquiv)) Fin-HasDecEq
