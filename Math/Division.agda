{-# OPTIONS --cubical --allow-unsolved-metas #-}
-- Euclidean division of natural numbers.
module Math.Division where

open import Math.Dec
open import Math.Fin
open import Math.Function
open import Math.Id
open import Math.Nat
open import Math.Type

module _ {d} (0<d : 0 < d) where
  -- The map (q, r) ↦ qd + r
  euclid : ℕ × Fin d → ℕ
  euclid (q , r) = q * d + toℕ r

  euclid-+d : ∀ q r → euclid (q , r) + d ≡ euclid (suc q , r)
  euclid-+d = {!!}

  euclid-IsEquiv : IsEquiv euclid
  euclid-IsEquiv = {!!}

  divmod : ℕ → ℕ × Fin d
  divmod = inv euclid-IsEquiv

  quotient : ℕ → ℕ
  quotient n = fst (divmod n)

  remainder : ℕ → Fin d
  remainder n = snd (divmod n)
