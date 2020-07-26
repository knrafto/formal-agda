{-# OPTIONS --cubical #-}
module Math.Mod where

open import Math.Fin
open import Math.Function
open import Math.Nat renaming (_+_ to _+ℕ_)
-- TODO: Math.Quotient?
open import Cubical.HITs.SetQuotients.Base using (_/_; [_])
open import Math.Type

module _ (d : ℕ) where
  _~_ : ℕ → ℕ → Type₀
  m ~ n = m +ℕ d ≡ n

  Mod : Type₀
  Mod = ℕ / _~_

module _ {d : ℕ} where
  -- "remainder"
  r : ℕ → Mod d
  r n = [ n ]

  φ : Fin d → Mod d
  φ i = r (toℕ i)

  φ-IsInjective : IsInjective φ
  φ-IsInjective = {!!}

  φ-IsEquiv : 0 < d → IsEquiv φ
  φ-IsEquiv = {!!}

  _+_ : Mod d → Mod d → Mod d
  _+_ = {!!}
