{-# OPTIONS --cubical #-}
module Systems.Log where

open import Math.Fin
open import Math.Function
open import Math.Nat
open import Math.Type

module Log
    (A : Type₀)
    (A-IsSet : IsSet A)
    (index : A → ℕ)
    (index-IsInjective : IsInjective index)
    (parent : ∀ {n} → fiber index (suc n) → fiber index n)
    where

  P : ℕ → Type₀
  P = fiber index

  P-IsProp : ∀ {a} → IsProp (P a)
  P-IsProp = IsInjective→fiber-IsProp A-IsSet ℕ-IsSet index-IsInjective _

  parent^ : ∀ {n} k → P (k + n) → P n
  parent^ zero    = id
  parent^ (suc k) = parent^ k ∘ parent

  _<L_ : A → A → Type₀
  a <L b = index a < index b

  <L-IsProp : ∀ {a b} → IsProp (a <L b)
  <L-IsProp = <-IsProp
