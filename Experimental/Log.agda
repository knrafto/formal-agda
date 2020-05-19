{-# OPTIONS --cubical #-}
module Experimental.Log where

open import Math.Fin
open import Math.Function
open import Math.Nat
open import Math.Type

module _
    (A : Type₀)
    (A-IsSet : IsSet A)
    (depth : A → ℕ)
    (depth-IsInjective : IsInjective depth)
    (parent : ∀ {n} → fiber depth (suc n) → fiber depth n)
    where

  P : ℕ → Type₀
  P = fiber depth

  P-IsProp : ∀ {a} → IsProp (P a)
  P-IsProp = IsInjective→fiber-IsProp A-IsSet ℕ-IsSet depth-IsInjective _

  parent^ : ∀ {n} k → P (k + n) → P n
  parent^ zero    = id
  parent^ (suc k) = parent^ k ∘ parent

  _<T_ : A → A → Type₀
  a <T b = depth a < depth b

  <T-IsProp : ∀ {a b} → IsProp (a < b)
  <T-IsProp = <-IsProp
