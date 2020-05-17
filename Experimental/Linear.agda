{-# OPTIONS --cubical #-}
module Experimental.Linear where

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

  -- TODO: name me
  φ : (b : A) → Fin (depth b) → Σ[ a ∈ A ] a <T b
  φ b (i , i<db) = let a , da≡i = parent^ k (b , db≡k+i) in a , subst (λ i → i < depth b) (sym da≡i) i<db
    where
    k : ℕ
    k = fst (<-weaken i<db)

    db≡k+i : depth b ≡ k + i
    db≡k+i = sym (snd (<-weaken i<db))

  ψ : (b : A) → Σ[ a ∈ A ] a <T b → Fin (depth b)
  ψ b (a , a<Tb) = depth a , a<Tb

  oneway : ∀ b x → φ b (ψ b x) ≡ x
  oneway b (a , da<db) = ΣProp≡ (λ a → <T-IsProp) goal
    where
    k : ℕ
    k = fst (<-weaken da<db)

    db≡k+da : depth b ≡ k + depth a
    db≡k+da = sym (snd (<-weaken da<db))

    goal : fst (parent^ k (b , db≡k+da)) ≡ a
    goal = {!!}

  otherway : ∀ b x → ψ b (φ b x) ≡ x
  otherway b (i , i<db) = toℕ-IsInjective (lemma (fst (<-weaken i<db)))
    where
    lemma : ∀ k {p : P (k + i)} → depth (fst (parent^ k p)) ≡ i
    lemma zero    {p} = snd p
    lemma (suc k) {p} = lemma k
