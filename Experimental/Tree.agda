{-# OPTIONS --cubical #-}
module Experimental.Tree where

open import Math.Function
open import Math.Id
open import Math.Nat
open import Math.Type

-- See https://ncatlab.org/nlab/show/tree#as_functors
module _
    (F : ℕ → Type₀)
    (φ : (n : ℕ) → F (suc n) → F n)
    (F-IsSet : (n : ℕ) → IsSet (F n)) where

  ancestor : {m n : ℕ} → m ≤ n → F n → F m
  ancestor = {!!}

  ancestor-refl : {n : ℕ} (f : F n) → ancestor ≤-refl f ≡ f
  ancestor-refl = {!!}

  ancestor-trans : {l m n : ℕ} (p₁ : l ≤ m) (p₂ : m ≤ n) (f : F n)
    → ancestor (≤-trans p₁ p₂) f ≡ ancestor p₁ (ancestor p₂ f)
  ancestor-trans = {!!}

  Node : Type₀
  Node = Σ[ n ∈ ℕ ] F n

  depth : Node → ℕ
  depth (n , _) = n

  IsAncestor : Node → Node → Type₀
  IsAncestor (m , fm) (n , fn) = Σ[ p ∈ m ≤ n ] ancestor p fn ≡ fm

  IsAncestor-IsProp : ∀ a b → IsProp (IsAncestor a b)
  IsAncestor-IsProp _ _ = Σ-IsProp ≤-IsProp λ _ → F-IsSet _ _ _

  IsAncestor-refl : ∀ a → IsAncestor a a
  IsAncestor-refl (n , fn) = ≤-refl , ancestor-refl fn

  IsAncestor-trans : ∀ a b c
    → IsAncestor a b → IsAncestor b c → IsAncestor a c
  IsAncestor-trans (l , fl) (m , fm) (n , fn) (l≤m , p₁) (m≤n , p₂)
    = ≤-trans l≤m m≤n , ancestor-trans l≤m m≤n fn ∙ ap (ancestor l≤m) p₂ ∙ p₁

  ancestor-unique : ∀ a b c
    → IsAncestor a c → IsAncestor b c → depth a ≡ depth b → a ≡ b
  ancestor-unique (l , fl) (m , fm) (n , fn) (l≤n , pl) (m≤n , pm) l≡m
    = Σ≡ l≡m (ap (subst F l≡m) (sym pl) ∙ lemma m l≡m l≤n m≤n ∙ pm)
    where
      lemma : (m : ℕ) (p : l ≡ m) (l≤n : l ≤ n) (m≤n : m ≤ n)
        → subst F p (ancestor l≤n fn) ≡ ancestor m≤n fn
      lemma m =
        pathInd
          (λ m (p : l ≡ m) →
            (l≤n : l ≤ n) (m≤n : m ≤ n) → subst F p (ancestor l≤n fn) ≡ ancestor m≤n fn)
          λ (p₁ p₂ : l ≤ n) → subst-refl F ∙ happly (ap ancestor (≤-IsProp p₁ p₂)) fn

  IsAncestor-antisym : ∀ a b
    → IsAncestor a b → IsAncestor b a → a ≡ b
  IsAncestor-antisym a b (m≤n , p₁) (n≤m , p₂)
    = ancestor-unique a b a (IsAncestor-refl a) (n≤m , p₂) (≤-antisym m≤n n≤m)
