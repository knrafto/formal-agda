{-# OPTIONS --cubical #-}
module Experimental.Tree where

open import Math.Function
open import Math.Id
open import Math.Nat
open import Math.Type

-- See https://ncatlab.org/nlab/show/tree#as_functors
-- In set theory, one might call this a "finite-ish forest": http://math.huji.ac.il/~sunger/cmu/TreesTalk.pdf
module Tree
    (A : Type₀)
    (A-IsSet : IsSet A)
    (depth : A → ℕ)
    (parent : ∀ {n} → fiber depth (suc n) → fiber depth n)
    where

  T : ℕ → Type₀
  T = fiber depth

  T-IsSet : ∀ {n} → IsSet (T n)
  T-IsSet = Σ-IsSet A-IsSet λ a → IsProp→IsSet (ℕ-IsSet _ _)

  toT : (a : A) → T (depth a)
  toT a = (a , refl)

  -- iterated version of parent
  parent^ : ∀ {n} k → T (k + n) → T n
  parent^ zero    = id
  parent^ (suc k) = parent^ k ∘ parent

  -- functor ℕ^op → Set
  ancestor : ∀ {m n} → m ≤ n → T n → T m
  ancestor {m} {n} (k , k+m≡n) = parent^ k ∘ subst T (sym k+m≡n)

  ancestor-refl : ∀ {n} (x : T n) → ancestor ≤-refl x ≡ x
  ancestor-refl x = subst-refl T

  -- TODO: include diagram
  ancestor-trans : {l m n : ℕ} (l≤m : l ≤ m) (m≤n : m ≤ n) (x : T n)
    → ancestor (≤-trans l≤m m≤n) x ≡ ancestor l≤m (ancestor m≤n x)
  ancestor-trans {l} {m} {n} (k₁ , k₁+l≡m) (k₂ , k₂+m≡n) x = goal
    where
    n≡[k₂+k₁]+l : n ≡ (k₂ + k₁) + l
    n≡[k₂+k₁]+l = sym (snd (≤-trans (k₁ , k₁+l≡m) (k₂ , k₂+m≡n)))

    k₂+m≡k₂+[k₁+l] : ∀ {k₂} → k₂ + m ≡ k₂ + (k₁ + l)
    k₂+m≡k₂+[k₁+l] {k₂} = ap (λ x → k₂ + x) (sym k₁+l≡m)

    k₂+[k₁+l]≡[k₂+k₁]+l : ∀ {k₂} → k₂ + (k₁ + l) ≡ (k₂ + k₁) + l
    k₂+[k₁+l]≡[k₂+k₁]+l {k₂} = +-assoc k₂ k₁ l

    parent-nat : ∀ {m n} {p : m ≡ n} {x : T (suc m)} → subst T p (parent x) ≡ parent (subst T (ap suc p) x)
    parent-nat = subst-nat (λ n → T (suc n)) (λ n → T n) (λ n x → parent x)

    lemma₁ : ∀ {x} → subst T n≡[k₂+k₁]+l x ≡ subst T k₂+[k₁+l]≡[k₂+k₁]+l (subst T k₂+m≡k₂+[k₁+l] (subst T (sym k₂+m≡n) x))
    lemma₁ {x} = ap (λ p → subst T p x) (ℕ-IsSet _ _ _ _) ∙ subst-∙ T ∙ subst-∙ T

    lemma₂ : ∀ {k₂ x} → parent^ (k₂ + k₁) (subst T k₂+[k₁+l]≡[k₂+k₁]+l x) ≡ parent^ k₁ (parent^ k₂ x)
    lemma₂ {zero}   {x} = ap (parent^ k₁) (subst-refl T)
    lemma₂ {suc k₂} {x} = ap (parent^ (k₂ + k₁)) (sym parent-nat) ∙ lemma₂ {k₂ = k₂}

    lemma₃ : ∀ {k₂ x} → parent^ k₂ (subst T k₂+m≡k₂+[k₁+l] x) ≡ subst T (sym k₁+l≡m) (parent^ k₂ x)
    lemma₃ {zero}   {x} = refl
    lemma₃ {suc k₂} {x} = ap (parent^ k₂) (sym parent-nat) ∙ lemma₃ {k₂ = k₂}

    goal : parent^ (k₂ + k₁) (subst T n≡[k₂+k₁]+l x) ≡ parent^ k₁ (subst T (sym k₁+l≡m) (parent^ k₂ (subst T (sym k₂+m≡n) x)))
    goal = ap (parent^ (k₂ + k₁)) lemma₁ ∙ lemma₂ {k₂ = k₂} ∙ ap (parent^ k₁) (lemma₃ {k₂ = k₂})      

  -- "is ancestor of" relation
  _≤T_ : A → A → Type₀
  a ≤T b = Σ[ p ∈ depth a ≤ depth b ] ancestor p (toT b) ≡ toT a

  ≤T-IsProp : ∀ a b → IsProp (a ≤T b)
  ≤T-IsProp _ _ = Σ-IsProp ≤-IsProp λ _ → T-IsSet _ _

  ≤T-depth : ∀ a b → a ≤T b → depth a ≤ depth b
  ≤T-depth _ _ (m≤n , _) = m≤n

  ≤T-unique : ∀ a b c → a ≤T c → b ≤T c → depth a ≡ depth b → a ≡ b
  ≤T-unique a b c (da≤db , p₁) (db≤dc , p₂) da≡db =
    sym (subst-const da≡db) ∙ subst-nat T (λ _ → A) (λ n x → fst x) {p = da≡db} {u = toT a} ∙ ap fst lemma₂
    where
      lemma₁ : (l m n : ℕ) (x : T n) (p : l ≡ m) (l≤n : l ≤ n) (m≤n : m ≤ n)
        → subst T p (ancestor l≤n x) ≡ ancestor m≤n x
      lemma₁ l m n x =
        pathInd
          (λ m (p : l ≡ m) →
            (l≤n : l ≤ n) (m≤n : m ≤ n) → subst T p (ancestor l≤n x) ≡ ancestor m≤n x)
          λ (p₁ p₂ : l ≤ n) → subst-refl T ∙ happly (ap ancestor (≤-IsProp p₁ p₂)) x

      lemma₂ : subst T da≡db (toT a) ≡ toT b
      lemma₂ = ap (subst T da≡db) (sym p₁) ∙ lemma₁ (depth a) (depth b) (depth c) (toT c) da≡db da≤db db≤dc ∙ p₂

  -- ≤T is a partial order
  ≤T-refl : ∀ a → a ≤T a
  ≤T-refl a = ≤-refl , ancestor-refl (a , refl)

  ≤T-trans : ∀ a b c → a ≤T b → b ≤T c → a ≤T c
  ≤T-trans a b c (da≤db , p₁) (db≤dc , p₂)
    = ≤-trans da≤db db≤dc , ancestor-trans da≤db db≤dc (c , refl) ∙ ap (ancestor da≤db) p₂ ∙ p₁

  ≤T-antisym : ∀ a b → a ≤T b → b ≤T a → a ≡ b
  ≤T-antisym a b (m≤n , p₁) (n≤m , p₂)
    = ≤T-unique a b a (≤T-refl a) (n≤m , p₂) (≤-antisym m≤n n≤m)
