module Math.Order where

open import Math.Type

module StrictPartialOrder
  (A : Type₀)
  (A-IsSet : IsSet A)
  (_<_ : A → A → Type₀)
  (<-IsProp : ∀ {a b} → IsProp (a < b))
  (<-irrefl : ∀ {a} → ¬ a < a)
  (<-trans : ∀ {a b c} → a < b → b < c → a < c)
  where

  _≤_ : A → A → Type₀
  a ≤ b = (a < b) ⊎ (a ≡ b)

  ≤-IsProp : ∀ {a b} → IsProp (a ≤ b)
  ≤-IsProp (inl p₁)  (inl p₂)  = ap inl (<-IsProp p₁ p₂)
  ≤-IsProp (inl a<b) (inr a≡b) = ⊥-rec (<-irrefl (subst (_< _) a≡b a<b))
  ≤-IsProp (inr a≡b) (inl a<b) = ⊥-rec (<-irrefl (subst (_< _) a≡b a<b))
  ≤-IsProp (inr p₁)  (inr p₂)  = ap inr (A-IsSet _ _ p₁ p₂)

  <→≤ : ∀ {a b} → a < b → a ≤ b
  <→≤ = inl

  ≡→≤ : ∀ {a b} → a ≡ b → a ≤ b
  ≡→≤ = inr

  ≤-refl : ∀ {a} → a ≤ a
  ≤-refl = inr refl

  ≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
  ≤-trans (inl a<b) (inl b<c) = inl (<-trans a<b b<c)
  ≤-trans (inl a<b) (inr b≡c) = inl (subst (_ <_) b≡c a<b)
  ≤-trans (inr a≡b) (inl b<c) = inl (subst (_< _) (sym a≡b) b<c)
  ≤-trans (inr a≡b) (inr b≡c) = inr (a≡b ∙ b≡c)

  <≤-trans : ∀ {a b c} → a < b → b ≤ c → a < c
  <≤-trans a<b (inl b<c) = <-trans a<b b<c
  <≤-trans a<b (inr b≡c) = subst (_ <_) b≡c a<b

  ≤<-trans : ∀ {a b c} → a ≤ b → b < c → a < c
  ≤<-trans (inl a<b) b<c = <-trans a<b b<c
  ≤<-trans (inr a≡b) b<c = subst (_< _) (sym a≡b) b<c

  ≤-antisym : ∀ {a b} → a ≤ b → b ≤ a → a ≡ b
  ≤-antisym (inl a<b) (inl b<a) = ⊥-rec (<-irrefl (<-trans a<b b<a))
  ≤-antisym (inl a<b) (inr b≡a) = sym b≡a
  ≤-antisym (inr a≡b) _         = a≡b
