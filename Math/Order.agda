{-# OPTIONS --cubical --no-prop #-}
module Math.Order where

open import Math.Nat
open import Math.Type

private
  variable
    ℓ ℓ' : Level

-- Subsets.
-- TODO: move.
Subset : Type ℓ → Type (ℓ-suc ℓ)
Subset {ℓ = ℓ} A = Σ[ P ∈ (A → Type ℓ) ] ∀ (a : A) → IsProp (P a)

infix 6 _∈_

_∈_ : {A : Type ℓ} → A → Subset A → Type ℓ
a ∈ (P , _) = P a

∈-IsProp : {A : Type ℓ} (a : A) (S : Subset A) → IsProp (a ∈ S)
∈-IsProp a (P , P-IsProp) = P-IsProp a

module _ {A : Type ℓ}
  (_<_ : A → A → Type ℓ)
  (<-IsProp : ∀ {a b : A} → IsProp (a < b))
  (trans : ∀ {a b c : A} → a < b → b < c → a < c)
  where

  data Trichotomy (a b : A) : Type ℓ where
    lt : a < b → Trichotomy a b
    eq : a ≡ b → Trichotomy a b
    gt : b < a → Trichotomy a b

  HasTrichotomy : Type ℓ
  HasTrichotomy = (a b : A) → Trichotomy a b

  -- TODO: HasTrichotomy-IsProp

  IsMax :  Subset A → A → Type ℓ
  IsMax S m = m ∈ S × (∀ (a : A) → m < a → ¬ a ∈ S)

  IsMax-IsProp : (S : Subset A) (m : A) → IsProp (IsMax S m)
  IsMax-IsProp S m = ×-IsProp (∈-IsProp m S) (Π-IsProp (λ a → Π-IsProp (λ m<a → ¬-IsProp)))

  Max : Subset A → Type ℓ
  Max S = Σ A (IsMax S)

  Max-IsProp : {S : Subset A} → HasTrichotomy → IsProp (Max S)
  Max-IsProp {S = S} trichotomy (m₁ , m₁∈S , m₁-max) (m₂ , m₂∈S , m₂-max) = ΣProp≡ (IsMax-IsProp S) m₁≡m₂
    where
    m₁≡m₂ : m₁ ≡ m₂ 
    m₁≡m₂ = case trichotomy m₁ m₂ of λ {
      (lt m₁<m₂) → contradiction m₂∈S (m₁-max m₂ m₁<m₂) ;
      (eq m₁≡m₂) → m₁≡m₂ ;
      (gt m₂<m₁) → contradiction m₁∈S (m₂-max m₁ m₂<m₁) }
  
  IsUpperBound : Subset A → A → Type ℓ
  IsUpperBound S u = ∀ (s : A) → s ∈ S → s < u

  IsUpperBound-IsProp : (S : Subset A) (u : A) → IsProp (IsUpperBound S u)
  IsUpperBound-IsProp S u = Π-IsProp (λ s → Π-IsProp (λ s∈S → <-IsProp))

  IsUpperSet : Subset A → Type ℓ
  IsUpperSet S = ∀ {a b : A} → a < b → a ∈ S → b ∈ S

  UpperSet : Type (ℓ-suc ℓ)
  UpperSet = Σ (Subset A) IsUpperSet

  principal : A → UpperSet
  principal u = ((λ a → u < a) , λ a → <-IsProp) , λ a<b u<a → trans u<a a<b

  -- Sets where every element is an upper bound has a surpremum of ∞ 
  -∞ : UpperSet
  -∞ = ((λ a → Lift ⊤) , λ a → Lift-IsProp (⊤-IsProp)) , λ a<b _ → lift tt

  -- Sets that have no upper bound have a supremum of ∞
  ∞ : UpperSet
  ∞ = ((λ a → Lift ⊥) , λ a → Lift-IsProp (⊥-IsProp)) , λ a<b ff → ff

  -- TODO: closure lower set?
  supremum : Subset A → UpperSet
  supremum S = (IsUpperBound S , IsUpperBound-IsProp S) , λ a<b a-IsUpperBound s s∈S → trans (a-IsUpperBound s s∈S) a<b

  -- IsMax-supremum : {S : Subset A} (m : A) → IsMax S m → closure S ≡ principal m
  -- IsMax-supremum m m-IsMax = {!!}
