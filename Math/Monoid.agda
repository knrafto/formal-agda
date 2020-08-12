{-# OPTIONS --cubical #-}
module Math.Monoid where

open import Math.Function
open import Math.Id
open import Math.Prod
open import Math.Type renaming (_∙_ to trans)

IsAssociative : ∀ {ℓ} {A : Type ℓ} → (A → A → A) → Type ℓ
IsAssociative _∙_ = ∀ a b c → a ∙ (b ∙ c) ≡ (a ∙ b) ∙ c

IsAssociative-IsProp : ∀ {ℓ} {A : Type ℓ} (_∙_ : A → A → A) → IsSet A → IsProp (IsAssociative _∙_)
IsAssociative-IsProp _∙_ A-IsSet = Π-IsProp λ _ → Π-IsProp λ _ → Π-IsProp λ _ → A-IsSet _ _

HasIdentity : ∀ {ℓ} {A : Type ℓ} → (A → A → A) → Type ℓ
HasIdentity {A = A} _∙_ = Σ[ e ∈ A ] (∀ a → e ∙ a ≡ a) × (∀ a → a ∙ e ≡ a)

HasIdentity-IsProp : ∀ {ℓ} {A : Type ℓ} (_∙_ : A → A → A) → IsSet A → IsProp (HasIdentity _∙_)
HasIdentity-IsProp _∙_ A-IsSet (e₁ , e₁-l , e₁-r) (e₂ , e₂-l , e₂-r) =
  ΣProp≡
    (λ _ → ×-IsProp (Π-IsProp λ _ → A-IsSet _ _) (Π-IsProp λ _ → A-IsSet _ _))
    (trans (sym (e₂-r e₁)) (e₁-l e₂))

IsMonoid : ∀ {ℓ} (A : Type ℓ) → (A → A → A) → Type ℓ
IsMonoid A _∙_ = IsAssociative _∙_ × HasIdentity _∙_

IsMonoid-IsProp : ∀ {ℓ} (A : Type ℓ) (_∙_ : A → A → A) → IsSet A → IsProp (IsMonoid A _∙_)
IsMonoid-IsProp A _∙_ A-IsSet = ×-IsProp (IsAssociative-IsProp _∙_ A-IsSet) (HasIdentity-IsProp _∙_ A-IsSet)

MonoidStructure : ∀ {ℓ} (A : Type ℓ) → Type ℓ
MonoidStructure A = Σ[ _∙_ ∈ (A → A → A) ] (IsMonoid A _∙_)

MonoidStructure-IsSet : ∀ {ℓ} (A : Type ℓ) → IsSet A → IsSet (MonoidStructure A)
MonoidStructure-IsSet A A-IsSet = Σ-IsSet (→-IsSet (→-IsSet A-IsSet)) λ _∙_ → IsProp→IsSet (IsMonoid-IsProp A _∙_ A-IsSet)

Monoid : ∀ ℓ → Type (ℓ-suc ℓ)
Monoid ℓ = Σ[ A ∈ Type ℓ ] IsSet A × MonoidStructure A

⟨_⟩ : ∀ {ℓ} → Monoid ℓ → Type ℓ
⟨ A ⟩ = fst A

⟨⟩-IsSet : ∀ {ℓ} (A : Monoid ℓ) → IsSet ⟨ A ⟩
⟨⟩-IsSet (_ , ⟨A⟩-IsSet , _) = ⟨A⟩-IsSet

structure : ∀ {ℓ} (A : Monoid ℓ) → MonoidStructure ⟨ A ⟩
structure (_ , _ , str) = str

op : ∀ {ℓ} → (A : Monoid ℓ) → ⟨ A ⟩ → ⟨ A ⟩ → ⟨ A ⟩
op (_ , _ , op , _) = op

e : ∀ {ℓ} → (A : Monoid ℓ) → ⟨ A ⟩
e (_ , _ , _ , _ , e , _) = e

IsHom : ∀ {ℓ} (A B : Monoid ℓ) → (⟨ A ⟩ → ⟨ B ⟩) → Type ℓ
IsHom A B f = (∀ a b → f (op A a b) ≡ op B (f a) (f b)) × (f (e A) ≡ e B)

IsHom-IsProp : ∀ {ℓ} (A B : Monoid ℓ) (f : ⟨ A ⟩ → ⟨ B ⟩) → IsProp (IsHom A B f)
IsHom-IsProp A B f = ×-IsProp (Π-IsProp λ _ → Π-IsProp λ _ → ⟨⟩-IsSet B _ _) (⟨⟩-IsSet B _ _)

Hom : ∀ {ℓ} → Monoid ℓ → Monoid ℓ → Type ℓ
Hom A B = Σ[ f ∈ (⟨ A ⟩ → ⟨ B ⟩) ] IsHom A B f

id-IsHom : ∀ {ℓ} (A : Monoid ℓ) → IsHom A A id
id-IsHom A = (λ a b → refl) , refl

id-Hom : ∀ {ℓ} (A : Monoid ℓ) → Hom A A
id-Hom A = id , id-IsHom A

∘-IsHom : ∀ {ℓ} (A B C : Monoid ℓ) (g : ⟨ B ⟩ → ⟨ C ⟩) (f : ⟨ A ⟩ → ⟨ B ⟩) → IsHom B C g → IsHom A B f → IsHom A C (g ∘ f)
∘-IsHom A B C g f (g-op , g-e) (f-op , f-e) = (λ a b → trans (ap g (f-op _ _)) (g-op _ _)) , trans (ap g f-e) g-e

∘-Hom : ∀ {ℓ} {A B C : Monoid ℓ} → Hom B C → Hom A B → Hom A C
∘-Hom {A = A} {B = B} {C = C} (g , g-IsHom) (f , f-IsHom) = g ∘ f , ∘-IsHom A B C g f g-IsHom f-IsHom

IsIso : ∀ {ℓ} (A B : Monoid ℓ) → (⟨ A ⟩ → ⟨ B ⟩) → Type ℓ
IsIso A B f = IsEquiv f × IsHom A B f

-- note: if f is a homomorphism, then f⁻¹ is automatically a homomorphism too

Iso : ∀ {ℓ} → Monoid ℓ → Monoid ℓ → Type ℓ
Iso A B = Σ[ f ∈ (⟨ A ⟩ → ⟨ B ⟩) ] IsIso A B f

id-Iso : ∀ {ℓ} (A : Monoid ℓ) → Iso A A
id-Iso A = id , id-IsEquiv , id-IsHom A

-- First, characterize A ≡ B
Monoid≡ : ∀ {ℓ} (A B : Monoid ℓ) → Σ[ p ∈ ⟨ A ⟩ ≡ ⟨ B ⟩ ] subst MonoidStructure p (structure A) ≡ structure B → A ≡ B
Monoid≡ A B (p , q) = Σ≡ p (×≡ (IsSet-IsProp _ _ , q))

Monoid≡-IsEquiv : ∀ {ℓ} (A B : Monoid ℓ) → IsEquiv (Monoid≡ A B)
Monoid≡-IsEquiv A B = {!!}

≡→Iso : ∀ {ℓ} (A B : Monoid ℓ) → A ≡ B → Iso A B
≡→Iso A B = {!!}

≡→Iso-IsEquiv : ∀ {ℓ} (A B : Monoid ℓ) → IsEquiv (≡→Iso A B)
≡→Iso-IsEquiv = {!!}

-- ℕ is free monoid on one element. ⟨ A ⟩ ≃ Hom ℕ A
