{-# OPTIONS --cubical #-}
module Math.Monoid where

open import Math.Function
open import Math.Id
open import Math.Nat
open import Math.Prod
open import Math.Type

private
  variable
    ℓ ℓ' ℓ'' : Level

record Monoid (ℓ : Level) : Type (ℓ-suc ℓ) where
  -- TODO: use ⋅ (LaTeX \cdot) or · (Agda's version)?
  infixl 7 _⋅_

  field
    Carrier : Type ℓ
    Carrier-IsSet : IsSet Carrier

    ε : Carrier
    _⋅_ : Carrier → Carrier → Carrier

    assoc : ∀ a b c → a ⋅ (b ⋅ c) ≡ (a ⋅ b) ⋅ c
    identity-l : ∀ a → ε ⋅ a ≡ a
    identity-r : ∀ a → a ⋅ ε ≡ a

⟨_⟩ : Monoid ℓ → Type ℓ
⟨_⟩ = Monoid.Carrier

IsHom : (A : Monoid ℓ) (B : Monoid ℓ') → (⟨ A ⟩ → ⟨ B ⟩) → Type _
IsHom A B f = (f A.ε ≡ B.ε) × (∀ a b → f (a A.⋅ b) ≡ f a B.⋅ f b)
  where
  module A = Monoid A
  module B = Monoid B

IsHom-IsProp : (A : Monoid ℓ) (B : Monoid ℓ') (f : ⟨ A ⟩ → ⟨ B ⟩) → IsProp (IsHom A B f)
IsHom-IsProp A B f = ×-IsProp (B.Carrier-IsSet _ _) (Π-IsProp λ _ → Π-IsProp λ _ → B.Carrier-IsSet _ _)
  where
  module B = Monoid B

Hom : Monoid ℓ → Monoid ℓ' → Type _
Hom A B = Σ[ f ∈ (⟨ A ⟩ → ⟨ B ⟩) ] IsHom A B f

id-IsHom : (A : Monoid ℓ) → IsHom A A id
id-IsHom A = refl , λ a b → refl

id-Hom : (A : Monoid ℓ) → Hom A A
id-Hom A = id , id-IsHom A

∘-IsHom : (A : Monoid ℓ) (B : Monoid ℓ') (C : Monoid ℓ'') (g : ⟨ B ⟩ → ⟨ C ⟩) (f : ⟨ A ⟩ → ⟨ B ⟩) → IsHom B C g → IsHom A B f → IsHom A C (g ∘ f)
∘-IsHom A B C g f (g-ε , g-⋅) (f-ε , f-⋅) = ap g f-ε ∙ g-ε , λ a b → ap g (f-⋅ _ _) ∙ (g-⋅ _ _)

∘-Hom : {A : Monoid ℓ} {B : Monoid ℓ'} {C : Monoid ℓ''} → Hom B C → Hom A B → Hom A C
∘-Hom {A = A} {B = B} {C = C} (g , g-IsHom) (f , f-IsHom) = g ∘ f , ∘-IsHom A B C g f g-IsHom f-IsHom

IsIso : (A : Monoid ℓ) (B : Monoid ℓ') → (⟨ A ⟩ → ⟨ B ⟩) → Type _
IsIso A B f = IsEquiv f × IsHom A B f

-- TODO: if f is a homomorphism, then f⁻¹ is automatically a homomorphism

Iso : Monoid ℓ → Monoid ℓ' → Type _
Iso A B = Σ[ f ∈ (⟨ A ⟩ → ⟨ B ⟩) ] IsIso A B f

id-Iso : (A : Monoid ℓ) → Iso A A
id-Iso A = id , id-IsEquiv , id-IsHom A

-- TODO: structure-identity principle for Monoid

ℕ-Monoid : Monoid ℓ-zero
ℕ-Monoid = record
  { Carrier = ℕ
  ; Carrier-IsSet = ℕ-IsSet
  ; ε = 0
  ; _⋅_ = _+_
  ; assoc = +-assoc
  ; identity-l = λ _ → refl
  ; identity-r = +-zero
  }

pow : (M : Monoid ℓ) → ⟨ M ⟩ → ℕ → ⟨ M ⟩
pow M a = f
  where
  open Monoid M

  f : ℕ → ⟨ M ⟩
  f zero = ε
  f (suc n) = a ⋅ f n

pow-Hom : (M : Monoid ℓ) → ⟨ M ⟩ → Hom ℕ-Monoid M
pow-Hom M a = pow M a , refl , pow-+
  where
  open Monoid M

  pow-+ : ∀ m n → pow M a (m + n) ≡ pow M a m ⋅ pow M a n
  pow-+ zero n = sym (identity-l (pow M a n))
  pow-+ (suc m) n = ap (a ⋅_) (pow-+ m n) ∙ assoc a (pow M a m) (pow M a n)

-- ℕ is the free monoid on one element
pow-IsEquiv : (M : Monoid ℓ) → IsEquiv (pow-Hom M)
pow-IsEquiv M = HasInverse→IsEquiv (λ (f , _) → f 1) identity-r (λ (h , h-IsHom) → ΣProp≡ (IsHom-IsProp ℕ-Monoid M) (funExt (unique h h-IsHom)))
  where
  open Monoid M

  unique : (h : ℕ → ⟨ M ⟩) → IsHom ℕ-Monoid M h → (n : ℕ) → pow M (h 1) n ≡ h n
  unique h (h-0 , h-+) zero = sym h-0
  unique h (h-0 , h-+) (suc n) = ap (h 1 ⋅_) (unique h (h-0 , h-+) n) ∙ sym (h-+ 1 n)
