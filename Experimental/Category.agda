{-# OPTIONS --cubical #-}
module Experimental.Category where

open import Math.Function hiding (id)
open import Math.Id
open import Math.Type

record Precategory ℓ : Type (ℓ-suc ℓ) where
  field
    Ob    : Type ℓ
    Hom   : Ob → Ob → Type ℓ
    id    : ∀ {x} → Hom x x
    comp  : ∀ {x y z} (f : Hom x y) (g : Hom y z) → Hom x z
    id-l  : ∀ {x y} (f : Hom x y) → comp id f ≡ f
    id-r  : ∀ {x y} (f : Hom x y) → comp f id ≡ f
    assoc : ∀ {w x y z} (f : Hom w x) (g : Hom x y) (h : Hom y z) → comp (comp f g) h ≡ comp f (comp g h)

open Precategory

record Iso {ℓ} (C : Precategory ℓ) (x y : Ob C) : Type ℓ where
  constructor iso
  field
    to    : Hom C x y
    from  : Hom C y x
    inv-l : C .comp from to ≡ C .id
    inv-r : C .comp to from ≡ C .id

open Iso

id-Iso : ∀ {ℓ} {C : Precategory ℓ} {x : Ob C} → Iso C x x
id-Iso {C = C} .to    = C .id
id-Iso {C = C} .from  = C .id
id-Iso {C = C} .inv-l = C .id-l (C .id)
id-Iso {C = C} .inv-r = C .id-r (C .id)

Id→Iso : ∀ {ℓ} {C : Precategory ℓ} {x y : Ob C} → x ≡ y → Iso C x y
Id→Iso {C = C} {x = x} = pathInd (λ y p → Iso C x y) id-Iso

-- TODO: type of homs is a set?
IsCategory : ∀ {ℓ} → Precategory ℓ → Type ℓ
IsCategory C = (x y : Ob C) → IsEquiv (Id→Iso {C = C} {x = x} {y = y})

-- Slice category
Slice : ∀ {ℓ} (C : Precategory ℓ) (c : Ob C) → Precategory ℓ
Slice C c .Ob = Σ[ x ∈ Ob C ] Hom C x c
Slice C c .Hom (x₁ , f₁) (x₂ , f₂) = Σ[ g ∈ Hom C x₁ x₂ ] C .comp g f₂ ≡ f₁
Slice C c .id = C .id , C .id-l _
Slice C c .comp (g₁ , p₁) (g₂ , p₂) = C .comp g₁ g₂ , C .assoc g₁ g₂ _ ∙ ap (C .comp g₁) p₂ ∙ p₁
Slice C c .id-l (g , p) = Σ≡ (C .id-l _) {!!}
Slice C c .id-r = {!!}
Slice C c .assoc = {!!}
