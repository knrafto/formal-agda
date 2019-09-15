{-# OPTIONS --cubical #-}
module Math.Id where

open import Cubical.Foundations.Prelude using (J; substRefl)
open import Cubical.Foundations.GroupoidLaws using (lUnit; rUnit)
open import Math.Function
open import Math.Type

private
  variable
    ℓ ℓ' ℓ'' : Level

-- The J rule.
-- TODO: which arguments can be made implicit?
pathInd : {A : Type ℓ} {a : A} (P : (x : A) → a ≡ x → Type ℓ') → P a refl → {x : A} (p : a ≡ x) → P x p
pathInd = J

refl-∙ : {A : Type ℓ} {a b : A} {p : a ≡ b} → refl ∙ p ≡ p
refl-∙ {p = p} = sym (lUnit p)

∙-refl : {A : Type ℓ} {a b : A} {p : a ≡ b} → p ∙ refl ≡ p
∙-refl {p = p} = sym (rUnit p)

subst-refl : {A : Type ℓ} (P : A → Type ℓ') {a : A} {x : P a} → subst P refl x ≡ x
subst-refl P {x = x} = substRefl {B = P} x

subst-a≡ : {A : Type ℓ} {a x y : A} {p : x ≡ y} {q : a ≡ x} → subst (a ≡_) p q ≡ q ∙ p
subst-a≡ {a = a} {p = p} {q = q} = pathInd (λ x p → subst (a ≡_) p q ≡ q ∙ p) (subst-refl (a ≡_) ∙ sym (∙-refl)) p
