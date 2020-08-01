{-# OPTIONS --cubical #-}
module Math.Quotient where

open import Cubical.Foundations.Prelude using (toPathP)
-- TODO: is [_] a good name?
open import Cubical.HITs.SetQuotients public using (_/_; [_])
open import Cubical.HITs.SetQuotients using (elim; elimProp)
open import Math.Id
open import Math.Type

-- TODO: can we get rid of the implicit argument to _≡_?
/-≡ : ∀ {ℓ ℓ'} {A : Type ℓ} {R : A → A → Type ℓ'} (x y : A) → R x y → _≡_ {A = A / R} [ x ] [ y ]
/-≡ = _/_.eq/

/-IsSet :  ∀ {ℓ ℓ'} {A : Type ℓ} {R : A → A → Type ℓ'} → IsSet (A / R)
/-IsSet = _/_.squash/

/-ind-IsProp :
  ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {R : A → A → Type ℓ'} {P : A / R → Type ℓ''} →
  (∀ x → IsProp (P x)) →
  ((a : A) → P [ a ]) →
  (x : A / R) → P x
/-ind-IsProp = elimProp

/-ind-IsSet :
  ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {R : A → A → Type ℓ'} {B : A / R → Type ℓ''} →
  (∀ x → IsSet (B x)) →
  (f : (a : A) → B [ a ]) →
  (∀ a b r → subst B (/-≡ a b r) (f a) ≡ f b) →
  (x : A / R) → B x
/-ind-IsSet B-IsSet f p = elim B-IsSet f (λ a b r → toPathP (p a b r))

/-rec : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {R : A → A → Type ℓ'} {B : Type ℓ''} →
  IsSet B →
  (f : A → B) →
  (∀ a b → R a b → f a ≡ f b) →
  A / R → B
/-rec {A = A} {R = R} B-IsSet f p =
  /-ind-IsSet (λ _ → B-IsSet) f (λ a b r → subst-const {A = A / R} (/-≡ a b r) ∙ p a b r)
