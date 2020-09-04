{-# OPTIONS --cubical #-}
module Math.Id where

open import Cubical.Foundations.Prelude using (J; substRefl; transportRefl)
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

subst-loop : {A : Type ℓ} (P : A → Type ℓ') {a : A} {x : P a} {p : a ≡ a} → IsSet A → subst P p x ≡ x
subst-loop P {x = x} A-IsSet = ap (λ p → subst P p x) (A-IsSet _ _ _ _) ∙ substRefl {B = P} x

subst-a≡ : {A : Type ℓ} {a x y : A} {p : x ≡ y} {q : a ≡ x} → subst (a ≡_) p q ≡ q ∙ p
subst-a≡ {a = a} {p = p} {q = q} = pathInd (λ x p → subst (a ≡_) p q ≡ q ∙ p) (subst-refl (a ≡_) ∙ sym (∙-refl)) p

transport-refl : {A : Type ℓ} {a : A} → transport refl a ≡ a
transport-refl = transportRefl _

subst-nat : {A : Type ℓ} (P Q : A → Type ℓ') (f : (x : A) → P x → Q x) {x y : A} {p : x ≡ y} {u : P x}
  → subst Q p (f x u) ≡ f y (subst P p u)
subst-nat P Q f {x = x} {p = p} {u = u} =
  pathInd
    (λ y p → subst Q p (f x u) ≡ f y (subst P p u))
    (subst-refl Q ∙ ap (f x) (sym (subst-refl P))) p

sym-≡[]≡ : {A B : Type ℓ} (p : A ≡ B) {x : A} {y : B} → x ≡[ p ]≡ y → y ≡[ sym p ]≡ x
sym-≡[]≡ {A = A} p {x = x} {y = y} =
  pathInd
    (λ B p → (x : A) (y : B) → x ≡[ p ]≡ y → y ≡[ sym p ]≡ x)
    (λ x y p → transport-refl ∙ sym p ∙ transport-refl)
    p x y

sym-∙ : ∀ {A : Type ℓ} {a b c : A} {p : a ≡ b} {q : b ≡ c} → sym (p ∙ q) ≡ sym q ∙ sym p
sym-∙ {p = p} {q = q} = pathInd (λ c q → sym (p ∙ q) ≡ sym q ∙ sym p) (ap sym (∙-refl {p = p}) ∙ sym refl-∙) q

subst-∙ : {A : Type ℓ} (P : A → Type ℓ') {a b c : A} {p : a ≡ b} {q : b ≡ c} {x : P a}
  → subst P (p ∙ q) x ≡ subst P q (subst P p x)
subst-∙ P {p = p} {q = q} {x = x} =
  pathInd
    (λ c q → subst P (p ∙ q) x ≡ subst P q (subst P p x))
    (ap (λ p → subst P p x) ∙-refl ∙ sym (subst-refl P))
    q

subst-const : {A : Type ℓ} {B : Type ℓ'} {a b : A} {x : B} (p : a ≡ b) → subst (λ _ → B) p x ≡ x
subst-const {A = A} {B = B} {a = a} {x = x} =
  pathInd (λ b p → subst (λ _ → B) p x ≡ x) (subst-refl {A = A} (λ _ → B) {a = a})

apd : {A : Type ℓ} {B : A → Type ℓ'} {x y : A} (f : (a : A) → B a) (p : x ≡ y) → subst B p (f x) ≡ f y
apd {B = B} {x = x} f = pathInd (λ y p → subst B p (f x) ≡ f y) (subst-refl B)
