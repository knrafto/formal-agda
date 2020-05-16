{-# OPTIONS --cubical #-}
module Math.Type where

open import Cubical.Core.Everything public using (Level; ℓ-zero; ℓ-suc; ℓ-max; Type; Type₀; Type₁; _≡_; Σ; Σ-syntax; _,_; fst; snd)
open import Cubical.Foundations.HLevels public using (ΣProp≡) renaming (propPi to Π-IsProp; isPropSigma to Σ-IsProp; isSetPi to Π-IsSet)
open import Cubical.Foundations.HLevels using (isOfHLevel; isOfHLevelΣ)
open import Cubical.Foundations.Prelude public using (Lift; lift; lower; refl; sym; _∙_; subst; transport) renaming (cong to ap; isContr to IsContr; isProp to IsProp; isSet to IsSet; isContr→isProp to IsContr→IsProp; isProp→isSet to IsProp→IsSet)
open import Cubical.Data.Empty public using (⊥; ⊥-elim) renaming (isProp⊥ to ⊥-IsProp)
open import Cubical.Data.Sum public using (_⊎_; inl; inr)
open import Cubical.Data.Unit public using (tt) renaming (Unit to ⊤; isContrUnit to ⊤-IsContr; isPropUnit to ⊤-IsProp)
open import Cubical.Data.Nat public using (ℕ)
open import Cubical.Data.Sigma using (sigmaPath→pathSigma)
open import Cubical.HITs.PropositionalTruncation public using (∥_∥; ∣_∣) renaming (propTruncIsProp to ∥∥-IsProp; recPropTrunc to ∥∥-rec)
open import Cubical.Relation.Nullary public using (¬_)

private
  variable
    ℓ ℓ' : Level

infix 4 _≡[_]≡_
infixr 5 _×_

-- Equality over another equality.
_≡[_]≡_ : ∀ {ℓ} {A B : Type ℓ} → A → A ≡ B → B → Type ℓ
a ≡[ p ]≡ b = transport p a ≡ b

-- Cubical defines × as a new record, but being compatible with Σ-type maxes it much easier to work with.
_×_ : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A × B = Σ[ x ∈ A ] B

case_of_ : {A : Type ℓ} {B : A → Type ℓ'} → (x : A) → (∀ x → B x) → B x
case x of f = f x

case_return_of_ : {A : Type ℓ} (x : A) (B : Type ℓ') → (∀ x → B) → B
case x return P of f = f x

the : {A : Type ℓ} → IsContr A → A
the = fst

the≡ : {A : Type ℓ} {a : A} → (A-IsContr : IsContr A) → the A-IsContr ≡ a
the≡ {a = a} A-IsContr = snd A-IsContr a

Lift-IsProp : {A : Type ℓ} → IsProp A → IsProp (Lift {j = ℓ'} A)
Lift-IsProp A-IsProp (lift a) (lift b) = ap lift (A-IsProp a b) 

contradiction : {A : Type ℓ} {B : Type ℓ'} → A → ¬ A → B
contradiction a ¬A = ⊥-elim (¬A a)

Π : (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
Π A B = (a : A) → B a

¬-IsProp : {A : Type ℓ} → IsProp (¬ A)
¬-IsProp = Π-IsProp (λ a → ⊥-IsProp)

Σ≡ : {A : Type ℓ} {B : A → Type ℓ'} {x y : Σ A B} (p : fst x ≡ fst y) → subst B p (snd x) ≡ snd y → x ≡ y
Σ≡ {x = x} {y = y} p q = sigmaPath→pathSigma x y (p , q)

Σ-IsSet : {A : Type ℓ} {B : A → Type ℓ'} → IsSet A → ((a : A) → IsSet (B a)) → IsSet (Σ A B)
Σ-IsSet A-IsSet B-IsSet = isOfHLevelΣ 2 A-IsSet B-IsSet

HasHLevel× : {A : Type ℓ} {B : Type ℓ'} (n : ℕ) → isOfHLevel n A → isOfHLevel n B → isOfHLevel n (A × B)
HasHLevel× n a b = isOfHLevelΣ n a (λ _ → b)

×-IsProp : {A : Type ℓ} {B : Type ℓ'} → IsProp A → IsProp B → IsProp (A × B)
×-IsProp = HasHLevel× 1

⊤-elim : {A : Type ℓ} → A → (⊤ → A)
⊤-elim a tt = a

⊤-IsSet : IsSet ⊤
⊤-IsSet = IsProp→IsSet ⊤-IsProp
