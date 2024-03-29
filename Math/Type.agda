module Math.Type where

-- TODO: Necessary to enable literal overloading. Where should I put this?
open import Agda.Builtin.FromNat public

open import Cubical.Core.Everything public using (Level; ℓ-zero; ℓ-suc; ℓ-max; Type; _≡_; Σ; Σ-syntax; _,_; fst; snd)
open import Cubical.Foundations.HLevels public using () renaming (isPropΠ to Π-IsProp; isPropΣ to Σ-IsProp; isSetΠ to Π-IsSet)
open import Cubical.Foundations.HLevels using (isOfHLevel; isOfHLevelΣ; isPropIsOfHLevel)
open import Cubical.Foundations.Prelude public using (Lift; lift; lower; refl; sym; _∙_; subst; transport) renaming (cong to ap; cong₂ to ap₂; isContr to IsContr; isProp to IsProp; isSet to IsSet; isContr→isProp to IsContr→IsProp; isProp→isSet to IsProp→IsSet)
open import Cubical.Data.Empty public using (⊥) renaming (rec to ⊥-rec; elim to ⊥-ind; isProp⊥ to ⊥-IsProp)
open import Cubical.Data.Sum public using (_⊎_; inl; inr)
open import Cubical.Data.Unit public using (tt) renaming (Unit to ⊤; isContrUnit to ⊤-IsContr; isPropUnit to ⊤-IsProp)
open import Cubical.Data.Nat public using (ℕ; fromNatℕ)
-- TODO: rename ΣProp≡
open import Cubical.Data.Sigma public using (_×_) renaming (Σ≡Prop to ΣProp≡)
open import Cubical.Data.Sigma using (ΣPathTransport→PathΣ)
open import Cubical.HITs.PropositionalTruncation public using (∥_∥; ∣_∣) renaming (propTruncIsProp to ∥∥-IsProp; rec to ∥∥-rec)
open import Cubical.Relation.Nullary public using (¬_)

private
  variable
    ℓ ℓ' : Level

infixr 5 _∧_
infixr 4 _∨_
infix 4 _≡[_]≡_

-- Equality over another equality.
_≡[_]≡_ : ∀ {ℓ} {A B : Type ℓ} → A → A ≡ B → B → Type ℓ
a ≡[ p ]≡ b = transport p a ≡ b

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
contradiction a ¬A = ⊥-rec (¬A a)

IsProp-IsProp : {A : Type ℓ} → IsProp (IsProp A)
IsProp-IsProp = isPropIsOfHLevel 1

IsSet-IsProp : {A : Type ℓ} → IsProp (IsSet A)
IsSet-IsProp = isPropIsOfHLevel 2

Π : (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
Π A B = (a : A) → B a

¬-IsProp : {A : Type ℓ} → IsProp (¬ A)
¬-IsProp = Π-IsProp (λ a → ⊥-IsProp)

→-IsProp : {A : Type ℓ} {B : Type ℓ'} → IsProp B → IsProp (A → B)
→-IsProp B-IsProp = Π-IsProp (λ a → B-IsProp)

→-IsSet : {A : Type ℓ} {B : Type ℓ'} → IsSet B → IsSet (A → B)
→-IsSet B-IsSet = Π-IsSet (λ a → B-IsSet)

Σ≡ : {A : Type ℓ} {B : A → Type ℓ'} {x y : Σ A B} (p : fst x ≡ fst y) → subst B p (snd x) ≡ snd y → x ≡ y
Σ≡ {x = x} {y = y} p q = ΣPathTransport→PathΣ x y (p , q)

Σ-IsSet : {A : Type ℓ} {B : A → Type ℓ'} → IsSet A → ((a : A) → IsSet (B a)) → IsSet (Σ A B)
Σ-IsSet A-IsSet B-IsSet = isOfHLevelΣ 2 A-IsSet B-IsSet

HasHLevel× : {A : Type ℓ} {B : Type ℓ'} (n : ℕ) → isOfHLevel n A → isOfHLevel n B → isOfHLevel n (A × B)
HasHLevel× n a b = isOfHLevelΣ n a (λ _ → b)

×-IsProp : {A : Type ℓ} {B : Type ℓ'} → IsProp A → IsProp B → IsProp (A × B)
×-IsProp = HasHLevel× 1

_∧_ : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
_∧_ = _×_

∧-IsProp : {A : Type ℓ} {B : Type ℓ'} → IsProp A → IsProp B → IsProp (A ∧ B)
∧-IsProp = ×-IsProp

_∨_ : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A ∨ B = ∥ A ⊎ B ∥

∨-IsProp : {A : Type ℓ} {B : Type ℓ'} → IsProp (A ∨ B)
∨-IsProp = ∥∥-IsProp

⊤-rec : {A : Type ℓ} → A → (⊤ → A)
⊤-rec a tt = a

⊤-ind : {B : ⊤ → Type ℓ} → B tt → Π ⊤ B
⊤-ind b tt = b

⊤-IsSet : IsSet ⊤
⊤-IsSet = IsProp→IsSet ⊤-IsProp

⊥-IsSet : IsSet ⊥
⊥-IsSet = IsProp→IsSet ⊥-IsProp

-- Rearranged version of ∥∥-rec
with-∥∥ : {A : Type ℓ} {P : Type ℓ'} → ∥ P ∥ → IsProp A → (P → A) → A
with-∥∥ p A-IsProp f = ∥∥-rec A-IsProp f p
