module Math.Dec where

open import Cubical.Relation.Nullary public using (Dec; yes; no) renaming (isPropDec to Dec-IsProp; Discrete to HasDecEq)

open import Math.Sum
open import Math.Function
open import Math.Type

if_then_else_ : ∀ {ℓ ℓ'} {P : Type ℓ} {A : Type ℓ'} → Dec P → A → A → A
if (yes p) then t else f = t
if (no ¬p) then t else f = f

⊤-Dec : Dec ⊤
⊤-Dec = yes tt

⊥-Dec : Dec ⊥
⊥-Dec = no λ p → p

¬-Dec : ∀ {ℓ} {A : Type ℓ} → Dec A → Dec (¬ A)
¬-Dec (yes p) = no λ ¬p → ¬p p
¬-Dec (no ¬p) = yes ¬p

Σ-Dec : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} → IsProp A → Dec A → (∀ a → Dec (B a)) → Dec (Σ A B)
Σ-Dec {B = B} A-IsProp (yes a) B-Dec with B-Dec a
... | yes b = yes (a , b)
... | no ¬b = no λ { (a , b) → ¬b (subst B (A-IsProp _ _) b) }
Σ-Dec A-IsProp (no ¬a) B-Dec = no λ { (a , b) → ¬a a }

×-Dec : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → Dec A → Dec B → Dec (A × B)
×-Dec (yes a) (yes b) = yes (a , b)
×-Dec (yes a) (no ¬b) = no λ { (a , b) → ¬b b }
×-Dec (no ¬a) _       = no λ { (a , b) → ¬a a }

∧-Dec : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → Dec A → Dec B → Dec (A ∧ B)
∧-Dec = ×-Dec

∨-Dec : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → Dec A → Dec B → Dec (A ∨ B)
∨-Dec (yes a) _ = yes ∣ inl a ∣
∨-Dec (no ¬a) (yes b) = yes ∣ inr b ∣
∨-Dec (no ¬a) (no ¬b) = no (∥∥-rec ⊥-IsProp λ { (inl a) → ¬a a; (inr b) → ¬b b })

IsProp→HasDecEq : ∀ {ℓ} {A : Type ℓ} → IsProp A → HasDecEq A
IsProp→HasDecEq A-IsProp a b = yes (A-IsProp a b)

⊥-HasDecEq : HasDecEq ⊥
⊥-HasDecEq = IsProp→HasDecEq ⊥-IsProp

⊤-HasDecEq : HasDecEq ⊤
⊤-HasDecEq = IsProp→HasDecEq ⊤-IsProp

⊎-HasDecEq : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → HasDecEq A → HasDecEq B → HasDecEq (A ⊎ B)
⊎-HasDecEq A-HasDecEq B-HasDecEq (inl a₁) (inl a₂) = case (A-HasDecEq a₁ a₂) of λ
  { (yes p) → yes (ap inl p)
  ; (no ¬p) → no (λ q → ¬p (IsEmbedding→IsInjective inl-IsEmbedding q))
  }
⊎-HasDecEq A-HasDecEq B-HasDecEq (inr b₁) (inr b₂) = case (B-HasDecEq b₁ b₂) of λ
  { (yes p) → yes (ap inr p)
  ; (no ¬p) → no λ q → ¬p (IsEmbedding→IsInjective inr-IsEmbedding q)
  }
⊎-HasDecEq A-HasDecEq B-HasDecEq (inl a) (inr b) = no λ p → ¬inl≡inr p
⊎-HasDecEq A-HasDecEq B-HasDecEq (inr b) (inl a) = no λ p → ¬inl≡inr (sym p)

-- Can be used as an implicit argument for compile time checking
True : ∀ {ℓ} {A : Type ℓ} → Dec A → Type₀
True (yes a) = ⊤
True (no ¬a) = ⊥

witness : ∀ {ℓ} {A : Type ℓ} {d : Dec A} → True d → A
witness {d = yes a} _ = a
witness {d = no ¬a} ()

-- If a decision procedure returns "yes", then we can extract the
-- proof using from-yes.

From-yes : ∀ {ℓ} {P : Type ℓ} → Dec P → Type ℓ
From-yes {P = P} (yes _) = P
From-yes {P = P} (no  _) = Lift ⊤

from-yes : ∀ {ℓ} {P : Set ℓ} → (p : Dec P) → From-yes p
from-yes (yes p) = p
from-yes (no  _) = _

-- If a decision procedure returns "no", then we can extract the proof
-- using from-no.

From-no : ∀ {ℓ} {P : Type ℓ} → Dec P → Type ℓ
From-no {P = P} (yes _) = Lift ⊤
From-no {P = P} (no  _) = ¬ P

from-no : ∀ {ℓ} {P : Type ℓ} → (p : Dec P) → From-no p
from-no (yes _) = _
from-no (no ¬p) = ¬p
