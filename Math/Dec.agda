module Math.Dec where

open import Cubical.Relation.Nullary public using (Dec; yes; no) renaming (isPropDec to Dec-IsProp; Discrete to HasDecEq)
open import Cubical.Data.Sigma.Properties public using () renaming (discreteΣ to Σ-HasDecEq)
open import Math.Type

if_then_else_ : ∀ {ℓ ℓ'} {P : Type ℓ} {A : Type ℓ'} → Dec P → A → A → A
if (yes p) then t else f = t
if (no ¬p) then t else f = f

¬-Dec : ∀ {ℓ} {A : Type ℓ} → Dec A → Dec (¬ A)
¬-Dec (yes p) = no λ ¬p → ¬p p
¬-Dec (no ¬p) = yes ¬p

×-Dec : ∀ {ℓ} {A B : Type ℓ} → Dec A → Dec B → Dec (A × B)
×-Dec (yes a) (yes b) = yes (a , b)
×-Dec (yes a) (no ¬b) = no λ { (a , b) → ¬b b }
×-Dec (no ¬a) _       = no λ { (a , b) → ¬a a }

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
