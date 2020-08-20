{-# OPTIONS --cubical #-}
module Math.Dec where

open import Cubical.Relation.Nullary public using (Dec; yes; no) renaming (isPropDec to Dec-IsProp)
open import Math.Type

HasDecEq : ∀ {ℓ} (A : Type ℓ) → Type ℓ
HasDecEq A = (a b : A) → Dec (a ≡ b)

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
