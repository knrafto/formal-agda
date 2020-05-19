{-# OPTIONS --cubical #-}
module Math.Dec where

open import Cubical.Relation.Nullary public using (Dec; yes; no) renaming (isPropDec to Dec-IsProp)
open import Math.Type

×-Dec : ∀ {ℓ} {A B : Type ℓ} → Dec A → Dec B → Dec (A × B)
×-Dec (yes a) (yes b) = yes (a , b)
×-Dec (yes a) (no ¬b) = no λ { (a , b) → ¬b b }
×-Dec (no ¬a) _       = no λ { (a , b) → ¬a a }
