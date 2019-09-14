{-# OPTIONS --cubical #-}
module Math.List where

open import Math.Fin
open import Math.Nat
open import Math.Type
open import Math.Vec

private
  variable
    ℓ : Level

List : Type ℓ → Type ℓ
List A = Σ[ n ∈ ℕ ] Vec n A

length : {A : Type ℓ} → List A → ℕ 
length = fst

-- TODO: rename?
index : {A : Type ℓ} (l : List A) → Fin (length l) → A
index = snd

[] : {A : Type ℓ} → List A
[] = (zero , 0-vector)

infixr 5 _∷_

_∷_ : {A : Type ℓ} → A → List A → List A
a ∷ (n , v) = suc n , cons (a , v)
