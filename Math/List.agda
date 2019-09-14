{-# OPTIONS --cubical #-}
module Math.List where

open import Math.Fin
open import Math.Nat
open import Math.Type
open import Math.Vec

private
  variable
    ℓ : Level

infixr 5 _∷_

data List (A : Type ℓ) : Type ℓ where
  [] : List A
  _∷_ : A → List A → List A

List-cons : {A : Type ℓ} → A × List A → List A
List-cons (a , l) = a ∷ l

List-singleton : {A : Type ℓ} → A → List A
List-singleton a = a ∷ []
