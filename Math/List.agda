{-# OPTIONS --cubical #-}
module Math.List where

open import Math.Fin
open import Math.Function
open import Math.Id
open import Math.Nat
open import Math.Type
open import Math.Vec

private
  variable
    ℓ : Level

data List (A : Type ℓ) : Type ℓ where
  [] : List A
  List-cons : A × List A → List A

infixr 5 _∷_

_∷_ : {A : Type ℓ} → A → List A → List A
a ∷ l = List-cons (a , l)

-- TODO: is there a shorter proof of this?
List-cons-IsEmbedding : {A : Type ℓ} → IsEmbedding (List-cons {A = A})
List-cons-IsEmbedding {A = A} a₀ x₀ = decode-IsEquiv (List-cons x₀)
  where
  Code : List A → Type _
  Code [] = Lift ⊥
  Code (List-cons a) = a₀ ≡ a

  encode : (x : List A) → List-cons a₀ ≡ x → Code x
  encode x p = subst Code p refl

  decode : (x : List A) → Code x → List-cons a₀ ≡ x
  decode (List-cons _) p = ap List-cons p

  decode-encode : (x : List A) (p : List-cons a₀ ≡ x) → decode x (encode x p) ≡ p
  decode-encode _ = pathInd (λ x p → decode x (encode x p) ≡ p) (ap (ap List-cons) (subst-refl Code))

  encode-decode : (x : List A) (p : Code x) → encode x (decode x p) ≡ p
  encode-decode (List-cons _) p = subst-a≡ ∙ refl-∙

  decode-IsEquiv : (x : List A) → IsEquiv (decode x)
  decode-IsEquiv x = HasInverse→IsEquiv (encode x) (encode-decode x) (decode-encode x)

List-singleton : {A : Type ℓ} → A → List A
List-singleton a = a ∷ []
