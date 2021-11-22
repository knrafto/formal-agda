module Math.List where

open import Math.Fin
open import Math.Function
open import Math.Id
open import Math.Nat
open import Math.Prod
open import Math.Type
open import Math.Vec

private
  variable
    ℓ : Level

data List (A : Type ℓ) : Type ℓ where
  [] : List A
  -- TODO: rename to just cons?
  List-cons : A × List A → List A

infixr 5 _∷_

_∷_ : {A : Type ℓ} → A → List A → List A
a ∷ l = List-cons (a , l)

[]-IsEmbedding : {A : Type ℓ} → IsEmbedding {B = List A} (⊤-rec [])
[]-IsEmbedding {A = A} a₀ x₀ = decode-IsEquiv []
  where
  Code : List A → Type _
  Code [] = a₀ ≡ tt
  Code (List-cons _) = Lift ⊥

  encode : (x : List A) → [] ≡ x → Code x
  encode x p = subst Code p refl

  decode : (x : List A) → Code x → [] ≡ x
  decode [] p = ap (⊤-rec []) p

  decode-encode : (x : List A) (p : [] ≡ x) → decode x (encode x p) ≡ p
  decode-encode _ = pathInd (λ x p → decode x (encode x p) ≡ p) (ap {y = refl} (decode []) (subst-refl Code))

  encode-decode : (x : List A) (p : Code x) → encode x (decode x p) ≡ p
  encode-decode [] p = refl

  decode-IsEquiv : (x : List A) → IsEquiv (decode x)
  decode-IsEquiv x = HasInverse→IsEquiv (encode x) (encode-decode x) (decode-encode x)

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
List-singleton a = List-cons (a , [])

List-singleton-IsEmbedding : {A : Type ℓ} → IsEmbedding (List-singleton {A = A})
List-singleton-IsEmbedding =
  List-cons-IsEmbedding ∘-IsEmbedding
  ×-map-IsEmbedding (IsEquiv→IsEmbedding id-IsEquiv) []-IsEmbedding ∘-IsEmbedding
  IsEquiv→IsEmbedding (inv-IsEquiv ⊤-fst-IsEquiv)

length : {A : Type ℓ} → List A → ℕ
length [] = zero
length (List-cons (x , xs)) = suc (length xs)

Index : {A : Type ℓ} → List A → Type₀
Index xs = Fin (length xs)

_[_] : {A : Type ℓ} → (xs : List A) → Index xs → A
[] [ i ] = ⊥-rec (¬Fin0 i)
List-cons (x , xs) [ i ] = case fsplit i of λ
  { (inl _) → x
  ; (inr (i' , _)) → xs [ i' ]
  }
