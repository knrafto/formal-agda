{-# OPTIONS --cubical #-}
module Math.Function where

open import Cubical.Core.Glue public using () renaming (isEquiv to IsEquiv)
open import Cubical.Foundations.Embedding public using () renaming (isEmbedding to IsEmbedding; isEmbedding→hasPropFibers to IsEmbedding→fiber-IsProp; injEmbedding to IsInjective→IsEmbedding)
open import Cubical.Foundations.Equiv public using (fiber)
-- TODO: rename (maybe export in Math.Type)?
open import Cubical.Foundations.HLevels using (inhProp→isContr)


open import Math.Type

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ'
    C : Type ℓ''

IsInjective : (f : A → B) → Type _
IsInjective {A = A} f = {a₁ a₂ : A} → f a₁ ≡ f a₂ → a₁ ≡ a₂

-- TODO: Truncate to make a proposition.
-- TODO: make b implicit?
IsSurjective : (f : A → B) → Type _
IsSurjective {B = B} f = (b : B) → fiber f b

IsEmbedding×IsSurjective→IsEquiv : {f : A → B} → IsEmbedding f → IsSurjective f → IsEquiv f
IsEmbedding×IsSurjective→IsEquiv f-IsEmbedding f-IsSurjective = record { equiv-proof = λ b → inhProp→isContr (f-IsSurjective b) (IsEmbedding→fiber-IsProp f-IsEmbedding b) }

IsInjective×IsSurjective→IsEquiv : {f : A → B} → IsSet A → IsSet B → IsInjective f → IsSurjective f → IsEquiv f
IsInjective×IsSurjective→IsEquiv A-IsSet B-IsSet f-IsInjective f-IsSurjective
  = IsEmbedding×IsSurjective→IsEquiv (IsInjective→IsEmbedding A-IsSet B-IsSet f-IsInjective) f-IsSurjective
