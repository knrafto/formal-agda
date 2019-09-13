{-# OPTIONS --cubical #-}
module Math.Function where

open import Cubical.Core.Everything public using () renaming (isEquiv to IsEquiv)
open import Cubical.Foundations.Embedding public using () renaming (isEmbedding to IsEmbedding; isEmbedding→hasPropFibers to IsEmbedding→fiber-IsProp; injEmbedding to IsInjective→IsEmbedding)
open import Cubical.Foundations.Equiv public using (fiber)
open import Cubical.Foundations.Equiv using (idEquiv; isoToEquiv; invEquiv; compEquiv)
open import Cubical.Foundations.Function public using (_∘_)
-- TODO: rename (maybe export in Math.Type)?
open import Cubical.Foundations.HLevels using (inhProp→isContr)
open import Cubical.Foundations.HAEquiv using (isHAEquiv; equiv→HAEquiv)
open import Cubical.Foundations.Isomorphism using (iso)

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

HasInverse→IsEquiv : {f : A → B} (g : B → A) → ((a : A) → g (f a) ≡ a) → ((b : B) → f (g b) ≡ b) → IsEquiv f
HasInverse→IsEquiv {f = f} g g-f f-g = snd (isoToEquiv (iso f g f-g g-f))

id : A → A
id a = a

id-IsEquiv : {A : Type ℓ} → IsEquiv (id {A = A})
id-IsEquiv {A = A} = snd (idEquiv A)

inv : {f : A → B} → IsEquiv f → (B → A)
inv {f = f} f-IsEquiv = isHAEquiv.g (snd (equiv→HAEquiv (f , f-IsEquiv)))

leftInv : {f : A → B} (f-IsEquiv : IsEquiv f) → (a : A) → inv f-IsEquiv (f a) ≡ a
leftInv {f = f} f-IsEquiv = isHAEquiv.sec (snd (equiv→HAEquiv (f , f-IsEquiv)))

rightInv : {f : A → B} (f-IsEquiv : IsEquiv f) → (b : B) → f (inv f-IsEquiv b) ≡ b
rightInv {f = f} f-IsEquiv = isHAEquiv.ret (snd (equiv→HAEquiv (f , f-IsEquiv)))

inv-IsEquiv : {f : A → B} (f-IsEquiv : IsEquiv f) → IsEquiv (inv f-IsEquiv)
inv-IsEquiv {f = f} f-IsEquiv = snd (invEquiv (f , f-IsEquiv))

infixr 9 _∘-IsEquiv_

_∘-IsEquiv_ : {g : B → C} {f : A → B} → IsEquiv g → IsEquiv f → IsEquiv (g ∘ f)
_∘-IsEquiv_ {g = g} {f = f} g-IsEquiv f-IsEquiv = snd (compEquiv (f , f-IsEquiv) (g , g-IsEquiv))

⊥-elim-IsEquiv : {A : Type ℓ} → ¬ A → IsEquiv (⊥-elim {A = A})
⊥-elim-IsEquiv {A = A} ¬A = HasInverse→IsEquiv ¬A ⊥-elim-leftInv ⊥-elim-rightInv
  where
  ⊥-elim-leftInv : (a : ⊥) → ¬A (⊥-elim a) ≡ a
  ⊥-elim-leftInv ()

  ⊥-elim-rightInv : (a : A) → ⊥-elim (¬A a) ≡ a
  ⊥-elim-rightInv a = ⊥-elim (¬A a)

¬-IsEquiv : {A : Type ℓ} (¬A : ¬ A) → IsEquiv ¬A
¬-IsEquiv {A = A} ¬A = HasInverse→IsEquiv ⊥-elim ¬-leftInv ¬-rightInv
  where
  ¬-leftInv : (a : A) → ⊥-elim (¬A a) ≡ a
  ¬-leftInv a = ⊥-elim (¬A a)

  ¬-rightInv : (b : ⊥) → ¬A (⊥-elim b) ≡ b
  ¬-rightInv b = ⊥-elim b
