{-# OPTIONS --cubical #-}
module Math.Function where

open import Cubical.Core.Everything public using () renaming (isEquiv to IsEquiv)
open import Cubical.Foundations.Equiv public using (fiber)
open import Cubical.Foundations.Equiv using (idEquiv; invEquiv; compEquiv)
open import Cubical.Foundations.Equiv.HalfAdjoint using (isHAEquiv; equiv→HAEquiv)
-- TODO: rename (maybe export in Math.Type)?
open import Cubical.Foundations.HLevels using (inhProp→isContr)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv)
open import Cubical.Foundations.Prelude public using (funExt)
open import Cubical.Foundations.Univalence using () renaming (ua to uaPrim)
open import Cubical.Functions.Embedding public using () renaming (isEmbedding to IsEmbedding; isEmbedding→hasPropFibers to IsEmbedding→fiber-IsProp; injEmbedding to IsInjective→IsEmbedding; hasPropFibers→isEmbedding to fiber-IsProp→IsEmbedding)

open import Math.Type

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ'
    C : Type ℓ''

ua : {A B : Type ℓ} {f : A → B} → IsEquiv f → A ≡ B
ua {f = f} f-IsEquiv = uaPrim (f , f-IsEquiv)

IsInjective : (f : A → B) → Type _
IsInjective {A = A} f = {a₁ a₂ : A} → f a₁ ≡ f a₂ → a₁ ≡ a₂

IsInjective→fiber-IsProp : {A B : Type ℓ} {f : A → B} → IsSet A → IsSet B → IsInjective f → ∀ y → IsProp (fiber f y)
IsInjective→fiber-IsProp A-IsSet B-IsSet f-IsInjective = IsEmbedding→fiber-IsProp (IsInjective→IsEmbedding A-IsSet B-IsSet f-IsInjective)

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

IsEquiv→fiber-IsContr : {f : A → B} → IsEquiv f → ((b : B) → IsContr (fiber f b))
IsEquiv→fiber-IsContr = IsEquiv.equiv-proof

IsEquiv→IsEmbedding : {f : A → B} → IsEquiv f → IsEmbedding f
IsEquiv→IsEmbedding f-IsEquiv = fiber-IsProp→IsEmbedding λ b → IsContr→IsProp (IsEquiv→fiber-IsContr f-IsEquiv b)

id : A → A
id a = a

infixr 9 _∘_

_∘_ : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g (f x)

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

infixr 9 _∘-IsEmbedding_

_∘-IsEmbedding_ : {g : B → C} {f : A → B} → IsEmbedding g → IsEmbedding f → IsEmbedding (g ∘ f)
_∘-IsEmbedding_ {g = g} {f = f} g-IsEmbedding f-IsEmbedding _ _ = (g-IsEmbedding _ _) ∘-IsEquiv (f-IsEmbedding _ _)

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

⊤-elim-IsEmbedding : {A : Type ℓ} → IsSet A → {a : A} → IsEmbedding (⊤-elim a)
⊤-elim-IsEmbedding A-IsSet _ _ = HasInverse→IsEquiv (λ _ → ⊤-IsProp _ _) (λ _ → IsProp→IsSet ⊤-IsProp _ _ _ _) (λ _ → A-IsSet _ _ _ _)

∘f-IsEquiv : {C : Type ℓ''} {f : A → B} → IsEquiv f → IsEquiv (_∘ f)
∘f-IsEquiv {A = A} {B = B} {C = C} {f = f} f-IsEquiv = HasInverse→IsEquiv ∘f-inv ∘f-inv-∘f ∘f-∘f-inv
  where
  ∘f-inv : (A → C) → (B → C)
  ∘f-inv = _∘ inv f-IsEquiv

  ∘f-inv-∘f : (g : B → C) → g ∘ f ∘ inv f-IsEquiv ≡ g
  ∘f-inv-∘f g = funExt λ x → ap g (rightInv f-IsEquiv x)

  ∘f-∘f-inv : (g : A → C) → g ∘ inv f-IsEquiv ∘ f ≡ g
  ∘f-∘f-inv g = funExt λ x → ap g (leftInv f-IsEquiv x)

f∘-IsEquiv : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {f : B → C} → IsEquiv f → IsEquiv (f ∘_)
f∘-IsEquiv {A = A} {B = B} {C = C} {f = f} f-IsEquiv = HasInverse→IsEquiv f∘-inv f∘-inv-f∘ f∘-f∘-inv
  where
  f∘-inv : (A → C) → (A → B)
  f∘-inv = inv f-IsEquiv ∘_

  f∘-inv-f∘ : (g : A → B) → inv f-IsEquiv ∘ f ∘ g ≡ g
  f∘-inv-f∘ g = funExt λ x → leftInv f-IsEquiv (g x)

  f∘-f∘-inv : (g : A → C) → f ∘ inv f-IsEquiv ∘ g ≡ g
  f∘-f∘-inv g = funExt λ x → rightInv f-IsEquiv (g x) 

const : A → (B → A)
const a = λ _ → a

const-IsEquiv : IsContr B → IsEquiv (const {A = A} {B = B})
const-IsEquiv B-IsContr = HasInverse→IsEquiv (λ f → f (the B-IsContr)) (λ _ → refl) (λ g → funExt λ b → ap g (the≡ B-IsContr))

IsContr→IsContr→IsEquiv : {A : Type ℓ} {B : Type ℓ'} {f : A → B} → IsContr A → IsContr B → IsEquiv f
IsContr→IsContr→IsEquiv {f = f} A-IsContr B-IsContr = HasInverse→IsEquiv
  (λ _ → the A-IsContr)
  (λ a → IsContr→IsProp A-IsContr _ _)
  (λ b → IsContr→IsProp B-IsContr _ _)
