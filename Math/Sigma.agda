{-# OPTIONS --cubical #-}
module Math.Sigma where

open import Math.Id
open import Math.Function
open import Math.Type

Σ-map-snd :
  ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : A → Type ℓ''} →
  (∀ a → B a → C a) → Σ A B → Σ A C
Σ-map-snd f (a , b) = a , f a b

Σ-map-snd-IsEquiv :
  ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : A → Type ℓ''} {f : ∀ a → B a → C a} →
  (∀ a → IsEquiv (f a)) → IsEquiv (Σ-map-snd f)
Σ-map-snd-IsEquiv {B = B} {C = C} f-IsEquiv = HasInverse→IsEquiv
  (Σ-map-snd (λ a → inv (f-IsEquiv a)))
  (λ (a , b) → Σ≡ refl (subst-refl B ∙ leftInv  (f-IsEquiv a) b))
  (λ (a , c) → Σ≡ refl (subst-refl C ∙ rightInv (f-IsEquiv a) c))
