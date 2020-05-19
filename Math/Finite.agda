{-# OPTIONS --cubical #-}
module Math.Finite where

open import Math.Dec
open import Math.Fin
open import Math.Function
open import Math.Id
open import Math.Type

IsFinite : Type₀ → Type₁
IsFinite A = ∥ Σ[ n ∈ ℕ ] Fin n ≡ A ∥

IsFinite-IsProp : ∀ {A : Type₀} → IsProp (IsFinite A)
IsFinite-IsProp = ∥∥-IsProp

IsFinite-∀-Dec : ∀ {ℓ} {A : Type₀} {P : A → Type ℓ} → IsFinite A → (∀ a → IsProp (P a)) → (∀ a → Dec (P a)) → Dec (∀ a → P a)
IsFinite-∀-Dec {P = P} A-IsFinite P-IsProp P-Dec = with-∥∥ A-IsFinite (Dec-IsProp (Π-IsProp P-IsProp)) λ { (n , Finn≡A) → lemma Finn≡A P P-Dec }
  where
  lemma : ∀ {ℓ} {n} {A : Type₀} → Fin n ≡ A → (P : A → Type ℓ) → (∀ a → Dec (P a)) → Dec (∀ a → P a)
  lemma {ℓ} = pathInd (λ A p → (P : A → Type ℓ) → ((a : A) → Dec (P a)) → Dec (∀ a → P a)) λ P → Fin-∀-Dec {P = P}

IsFinite-∃-Dec : ∀ {ℓ} {A : Type₀} {P : A → Type ℓ} → IsFinite A → (∀ a → Dec (P a)) → Dec ∥ Σ[ a ∈ A ] P a ∥
IsFinite-∃-Dec {P = P} A-IsFinite P-Dec = with-∥∥ A-IsFinite (Dec-IsProp ∥∥-IsProp) λ { (n , Finn≡A) → lemma Finn≡A P P-Dec }
  where
  lemma : ∀ {ℓ} {n} {A : Type₀} → Fin n ≡ A → (P : A → Type ℓ) → (∀ a → Dec (P a)) → Dec ∥ Σ[ a ∈ A ] P a ∥
  lemma {ℓ} = pathInd (λ A p → (P : A → Type ℓ) → ((a : A) → Dec (P a)) → Dec ∥ Σ[ a ∈ A ] P a ∥) λ P → Fin-∃-Dec {P = P}
