{-# OPTIONS --cubical --allow-unsolved-metas #-}
module Math.Finite where

open import Math.Dec
open import Math.Fin
open import Math.Function
open import Math.Id
open import Math.Nat
open import Math.Type

IsFinite : Type₀ → Type₁
IsFinite A = Σ[ n ∈ ℕ ] ∥ Fin n ≡ A ∥

card : ∀ {A : Type₀} → IsFinite A → ℕ
card = fst

Fin-IsInjective : ∀ {m n} → Fin m ≡ Fin n → m ≡ n
Fin-IsInjective {zero} {zero} _ = refl
Fin-IsInjective {zero} {suc n} Fin0≡Finsn = ⊥-rec (¬Fin0 (transport (sym Fin0≡Finsn) fzero))
Fin-IsInjective {suc m} {zero} Finsm≡Fin0 = ⊥-rec (¬Fin0 (transport Finsm≡Fin0 fzero))
Fin-IsInjective {suc m} {suc n} Finsm≡Finsn = ap suc (Fin-IsInjective (ua f (HasInverse→IsEquiv g g-f f-g)))
  where
  f : Fin m → Fin n
  f = {!!}

  g : Fin n → Fin m
  g = {!!}

  g-f : (a : Fin m) → g (f a) ≡ a
  g-f = {!!}

  f-g : (b : Fin n) → f (g b) ≡ b
  f-g = {!!}

IsFinite-IsProp : ∀ {A : Type₀} → IsProp (IsFinite A)
IsFinite-IsProp (m , |Finm≡A|) (n , |Finn≡A|) = ΣProp≡ (λ _ → ∥∥-IsProp) m≡n
  where
  m≡n : m ≡ n
  m≡n =
    with-∥∥ |Finm≡A| (ℕ-IsSet _ _) λ Finm≡A →
    with-∥∥ |Finn≡A| (ℕ-IsSet _ _) λ Finn≡A →
    Fin-IsInjective (Finm≡A ∙ sym Finn≡A)

IsFinite→IsSet : ∀ {A : Type₀} → IsFinite A → IsSet A
IsFinite→IsSet (n , |Finm≡A|) = with-∥∥ |Finm≡A| IsSet-IsProp λ Finm≡A →
  subst IsSet Finm≡A Fin-IsSet

IsFinite-∀-Dec : ∀ {ℓ} {A : Type₀} {P : A → Type ℓ} → IsFinite A → (∀ a → IsProp (P a)) → (∀ a → Dec (P a)) → Dec (∀ a → P a)
IsFinite-∀-Dec {P = P} (n , |Finn≡A|) P-IsProp P-Dec = with-∥∥ |Finn≡A| (Dec-IsProp (Π-IsProp P-IsProp)) λ Finn≡A → lemma Finn≡A P P-Dec
  where
  lemma : ∀ {ℓ} {n} {A : Type₀} → Fin n ≡ A → (P : A → Type ℓ) → (∀ a → Dec (P a)) → Dec (∀ a → P a)
  lemma {ℓ} = pathInd (λ A p → (P : A → Type ℓ) → ((a : A) → Dec (P a)) → Dec (∀ a → P a)) λ P → Fin-∀-Dec {P = P}

IsFinite-∃-Dec : ∀ {ℓ} {A : Type₀} {P : A → Type ℓ} → IsFinite A → (∀ a → Dec (P a)) → Dec ∥ Σ[ a ∈ A ] P a ∥
IsFinite-∃-Dec {P = P} (n , |Finn≡A|) P-Dec = with-∥∥ |Finn≡A| (Dec-IsProp ∥∥-IsProp) λ Finn≡A → lemma Finn≡A P P-Dec
  where
  lemma : ∀ {ℓ} {n} {A : Type₀} → Fin n ≡ A → (P : A → Type ℓ) → (∀ a → Dec (P a)) → Dec ∥ Σ[ a ∈ A ] P a ∥
  lemma {ℓ} = pathInd (λ A p → (P : A → Type ℓ) → ((a : A) → Dec (P a)) → Dec ∥ Σ[ a ∈ A ] P a ∥) λ P → Fin-∃-Dec {P = P}
