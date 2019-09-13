{-# OPTIONS --cubical #-}
module Math.Fin where

open import Cubical.Data.Fin public using (Fin; toℕ; fzero; fsuc; ¬Fin0) renaming (toℕ-injective to toℕ-IsInjective; isSetFin to Fin-IsSet)

open import Math.Function
open import Math.Nat
open import Math.Prod
open import Math.Sum
open import Math.Type

private
  variable
    ℓ : Level

¬fzero≡fsuc : {n : ℕ} {i : Fin n} → ¬ fzero ≡ fsuc i
¬fzero≡fsuc p = ¬zero≡suc (ap toℕ p)

fsuc-IsInjective : {n : ℕ} → IsInjective (fsuc {k = n})
fsuc-IsInjective p = toℕ-IsInjective (suc-IsInjective (ap toℕ p))

-- TODO: better name?
Fin-suc : {n : ℕ} → ⊤ ⊎ Fin n → Fin (suc n)
Fin-suc (inl _) = fzero
Fin-suc (inr n) = fsuc n

Fin-suc-IsInjective : {n : ℕ} → IsInjective (Fin-suc {n = n})
Fin-suc-IsInjective {a₁ = inl tt} {a₂ = inl tt} p = refl
Fin-suc-IsInjective {a₁ = inl tt} {a₂ = inr n₂} p = contradiction p ¬fzero≡fsuc
Fin-suc-IsInjective {a₁ = inr n₁} {a₂ = inl tt} p = contradiction (sym p) ¬fzero≡fsuc
Fin-suc-IsInjective {a₁ = inr n₁} {a₂ = inr n₂} p = ap inr (fsuc-IsInjective p)

Fin-suc-IsSurjective : {n : ℕ} → IsSurjective (Fin-suc {n = n})
Fin-suc-IsSurjective (zero , _) = inl tt , toℕ-IsInjective refl
Fin-suc-IsSurjective (suc i , si<sn) = inr (i , suc-reflects-< si<sn) , toℕ-IsInjective refl

Fin-suc-IsEquiv : {n : ℕ} → IsEquiv (Fin-suc {n = n})
Fin-suc-IsEquiv = IsInjective×IsSurjective→IsEquiv (⊎-IsSet ⊤-IsSet Fin-IsSet) Fin-IsSet Fin-suc-IsInjective Fin-suc-IsSurjective

-- TODO: better name?
Fin-+ : {m n : ℕ} → Fin m ⊎ Fin n → Fin (m + n)
Fin-+ {zero} {n} = inv ⊥-inr-IsEquiv ∘ ⊎-map ¬Fin0 id
Fin-+ {suc m} {n} = Fin-suc ∘ ⊎-map id Fin-+ ∘ ⊎-assoc ∘ ⊎-map (inv Fin-suc-IsEquiv) id

Fin-+-IsEquiv : {m n : ℕ} → IsEquiv (Fin-+ {m = m} {n = n})
Fin-+-IsEquiv {zero} {n} = inv-IsEquiv ⊥-inr-IsEquiv ∘-IsEquiv (⊎-map-IsEquiv (¬-IsEquiv ¬Fin0) id-IsEquiv)
Fin-+-IsEquiv {suc m} {n} =
  Fin-suc-IsEquiv ∘-IsEquiv
  ⊎-map-IsEquiv id-IsEquiv Fin-+-IsEquiv ∘-IsEquiv
  ⊎-assoc-IsEquiv ∘-IsEquiv
  ⊎-map-IsEquiv (inv-IsEquiv Fin-suc-IsEquiv) id-IsEquiv

-- TODO: better name?
Fin-* : {m n : ℕ} → Fin m × Fin n → Fin (m * n)
Fin-* {zero} {n} = ⊥-elim ∘ fst ∘ ×-map ¬Fin0 id
Fin-* {suc m} {n} = Fin-+ ∘ ⊎-map snd Fin-* ∘ ⊎-distribute ∘ ×-map (inv Fin-suc-IsEquiv) id

Fin-*-IsEquiv : {m n : ℕ} → IsEquiv (Fin-* {m = m} {n = n})
Fin-*-IsEquiv {zero} {n} = ⊥-elim-IsEquiv ¬Fin0 ∘-IsEquiv (¬-IsEquiv fst) ∘-IsEquiv ×-map-IsEquiv (¬-IsEquiv ¬Fin0) id-IsEquiv 
Fin-*-IsEquiv {suc m} {n} = 
  Fin-+-IsEquiv ∘-IsEquiv
  ⊎-map-IsEquiv ⊤-snd-IsEquiv Fin-*-IsEquiv ∘-IsEquiv
  ⊎-distribute-IsEquiv ∘-IsEquiv
  ×-map-IsEquiv (inv-IsEquiv Fin-suc-IsEquiv) id-IsEquiv
