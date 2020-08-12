{-# OPTIONS --cubical #-}
module Math.Fin where

open import Cubical.Data.Fin public using (Fin; toℕ; fzero; fsuc; ¬Fin0; fsplit) renaming (toℕ-injective to toℕ-IsInjective; isSetFin to Fin-IsSet)

open import Math.Dec
open import Math.Function
open import Math.Nat
open import Math.Prod
open import Math.Sum
open import Math.Type

private
  variable
    ℓ : Level

Fin1-IsContr : IsContr (Fin 1)
Fin1-IsContr = fzero , λ { (zero , _) → toℕ-IsInjective refl ; (suc n , p) → contradiction (suc-reflects-< p) ¬-<-zero }

¬fzero≡fsuc : {n : ℕ} {i : Fin n} → ¬ fzero ≡ fsuc i
¬fzero≡fsuc p = ¬zero≡suc (ap toℕ p)

Fin-≡-Dec : ∀ {n} → (i j : Fin n) → Dec (i ≡ j)
Fin-≡-Dec i j with ℕ-≡-Dec (toℕ i) (toℕ j)
Fin-≡-Dec i j | yes toℕi≡toℕj = yes (toℕ-IsInjective toℕi≡toℕj)
Fin-≡-Dec i j | no ¬toℕi≡toℕj = no λ i≡j → ¬toℕi≡toℕj (ap toℕ i≡j)

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
Fin-* {zero} {n} = ⊥-rec ∘ fst ∘ ×-map ¬Fin0 id
Fin-* {suc m} {n} = Fin-+ ∘ ⊎-map snd Fin-* ∘ ⊎-distribute ∘ ×-map (inv Fin-suc-IsEquiv) id

Fin-*-IsEquiv : {m n : ℕ} → IsEquiv (Fin-* {m = m} {n = n})
-- TODO: rewrite: any function between empty types is an equivalence
Fin-*-IsEquiv {zero} {n} = ⊥-rec-IsEquiv ¬Fin0 ∘-IsEquiv (¬-IsEquiv fst) ∘-IsEquiv ×-map-IsEquiv (¬-IsEquiv ¬Fin0) id-IsEquiv
Fin-*-IsEquiv {suc m} {n} =
  Fin-+-IsEquiv ∘-IsEquiv
  ⊎-map-IsEquiv ⊤-snd-IsEquiv Fin-*-IsEquiv ∘-IsEquiv
  ⊎-distribute-IsEquiv ∘-IsEquiv
  ×-map-IsEquiv (inv-IsEquiv Fin-suc-IsEquiv) id-IsEquiv

Fin-∀-Dec : {n : ℕ} {P : Fin n → Type ℓ} → (∀ i → Dec (P i)) → Dec (∀ i → P i)
Fin-∀-Dec {n = zero}  {P} P-Dec = yes λ i → ⊥-rec (¬Fin0 i)
Fin-∀-Dec {n = suc k} {P} P-Dec with P-Dec fzero | Fin-∀-Dec (λ i → P-Dec (fsuc i))
... | yes P-fzero | yes P-rest = yes λ i → case fsplit i return P i of λ
    { (inl fzero≡i) → subst P fzero≡i P-fzero
    ; (inr (i' , fsuci'≡i)) → subst P fsuci'≡i (P-rest i')
    }
... | yes P-fzero | no ¬P-rest = no λ f → ¬P-rest λ i → f (fsuc i)
... | no ¬P-fzero | _ = no λ f → ¬P-fzero (f fzero)

Fin-∃-Dec : ∀ {ℓ} {n} {P : Fin n → Type ℓ} → (∀ i → Dec (P i)) → Dec ∥ Σ[ i ∈ Fin n ] P i ∥
Fin-∃-Dec {n = zero}  {P} P-Dec = no (∥∥-rec ⊥-IsProp λ { (i , _) → ¬Fin0 i })
Fin-∃-Dec {n = suc k} {P} P-Dec with P-Dec fzero | Fin-∃-Dec (λ i → P-Dec (fsuc i))
... | yes P-fzero | _          = yes ∣ fzero , P-fzero ∣
... | no ¬P-fzero | yes P-rest = with-∥∥ P-rest (Dec-IsProp ∥∥-IsProp) λ { (i , P-fsuci) → yes ∣ fsuc i , P-fsuci ∣ }
... | no ¬P-fzero | no ¬P-rest = no (∥∥-rec ⊥-IsProp λ { (i , P-i) → case fsplit i of λ
    { (inl fzero≡i) → ¬P-fzero (subst P (sym fzero≡i) P-i)
    ; (inr (i' , fsuci'≡i)) → ¬P-rest ∣ i' , subst P (sym fsuci'≡i) P-i ∣
    } })

