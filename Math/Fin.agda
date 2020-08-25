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

Fin-HasDecEq : ∀ {n} → HasDecEq (Fin n)
Fin-HasDecEq i j with ℕ-HasDecEq (toℕ i) (toℕ j)
Fin-HasDecEq i j | yes toℕi≡toℕj = yes (toℕ-IsInjective toℕi≡toℕj)
Fin-HasDecEq i j | no ¬toℕi≡toℕj = no λ i≡j → ¬toℕi≡toℕj (ap toℕ i≡j)

fsuc-IsInjective : {n : ℕ} → IsInjective (fsuc {k = n})
fsuc-IsInjective p = toℕ-IsInjective (suc-IsInjective (ap toℕ p))

¬fzero≡fsuc : {n : ℕ} {i : Fin n} → ¬ fzero ≡ fsuc i
¬fzero≡fsuc p = ¬zero≡suc (ap toℕ p)

-- TODO: name?
finj : ∀ {n : ℕ} → Fin n → Fin (suc n)
finj (i , i<n) = i , ≤-suc i<n

fmax : ∀ {n : ℕ} → Fin (suc n)
fmax {n} = (n , ≤-refl)

finj-IsInjective : {n : ℕ} → IsInjective (finj {n = n})
finj-IsInjective p = toℕ-IsInjective (ap toℕ p)

¬finj≡fmax : {n : ℕ} {i : Fin n} → ¬ finj i ≡ fmax
¬finj≡fmax {n} {(i , i<n)} p = <-irrefl (subst (_< n) (ap fst p) i<n)

inject : ∀ {m n} → Fin m → Fin (m + n)
inject {m} {n} (i , i<m) = i , <≤-trans i<m (n , +-comm n m)

inject-IsInjective : ∀ {m n} → IsInjective (inject {m = m} {n = n})
inject-IsInjective p = toℕ-IsInjective (ap toℕ p)

raise : ∀ {m n} → Fin n → Fin (m + n)
raise {m} {n} (j , j<n) = m + j , <-k+ j<n

raise-IsInjective : ∀ {m n} → IsInjective (raise {m = m} {n = n})
raise-IsInjective p = toℕ-IsInjective (m+-IsInjective (ap toℕ p))

¬inject≡raise : ∀ {m n} (i : Fin m) (j : Fin n) → ¬ inject i ≡ raise j
¬inject≡raise {m} {n} (i , i<m) (j , _) p = <-asym (subst (_< m) (ap toℕ p) i<m) (j , +-comm j m)

-- i ↦ n - i - 1
reflect : ∀ {n} → Fin n → Fin n
reflect (i , (k , k+suci≡n)) = k , (i , +-suc i k ∙ +-comm (suc i) k ∙ k+suci≡n)

reflect-toℕ : ∀ {n} (i : Fin n) → suc (toℕ (reflect i) + toℕ i) ≡ n
reflect-toℕ (i , (k , k+suci≡n)) = sym (+-suc k i) ∙ k+suci≡n

reflect-reflect : ∀ {n} (i : Fin n) → reflect (reflect i) ≡ i
reflect-reflect (i , _) = toℕ-IsInjective refl

reflect-IsEquiv : ∀ {n} → IsEquiv (reflect {n = n})
reflect-IsEquiv {n} = HasInverse→IsEquiv reflect reflect-reflect reflect-reflect

[fzero,fsuc] : {n : ℕ} → ⊤ ⊎ Fin n → Fin (suc n)
[fzero,fsuc] = pair (const fzero , fsuc)

[fzero,fsuc]-IsInjective : {n : ℕ} → IsInjective ([fzero,fsuc] {n = n})
[fzero,fsuc]-IsInjective = pair-IsInjective ⊤-rec-IsInjective fsuc-IsInjective λ _ _ → ¬fzero≡fsuc

[fzero,fsuc]-IsSurjective : {n : ℕ} → IsSurjective ([fzero,fsuc] {n = n})
[fzero,fsuc]-IsSurjective (zero , _) = inl tt , toℕ-IsInjective refl
[fzero,fsuc]-IsSurjective (suc i , si<sn) = inr (i , suc-reflects-< si<sn) , toℕ-IsInjective refl

[fzero,fsuc]-IsEquiv : {n : ℕ} → IsEquiv ([fzero,fsuc] {n = n})
[fzero,fsuc]-IsEquiv = IsInjective×IsSurjective→IsEquiv (⊎-IsSet ⊤-IsSet Fin-IsSet) Fin-IsSet [fzero,fsuc]-IsInjective [fzero,fsuc]-IsSurjective

[finj,fmax] : {n : ℕ} → Fin n ⊎ ⊤ → Fin (suc n)
[finj,fmax] = pair (finj , const fmax)

[finj,fmax]-IsInjective : {n : ℕ} → IsInjective ([finj,fmax] {n = n})
[finj,fmax]-IsInjective = pair-IsInjective finj-IsInjective ⊤-rec-IsInjective λ _ _ → ¬finj≡fmax

[finj,fmax]-IsSurjective : {n : ℕ} → IsSurjective ([finj,fmax] {n = n})
[finj,fmax]-IsSurjective (i , zero , si≡sn) = inr tt , toℕ-IsInjective (suc-IsInjective (sym si≡sn))
[finj,fmax]-IsSurjective (i , suc k , sk+si≡sn) = inl (i , (k , suc-IsInjective sk+si≡sn)) , toℕ-IsInjective refl

[finj,fmax]-IsEquiv : {n : ℕ} → IsEquiv ([finj,fmax]{n = n})
[finj,fmax]-IsEquiv = IsInjective×IsSurjective→IsEquiv (⊎-IsSet Fin-IsSet ⊤-IsSet) Fin-IsSet [finj,fmax]-IsInjective [finj,fmax]-IsSurjective

[inject,raise] : ∀ {m n} → Fin m ⊎ Fin n → Fin (m + n)
[inject,raise] = pair (inject , raise)

[inject,raise]-IsInjective : ∀ {m n} → IsInjective ([inject,raise] {m = m} {n = n})
[inject,raise]-IsInjective = pair-IsInjective inject-IsInjective raise-IsInjective ¬inject≡raise

[inject,raise]-IsSurjective : ∀ {m n} → IsSurjective ([inject,raise] {m = m} {n = n})
[inject,raise]-IsSurjective {m} {n} (i , i<m+n) = case dichotomy i m return fiber [inject,raise] (i , i<m+n) of λ
  { (inl i<m) → inl (i , i<m) , toℕ-IsInjective refl
  ; (inr (k , k+m≡i)) → inr (k , <-k+-inv {k = m} (subst (_< m + n) (sym k+m≡i ∙ +-comm k m) i<m+n)) , toℕ-IsInjective (+-comm m k ∙ k+m≡i)
  }

[inject,raise]-IsEquiv : ∀ {m n} → IsEquiv ([inject,raise] {m = m} {n = n})
[inject,raise]-IsEquiv = IsInjective×IsSurjective→IsEquiv (⊎-IsSet Fin-IsSet Fin-IsSet) Fin-IsSet [inject,raise]-IsInjective [inject,raise]-IsSurjective

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

