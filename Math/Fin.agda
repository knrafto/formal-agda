{-# OPTIONS --cubical #-}
module Math.Fin where

open import Math.Dec
open import Math.Function
open import Math.Id
open import Math.Sum
open import Math.Nat
open import Math.Prod
open import Math.Type

Fin : ℕ → Type
Fin zero = ⊥
Fin (suc n) = ⊤ ⊎ Fin n

Fin-IsSet : ∀ {n} → IsSet (Fin n)
Fin-IsSet {n = zero} = ⊥-IsSet
Fin-IsSet {n = suc n} = ⊎-IsSet ⊤-IsSet Fin-IsSet

¬Fin0 : ¬ Fin 0
¬Fin0 x = x

Fin1-IsContr : IsContr (Fin 1)
Fin1-IsContr = inl tt , λ { (inl tt) → refl }

Fin-HasDecEq : ∀ {n} → HasDecEq (Fin n)
Fin-HasDecEq {n = zero} = ⊥-HasDecEq
Fin-HasDecEq {n = suc n} = ⊎-HasDecEq ⊤-HasDecEq Fin-HasDecEq

-- I'd like to be able to define this as:
--
-- toℕ {n = suc n} (inl tt) = 0
-- toℕ {n = suc n} (inr i) = suc (toℕ i)
--
-- and still be able to give a slick "trivial" proof of
-- toℕ-IsInjective. In other words, I wish Agda's pattern matching was
-- judgmentally equal to using eliminators.
toℕ : ∀ {n} → Fin n → ℕ
toℕ {n = zero} = ⊥-rec
toℕ {n = suc n} = pair (⊤-rec 0 , suc ∘ toℕ)

toℕ-IsInjective : ∀ {n} → IsInjective (toℕ {n = n})
toℕ-IsInjective {n = zero} = ⊥-rec-IsInjective
toℕ-IsInjective {n = suc n} = pair-IsInjective ⊤-rec-IsInjective (suc-IsInjective ∘-IsInjective toℕ-IsInjective) (λ a b → ¬zero≡suc)

toℕ-< : ∀ {n} (i : Fin n) → toℕ i < n
toℕ-< {n = suc n} (inl tt) = suc-preserves-≤ zero-≤
toℕ-< {n = suc n} (inr i) = suc-preserves-≤ (toℕ-< i)

fzero : ∀ {n} → Fin (suc n)
fzero = inl tt

fsuc : ∀ {n} → Fin n → Fin (suc n)
fsuc i = inr i

fsuc-IsInjective : ∀ {n} → IsInjective (fsuc {n = n})
fsuc-IsInjective = inr-IsInjective

¬fzero≡fsuc : {n : ℕ} {i : Fin n} → ¬ fzero ≡ fsuc i
¬fzero≡fsuc = ¬inl≡inr

fromℕ : ∀ {n} (i : ℕ) → i < n → Fin n
fromℕ {n = zero} i i<n = ⊥-rec (¬-<-zero i<n)
fromℕ {n = suc n} zero i<n = fzero
fromℕ {n = suc n} (suc i) i<n = fsuc (fromℕ i (suc-reflects-< i<n))

toℕ-fromℕ : ∀ {n} (i : ℕ) (i<n : i < n) → toℕ (fromℕ i i<n) ≡ i
toℕ-fromℕ {n = zero} i i<n = ⊥-rec (¬-<-zero i<n)
toℕ-fromℕ {n = suc n} zero i<n = refl
toℕ-fromℕ {n = suc n} (suc i) i<n = ap suc (toℕ-fromℕ i (suc-reflects-< i<n))

finj : ∀ {n : ℕ} → Fin n → Fin (suc n)
finj {n = zero} = ⊥-rec
finj {n = suc n} = pair (⊤-rec fzero , fsuc ∘ finj)

fmax : ∀ {n : ℕ} → Fin (suc n)
fmax {n = zero} = fzero
fmax {n = suc n} = fsuc fmax

finj-IsInjective : {n : ℕ} → IsInjective (finj {n = n})
finj-IsInjective {n = zero} = ⊥-rec-IsInjective
finj-IsInjective {n = suc n} = pair-IsInjective ⊤-rec-IsInjective (fsuc-IsInjective ∘-IsInjective finj-IsInjective) (λ a b → ¬fzero≡fsuc)

¬finj≡fmax : {n : ℕ} {i : Fin n} → ¬ finj i ≡ fmax
¬finj≡fmax {n = suc n} {i = inl tt} = ¬fzero≡fsuc
¬finj≡fmax {n = suc n} {i = inr i} = ¬finj≡fmax ∘ fsuc-IsInjective

toℕ-finj : ∀ {n} (i : Fin n) → toℕ (finj i) ≡ toℕ i
toℕ-finj {n = suc n} (inl tt) = refl
toℕ-finj {n = suc n} (inr i) = ap suc (toℕ-finj i)

toℕ-fmax : ∀ {n} → toℕ (fmax {n = n}) ≡ n
toℕ-fmax {n = zero} = refl
toℕ-fmax {n = suc n} = ap suc toℕ-fmax

Fin-+ : ∀ {m n} → Fin (m + n) → Fin m ⊎ Fin n
Fin-+ {m = zero} = inr
Fin-+ {m = suc m} = ⊎-unassoc ∘ ⊎-map id Fin-+

Fin-+-IsEquiv : ∀ {m n} → IsEquiv (Fin-+ {m = m} {n = n})
Fin-+-IsEquiv {m = zero} = ⊥-inr-IsEquiv
Fin-+-IsEquiv {m = suc m} = ⊎-unassoc-IsEquiv ∘-IsEquiv ⊎-map-IsEquiv id-IsEquiv Fin-+-IsEquiv

Fin-* : ∀ {m n} → Fin (m * n) → Fin m × Fin n
Fin-* {m = zero} = ⊥-rec
Fin-* {m = suc m} = ⊎-factor ∘ ⊎-map (λ i → (tt , i)) Fin-* ∘ Fin-+

Fin-*-IsEquiv : ∀ {m n} → IsEquiv (Fin-* {m = m} {n = n})
Fin-*-IsEquiv {m = zero} = ⊥-rec-IsEquiv fst
Fin-*-IsEquiv {m = suc m} = ⊎-factor-IsEquiv ∘-IsEquiv ⊎-map-IsEquiv (inv-IsEquiv ⊤-snd-IsEquiv) Fin-*-IsEquiv ∘-IsEquiv Fin-+-IsEquiv

-- TODO: there's an ugly "+-comm" in here, is the definition of ^
-- wrong? Why did I write it this way in the first place?
--
-- Eventually we'll want to prove this is order-preserving. What is
-- the ordering for functions? Probably some kind of lexicographic
-- ordering: for two functions f, g : A → B, we say f < g if there is
-- some a : A such that f a < g a and ∀ a' < a we have f a' = g a'.
Fin-^ : ∀ {m n} → Fin (n ^ m) → (Fin m → Fin n)
Fin-^ {m = zero} {n = n} = λ i → ⊥-rec
Fin-^ {m = suc m} {n = n} = pair ∘ ×-map ⊤-ind Fin-^ ∘ Fin-* ∘ subst Fin (*-comm (n ^ m) n)

Fin-^-IsEquiv : ∀ {m n} → IsEquiv (Fin-^ {m = m} {n = n})
Fin-^-IsEquiv {m = zero} {n = n} = IsContr→IsContr→IsEquiv Fin1-IsContr Π-⊥-IsContr
Fin-^-IsEquiv {m = suc m} {n = n} = pair-IsEquiv ∘-IsEquiv ×-map-IsEquiv ⊤-ind-IsEquiv Fin-^-IsEquiv ∘-IsEquiv Fin-*-IsEquiv ∘-IsEquiv subst-IsEquiv Fin (*-comm (n ^ m) n)

-- i ↦ n - i - 1
reflect : ∀ {n} → Fin n → Fin n
reflect {n = suc n} (inl tt) = fmax
reflect {n = suc n} (inr i) = finj (reflect i)

reflect-finj : ∀ {n} (i : Fin n) → reflect (finj i) ≡ fsuc (reflect i)
reflect-finj {n = suc n} (inl tt) = refl
reflect-finj {n = suc n} (inr i) = ap finj (reflect-finj i)

reflect-fmax : ∀ {n} → reflect fmax ≡ fzero {n = n}
reflect-fmax {n = zero} = refl
reflect-fmax {n = suc n} = ap finj reflect-fmax

reflect-reflect : ∀ {n} (i : Fin n) → reflect (reflect i) ≡ i
reflect-reflect {n = suc n} (inl tt) = reflect-fmax
reflect-reflect {n = suc n} (inr i) = reflect-finj _ ∙ ap fsuc (reflect-reflect i)

reflect-IsEquiv : ∀ {n} → IsEquiv (reflect {n = n})
reflect-IsEquiv {n} = HasInverse→IsEquiv reflect reflect-reflect reflect-reflect

toℕ-reflect : ∀ {n} (i : Fin n) → suc (toℕ i + toℕ (reflect i)) ≡ n
toℕ-reflect {n = suc n} (inl tt) = ap suc (toℕ-fmax)
toℕ-reflect {n = suc n} (inr i) = ap suc (ap (λ x → suc (toℕ i + x)) (toℕ-finj (reflect i)) ∙ toℕ-reflect i)

Fin-∀-Dec : ∀ {ℓ} {n : ℕ} {P : Fin n → Type ℓ} → (∀ i → Dec (P i)) → Dec (∀ i → P i)
Fin-∀-Dec {n = zero}  {P} P-Dec = yes λ i → ⊥-rec i
Fin-∀-Dec {n = suc k} {P} P-Dec with P-Dec fzero | Fin-∀-Dec (λ i → P-Dec (fsuc i))
... | yes P-fzero | yes P-rest = yes λ { (inl tt) → P-fzero; (inr i) → P-rest i }
... | yes P-fzero | no ¬P-rest = no λ f → ¬P-rest λ i → f (fsuc i)
... | no ¬P-fzero | _ = no λ f → ¬P-fzero (f fzero)

Fin-∃-Dec : ∀ {ℓ} {n} {P : Fin n → Type ℓ} → (∀ i → Dec (P i)) → Dec ∥ Σ[ i ∈ Fin n ] P i ∥
Fin-∃-Dec {n = zero}  {P} P-Dec = no (∥∥-rec ⊥-IsProp λ { (i , _) → ⊥-rec i })
Fin-∃-Dec {n = suc k} {P} P-Dec with P-Dec fzero | Fin-∃-Dec (λ i → P-Dec (fsuc i))
... | yes P-fzero | _          = yes ∣ fzero , P-fzero ∣
... | no ¬P-fzero | yes P-rest = with-∥∥ P-rest (Dec-IsProp ∥∥-IsProp) λ { (i , P-fsuci) → yes ∣ fsuc i , P-fsuci ∣ }
... | no ¬P-fzero | no ¬P-rest = no (∥∥-rec ⊥-IsProp λ { (inl tt , P-fzero) → ¬P-fzero P-fzero ; (inr i , P-rest) → ¬P-rest ∣ i , P-rest ∣ })
