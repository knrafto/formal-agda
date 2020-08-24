{-# OPTIONS --cubical #-}
module Math.Vec where

open import Math.Dec
open import Math.Fin
open import Math.Function
open import Math.Nat
open import Math.Prod
open import Math.Sum
open import Math.Type

private
  variable
    ℓ ℓ′ : Level
    A : Type ℓ

-- TODO: the definitions of concat, split, cons, head, tail, etc. are too obscure, and makes definitional equality hard to reason about.
-- Need to rewrite using operations on indices. For example:
-- head v = v fzero
-- tail v = v ∘ fsuc
-- uncons v = (head v , tail v)
-- uncons-IsEquiv
-- cons = inv uncons
--
-- This will require rewriting/renaming the definitions in Fin (for the better)

Vec : ℕ → Type ℓ → Type ℓ
Vec n A = Fin n → A

Vec-IsSet : {n : ℕ} → IsSet A → IsSet (Vec n A)
Vec-IsSet A-IsSet = Π-IsSet (λ _ → A-IsSet)

Vec-HasDecEq : {n : ℕ} → HasDecEq A → HasDecEq (Vec n A)
Vec-HasDecEq A-HasDecEq v₁ v₂ = case Fin-∀-Dec (λ i → A-HasDecEq (v₁ i) (v₂ i)) return Dec (v₁ ≡ v₂) of λ
  { (yes p) → yes (funExt p)
  ; (no ¬p) → no λ v₁≡v₂ → ¬p (happly v₁≡v₂)
  }

Vec0-IsContr : IsContr (Vec 0 A)
Vec0-IsContr = (λ i → ⊥-rec (¬Fin0 i)) , λ y → funExt λ i → ⊥-rec (¬Fin0 i)

concat : {m n : ℕ} → Vec m A × Vec n A → Vec (m + n) A
concat = (_∘ inv Fin-+-IsEquiv) ∘ pair

concat-IsEquiv : {m n : ℕ} → IsEquiv (concat {A = A} {m = m} {n = n})
concat-IsEquiv = ∘f-IsEquiv (inv-IsEquiv Fin-+-IsEquiv) ∘-IsEquiv pair-IsEquiv

split : {m n : ℕ} → Vec (m + n) A → Vec m A × Vec n A
split = inv concat-IsEquiv

split-IsEquiv : {m n : ℕ} → IsEquiv (split {A = A} {m = m} {n = n})
split-IsEquiv = inv-IsEquiv concat-IsEquiv

singleton : A → Vec 1 A
singleton a = const a

singleton-IsEquiv : IsEquiv (singleton {A = A})
singleton-IsEquiv = const-IsEquiv Fin1-IsContr

cons : {n : ℕ} → A × Vec n A → Vec (suc n) A
cons = (_∘ inv Fin-suc-IsEquiv) ∘ pair ∘ ×-map const id

cons-IsEquiv : {n : ℕ} → IsEquiv (cons {A = A} {n = n})
cons-IsEquiv = ∘f-IsEquiv (inv-IsEquiv Fin-suc-IsEquiv) ∘-IsEquiv pair-IsEquiv ∘-IsEquiv ×-map-IsEquiv (const-IsEquiv ⊤-IsContr) id-IsEquiv

uncons : {n : ℕ} → Vec (suc n) A → A × Vec n A
uncons = inv cons-IsEquiv

head : {n : ℕ} → Vec (suc n) A → A
head v = fst (uncons v)

tail : {n : ℕ} → Vec (suc n) A → Vec n A
tail v = snd (uncons v)

snoc : {n : ℕ} → Vec n A × A → Vec (suc n) A
snoc = (_∘ inv Fin-pred-IsEquiv) ∘ pair ∘ ×-map id const

snoc-IsEquiv : {n : ℕ} → IsEquiv (snoc {A = A} {n = n})
snoc-IsEquiv = ∘f-IsEquiv (inv-IsEquiv Fin-pred-IsEquiv) ∘-IsEquiv pair-IsEquiv ∘-IsEquiv ×-map-IsEquiv id-IsEquiv (const-IsEquiv ⊤-IsContr)

unsnoc : {n : ℕ} → Vec (suc n) A → Vec n A × A
unsnoc = inv snoc-IsEquiv

init : {n : ℕ} → Vec (suc n) A → Vec n A
init v = fst (unsnoc v)

last : {n : ℕ} → Vec (suc n) A → A
last v = snd (unsnoc v)

last-tail : ∀ {n : ℕ} (w : Vec (suc (suc n)) A) → last (tail w) ≡ last w
last-tail w = ap w fsuc-fmax

reverse : ∀ {n} → Vec n A → Vec n A
reverse = _∘ reflect

reverse-IsEquiv : ∀ {n} → IsEquiv (reverse {A = A} {n = n})
reverse-IsEquiv = ∘f-IsEquiv reflect-IsEquiv

replicate : (n : ℕ) → A → Vec n A
replicate n a = λ i → a
