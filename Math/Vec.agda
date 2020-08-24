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

replicate : (n : ℕ) → A → Vec n A
replicate n a = λ i → a

head : ∀ {n} → Vec (suc n) A → A
head v = v fzero

tail : ∀ {n} → Vec (suc n) A → Vec n A
tail v = λ i → v (fsuc i)

uncons : ∀ {n} → Vec (suc n) A → A × Vec n A
uncons v = (head v , tail v)

uncons-IsEquiv : ∀ {n} → IsEquiv (uncons {A = A} {n = n})
uncons-IsEquiv = ×-map-IsEquiv (inv-IsEquiv (const-IsEquiv ⊤-IsContr)) id-IsEquiv ∘-IsEquiv inv-IsEquiv pair-IsEquiv ∘-IsEquiv ∘f-IsEquiv Fin-suc-IsEquiv

cons : ∀ {n} → A × Vec n A → Vec (suc n) A
cons = inv uncons-IsEquiv

init : {n : ℕ} → Vec (suc n) A → Vec n A
init v = λ i → v (finj i)

last : {n : ℕ} → Vec (suc n) A → A
last v = v fmax

unsnoc : ∀ {n} → Vec (suc n) A → Vec n A × A
unsnoc v = (init v , last v)

unsnoc-IsEquiv : ∀ {n} → IsEquiv (unsnoc {A = A} {n = n})
unsnoc-IsEquiv = ×-map-IsEquiv id-IsEquiv (inv-IsEquiv (const-IsEquiv ⊤-IsContr)) ∘-IsEquiv inv-IsEquiv pair-IsEquiv ∘-IsEquiv ∘f-IsEquiv Fin-pred-IsEquiv

snoc : ∀ {n} → Vec n A × A → Vec (suc n) A
snoc = inv unsnoc-IsEquiv

last-tail : ∀ {n : ℕ} (w : Vec (suc (suc n)) A) → last (tail w) ≡ last w
last-tail w = ap w fsuc-fmax

-- TODO: Rewrite split to operate on indices, and make concat the inv of split

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

reverse : ∀ {n} → Vec n A → Vec n A
reverse v = λ i → v (reflect i)

reverse-IsEquiv : ∀ {n} → IsEquiv (reverse {A = A} {n = n})
reverse-IsEquiv = ∘f-IsEquiv reflect-IsEquiv
