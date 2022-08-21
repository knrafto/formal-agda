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

empty : Vec 0 A
empty = λ i → ⊥-rec (¬Fin0 i)

Vec0-IsContr : IsContr (Vec 0 A)
Vec0-IsContr = empty , λ y → funExt λ i → ⊥-rec (¬Fin0 i)

replicate : (n : ℕ) → A → Vec n A
replicate n a = λ i → a

singleton : A → Vec 1 A
singleton a = const a

singleton-IsEquiv : IsEquiv (singleton {A = A})
singleton-IsEquiv = const-IsEquiv Fin1-IsContr

cons : ∀ {n} → A × Vec n A → Vec (suc n) A
cons = pair ∘ ×-map const id

cons-IsEquiv : ∀ {n} → IsEquiv (cons {A = A} {n = n})
cons-IsEquiv = pair-IsEquiv ∘-IsEquiv ×-map-IsEquiv (const-IsEquiv ⊤-IsContr) id-IsEquiv

uncons : ∀ {n} → Vec (suc n) A → A × Vec n A
uncons = inv cons-IsEquiv

uncons-IsEquiv : ∀ {n} → IsEquiv (uncons {A = A} {n = n})
uncons-IsEquiv = inv-IsEquiv cons-IsEquiv

concat : {m n : ℕ} → Vec m A × Vec n A → Vec (m + n) A
concat = (λ v → v ∘ Fin-+) ∘ pair

concat-IsEquiv : {m n : ℕ} → IsEquiv (concat {A = A} {m = m} {n = n})
concat-IsEquiv = ∘f-IsEquiv Fin-+-IsEquiv ∘-IsEquiv pair-IsEquiv

split : {m n : ℕ} → Vec (m + n) A → Vec m A × Vec n A
split = inv concat-IsEquiv

split-IsEquiv : {m n : ℕ} → IsEquiv (split {A = A} {m = m} {n = n})
split-IsEquiv = inv-IsEquiv concat-IsEquiv

reverse : ∀ {n} → Vec n A → Vec n A
reverse v = λ i → v (reflect i)

reverse-IsEquiv : ∀ {n} → IsEquiv (reverse {A = A} {n = n})
reverse-IsEquiv = ∘f-IsEquiv reflect-IsEquiv
