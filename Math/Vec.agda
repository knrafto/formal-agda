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
uncons-IsEquiv = ×-map-IsEquiv (inv-IsEquiv (const-IsEquiv ⊤-IsContr)) id-IsEquiv ∘-IsEquiv inv-IsEquiv pair-IsEquiv ∘-IsEquiv ∘f-IsEquiv [fzero,fsuc]-IsEquiv

cons : ∀ {n} → A × Vec n A → Vec (suc n) A
cons = inv uncons-IsEquiv

init : {n : ℕ} → Vec (suc n) A → Vec n A
init v = λ i → v (finj i)

last : {n : ℕ} → Vec (suc n) A → A
last v = v fmax

unsnoc : ∀ {n} → Vec (suc n) A → Vec n A × A
unsnoc v = (init v , last v)

unsnoc-IsEquiv : ∀ {n} → IsEquiv (unsnoc {A = A} {n = n})
unsnoc-IsEquiv = ×-map-IsEquiv id-IsEquiv (inv-IsEquiv (const-IsEquiv ⊤-IsContr)) ∘-IsEquiv inv-IsEquiv pair-IsEquiv ∘-IsEquiv ∘f-IsEquiv [finj,fmax]-IsEquiv

snoc : ∀ {n} → Vec n A × A → Vec (suc n) A
snoc = inv unsnoc-IsEquiv

last-tail : ∀ {n} (w : Vec (suc (suc n)) A) → last (tail w) ≡ last w
last-tail w = ap w (toℕ-IsInjective refl)

take : ∀ m {n} → Vec (m + n) A → Vec m A
take m v = λ i → v (inject i)

drop : ∀ m {n} → Vec (m + n) A → Vec n A
drop m v = λ i → v (raise i)

split : {m n : ℕ} → Vec (m + n) A → Vec m A × Vec n A
split {m = m} v = (take m v , drop m v)

split-IsEquiv : {m n : ℕ} → IsEquiv (split {A = A} {m = m} {n = n})
split-IsEquiv = inv-IsEquiv pair-IsEquiv ∘-IsEquiv ∘f-IsEquiv [inject,raise]-IsEquiv

concat : {m n : ℕ} → Vec m A × Vec n A → Vec (m + n) A
concat = inv split-IsEquiv

concat-IsEquiv : {m n : ℕ} → IsEquiv (concat {A = A} {m = m} {n = n})
concat-IsEquiv = inv-IsEquiv split-IsEquiv

take-concat : ∀ {m n} (x : Vec m A) (y : Vec n A) → take m (concat (x , y)) ≡ x
take-concat x y = ap fst (leftInv concat-IsEquiv (x , y))

drop-concat : ∀ {m n} (x : Vec m A) (y : Vec n A) → drop m (concat (x , y)) ≡ y
drop-concat x y = ap snd (leftInv concat-IsEquiv (x , y))

take-tail : ∀ {m n} (v : Vec (suc m + n) A) → take m (tail v) ≡ tail (take (suc m) v)
take-tail v = funExt λ i → ap v (toℕ-IsInjective refl)

drop-tail : ∀ {m n} (v : Vec (suc m + n) A) → drop m (tail v) ≡ drop (suc m) v
drop-tail v = funExt λ i → ap v (toℕ-IsInjective refl)

tail-concat : ∀ {m n} (x : Vec (suc m) A) (y : Vec n A) → tail (concat (x , y)) ≡ concat (tail x , y)
tail-concat {A = A} {m = m} {n = n} x y = sym (rightInv concat-IsEquiv _) ∙ ap concat (×≡ (take-tail v ∙ ap tail (take-concat x y) , drop-tail v ∙ drop-concat x y))
  where
  v : Vec (suc m + n) A
  v = concat (x , y)

singleton : A → Vec 1 A
singleton a = const a

singleton-IsEquiv : IsEquiv (singleton {A = A})
singleton-IsEquiv = const-IsEquiv Fin1-IsContr

reverse : ∀ {n} → Vec n A → Vec n A
reverse v = λ i → v (reflect i)

reverse-IsEquiv : ∀ {n} → IsEquiv (reverse {A = A} {n = n})
reverse-IsEquiv = ∘f-IsEquiv reflect-IsEquiv
