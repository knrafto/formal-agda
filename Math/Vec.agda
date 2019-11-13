{-# OPTIONS --cubical #-}
module Math.Vec where

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

Vec0-IsContr : IsContr (Vec 0 A)
Vec0-IsContr = (λ i → ⊥-elim (¬Fin0 i)) , λ y → funExt λ i → ⊥-elim (¬Fin0 i)

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
cons = concat ∘ ×-map singleton id

cons-IsEquiv : {n : ℕ} → IsEquiv (cons {A = A} {n = n})
cons-IsEquiv = concat-IsEquiv ∘-IsEquiv ×-map-IsEquiv singleton-IsEquiv id-IsEquiv

0-vector : Vec 0 A
0-vector = λ i → ⊥-elim (¬Fin0 i)

1-vector : A → Vec 1 A
1-vector a₀ = cons (a₀ , 0-vector)

2-vector : A → A → Vec 2 A
2-vector a₀ a₁ = cons (a₀ , 1-vector a₁)

3-vector : A → A → A → Vec 3 A
3-vector a₀ a₁ a₂ = cons (a₀ , 2-vector a₁ a₂)

4-vector : A → A → A → A → Vec 4 A
4-vector a₀ a₁ a₂ a₃ = cons (a₀ , 3-vector a₁ a₂ a₃)

5-vector : A → A → A → A → A → Vec 5 A
5-vector a₀ a₁ a₂ a₃ a₄ = cons (a₀ , 4-vector a₁ a₂ a₃ a₄)

-- Note digits are in big-endian order.
fromDigits : {d n : ℕ} → Vec n (Fin d) → Fin (d ^ n)
fromDigits {n = zero} = const fzero
fromDigits {n = suc n} = Fin-* ∘ ×-map id fromDigits ∘ inv cons-IsEquiv

fromDigits-IsEquiv : {d n : ℕ} → IsEquiv (fromDigits {d = d} {n = n})
fromDigits-IsEquiv {n = zero} = IsContr→IsContr→IsEquiv Vec0-IsContr Fin1-IsContr
fromDigits-IsEquiv {n = suc n} = Fin-*-IsEquiv ∘-IsEquiv (×-map-IsEquiv id-IsEquiv fromDigits-IsEquiv) ∘-IsEquiv (inv-IsEquiv cons-IsEquiv)
