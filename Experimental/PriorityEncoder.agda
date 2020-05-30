{-# OPTIONS --cubical #-}
module Experimental.PriorityEncoder where

open import Math.Dec
open import Math.Fin
open import Math.Nat
open import Math.Type

clog2 : ℕ → ℕ
clog2 = {!!}

n≤2^clog2n : ∀ n → n ≤ 2 ^ clog2 n
n≤2^clog2n = {!!}

<-Fin : ∀ {n} → Fin n → Fin n → Type₀
<-Fin i j = toℕ i < toℕ j

Max : {A : Type₀} → (_<_ : A → A → Type₀) → (P : A → Type₀) → Type₀
Max = {!!}

theorem : ∀ n → 2 ≤ n → (P : Fin n → Type₀) → (∀ i → Dec (P i)) → Dec (Max <-Fin P)
theorem = <-ind λ n rec 2≤n P P-Dec →
  case n ≟ 2 return Dec (Max <-Fin P) of λ
    { (lt n<2) → ⊥-rec (<-asym n<2 2≤n)
    ; (eq n≡2) → {!!}
    ; (gt 2<n) → {!!}
    }
