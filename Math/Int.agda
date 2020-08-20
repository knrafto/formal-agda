{-# OPTIONS --cubical --allow-unsolved-metas #-}
module Math.Int where

open import Cubical.Data.Int public using (pos; neg; _+_; _-_) renaming (Int to ℤ)
open import Math.Dec
open import Math.Nat using (ℕ) renaming (_<_ to _<ℕ_; _≤_ to _≤ℕ_)
open import Math.Type

_<_ : ℤ → ℤ → Type₀
ℤ.pos m < ℤ.pos n = m <ℕ n
ℤ.pos m < ℤ.negsuc n = ⊥
ℤ.negsuc m < ℤ.pos n = ⊤
ℤ.negsuc m < ℤ.negsuc n = n <ℕ m

<-Dec : ∀ m n → Dec (m < n)
<-Dec = {!!}

_≤_ : ℤ → ℤ → Type₀
ℤ.pos m ≤ ℤ.pos n = m ≤ℕ n
ℤ.pos m ≤ ℤ.negsuc n = ⊥
ℤ.negsuc m ≤ ℤ.pos n = ⊤
ℤ.negsuc m ≤ ℤ.negsuc n = n ≤ℕ m

≤-Dec : ∀ m n → Dec (m ≤ n)
≤-Dec = {!!}
