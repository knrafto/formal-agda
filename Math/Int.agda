{-# OPTIONS --cubical #-}
module Math.Int where

open import Cubical.Data.Int public using (pos; negsuc; neg; _+_) renaming (Int to ℤ; isSetInt to ℤ-IsSet; discreteInt to ℤ-HasDecEq)
open import Math.Dec
open import Math.Nat using (ℕ; zero; suc) renaming (_<_ to _<ℕ_; _≤_ to _≤ℕ_; <-Dec to <ℕ-Dec; ≤-Dec to ≤ℕ-Dec)
open import Math.Type

negate : ℤ → ℤ
negate (pos zero) = pos zero
negate (pos (suc n)) = negsuc n
negate (negsuc n) = pos (suc n)

_-_ : ℤ → ℤ → ℤ
m - n = m + negate n

_<_ : ℤ → ℤ → Type₀
pos m < pos n = m <ℕ n
pos m < negsuc n = ⊥
negsuc m < pos n = ⊤
negsuc m < negsuc n = n <ℕ m

<-Dec : ∀ m n → Dec (m < n)
<-Dec (pos m) (pos n) = <ℕ-Dec m n
<-Dec (pos m) (negsuc n) = no λ x → x
<-Dec (negsuc m) (pos n) = yes tt
<-Dec (negsuc m) (negsuc n) = <ℕ-Dec n m

_≤_ : ℤ → ℤ → Type₀
pos m ≤ pos n = m ≤ℕ n
pos m ≤ negsuc n = ⊥
negsuc m ≤ pos n = ⊤
negsuc m ≤ negsuc n = n ≤ℕ m

≤-Dec : ∀ m n → Dec (m ≤ n)
≤-Dec (pos m) (pos n) = ≤ℕ-Dec m n
≤-Dec (pos m) (negsuc n) = no λ x → x
≤-Dec (negsuc m) (pos n) = yes tt
≤-Dec (negsuc m) (negsuc n) = ≤ℕ-Dec n m
