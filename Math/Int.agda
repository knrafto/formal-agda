{-# OPTIONS --cubical --allow-unsolved-metas #-}
module Math.Int where

open import Cubical.Data.Int public using (pos; negsuc; neg; _+_; _-_) renaming (Int to ℤ; isSetInt to ℤ-IsSet; discreteInt to ℤ-HasDecEq)
open import Cubical.Data.Int using (sucInt; predInt; _+pos_; _+negsuc_)
open import Math.Dec
open import Math.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_; _<_ to _<ℕ_; _≤_ to _≤ℕ_; <-Dec to <ℕ-Dec; ≤-Dec to ≤ℕ-Dec)
import Math.Nat as ℕ
open import Math.Type

-- TODO: define + to induct on left argument instead of right?
-- TODO: define binary - in terms of unary -?

-_ : ℤ → ℤ
- n = pos zero - n

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
