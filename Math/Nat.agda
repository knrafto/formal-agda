{-# OPTIONS --cubical #-}
module Math.Nat where

open import Cubical.Data.Nat public using (ℕ; zero; suc; _+_; +-assoc; +-comm; _*_) renaming (injSuc to suc-IsInjective; znots to ¬zero≡suc)
open import Cubical.Data.Nat.Order public using (_<_; _≤_; <≤-trans; ≤<-trans; ¬-<-zero; zero-≤)
open import Cubical.Data.Nat.Order using (suc-≤-suc; pred-≤-pred)
open import Math.Decidable
open import Math.Type

infixr 8 _^_

_^_ : ℕ → ℕ → ℕ
b ^ zero = 1
b ^ suc e = b * (b ^ e)

suc-preserves-≤ : {m n : ℕ} → m ≤ n → suc m ≤ suc n
suc-preserves-≤ = suc-≤-suc

suc-reflects-≤ : {m n : ℕ} → suc m ≤ suc n → m ≤ n
suc-reflects-≤ = pred-≤-pred

suc-preserves-< : {m n : ℕ} → m < n → suc m < suc n
suc-preserves-< = suc-≤-suc

suc-reflects-< : {m n : ℕ} → suc m < suc n → m < n
suc-reflects-< = pred-≤-pred

<-Dec : ∀ m n → Dec (m < n)
<-Dec _ zero = no ¬-<-zero
<-Dec zero (suc n) = yes (suc-≤-suc zero-≤)  -- TODO: rename proof parts
<-Dec (suc m) (suc n) with <-Dec m n
<-Dec (suc m) (suc n) | yes m<n = yes (suc-preserves-< m<n)
<-Dec (suc m) (suc n) | no ¬m<n = no (λ sm<sn → contradiction (suc-reflects-< sm<sn) ¬m<n)
