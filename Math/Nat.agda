{-# OPTIONS --cubical #-}
module Math.Nat where

open import Cubical.Data.Nat public using (ℕ; zero; suc; _+_)
open import Cubical.Data.Nat.Order public using (_<_)
open import Cubical.Data.Nat.Order using (¬-<-zero; zero-≤; suc-≤-suc; pred-≤-pred)
open import Math.Decidable
open import Math.Type

<-Dec : ∀ m n → Dec (m < n)
<-Dec _ zero = no ¬-<-zero
<-Dec zero (suc n) = yes (suc-≤-suc zero-≤)
<-Dec (suc m) (suc n) with <-Dec m n
<-Dec (suc m) (suc n) | yes m<n = yes (suc-≤-suc m<n)
<-Dec (suc m) (suc n) | no ¬m<n = no (λ sm<sn → contradiction (pred-≤-pred sm<sn) ¬m<n)
