{-# OPTIONS --cubical #-}
module Math.Nat where

open import Cubical.Data.Nat public using (ℕ; zero; suc; _+_; +-assoc; +-comm; +-zero; _*_; *-comm) renaming (isSetℕ to ℕ-IsSet; injSuc to suc-IsInjective; znots to ¬zero≡suc; snotz to ¬suc≡zero)
open import Cubical.Data.Nat.Order public using (_<_; _≤_; <-trans; <≤-trans; ≤<-trans; ≤-refl; ≤-antisym; ¬-<-zero; zero-≤; ≤-suc; Trichotomy; lt; eq; gt; _≟_; <-asym) renaming (m≤n-isProp to ≤-IsProp)
open import Cubical.Data.Nat.Order using (suc-≤-suc; pred-≤-pred)
open import Math.Dec
open import Math.Type

infixr 8 _^_

_^_ : ℕ → ℕ → ℕ
b ^ zero = 1
b ^ suc e = b * (b ^ e)

-- The use of j + i rather than cubical's i + j makes this version a little easier to work with in proofs
≤-trans : ∀ {k m n} → k ≤ m → m ≤ n → k ≤ n
≤-trans {k} {m} {n} (i , p) (j , q) = j + i , sym (+-assoc j i k) ∙ ap (j +_) p ∙ q

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

1-* : ∀ n → 1 * n ≡ n
1-* n = +-zero n

*-1 : ∀ n → n * 1 ≡ n
*-1 n = *-comm n 1 ∙ 1-* n

-- TODO: name?
*-dist-r : ∀ m n o → (n + o) * m ≡ n * m + o * m
*-dist-r _ zero _ = refl
*-dist-r m (suc n) o = ap (m +_) (*-dist-r m n o) ∙ +-assoc m (n * m) (o * m)

-- TODO: contribute to cubical?
*-assoc : ∀ m n o → m * (n * o) ≡ (m * n) * o
*-assoc zero _ _ = refl
*-assoc (suc m) n o = ap (n * o +_) (*-assoc m n o) ∙ sym (*-dist-r o n (m * n))
