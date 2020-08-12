{-# OPTIONS --cubical #-}
module Math.Nat where

open import Agda.Builtin.FromNat
open import Cubical.Data.Nat public using (ℕ; zero; suc; _+_; +-assoc; +-comm; +-zero; _*_; *-comm; *-assoc) renaming (isSetℕ to ℕ-IsSet; injSuc to suc-IsInjective; znots to ¬zero≡suc; snotz to ¬suc≡zero; *-identityˡ to 1-*; *-identityʳ to *-1)
open import Cubical.Data.Nat.Order public using (_<_; _≤_; <-trans; <≤-trans; ≤<-trans; ≤-refl; ≤-antisym; ¬-<-zero; zero-≤; ≤-suc; Trichotomy; lt; eq; gt; _≟_; <-asym; <-weaken; <-split; ≤-+k) renaming (m≤n-isProp to ≤-IsProp; ¬m<m to <-irrefl)
open import Cubical.Data.Nat.Order using (suc-≤-suc; pred-≤-pred; <-wellfounded)
open import Cubical.Induction.WellFounded
open import Math.Dec
open import Math.Type

infixr 8 _^_

_^_ : ℕ → ℕ → ℕ
b ^ zero = 1
b ^ suc e = b * (b ^ e)

-- The use of j + i rather than cubical's i + j makes this version a little easier to work with in proofs
≤-trans : ∀ {k m n} → k ≤ m → m ≤ n → k ≤ n
≤-trans {k} {m} {n} (i , p) (j , q) = j + i , sym (+-assoc j i k) ∙ ap (j +_) p ∙ q

-- TODO: not sold on these names
suc-preserves-≤ : {m n : ℕ} → m ≤ n → suc m ≤ suc n
suc-preserves-≤ = suc-≤-suc

suc-reflects-≤ : {m n : ℕ} → suc m ≤ suc n → m ≤ n
suc-reflects-≤ = pred-≤-pred

suc-preserves-< : {m n : ℕ} → m < n → suc m < suc n
suc-preserves-< = suc-≤-suc

suc-reflects-< : {m n : ℕ} → suc m < suc n → m < n
suc-reflects-< = pred-≤-pred

<-IsProp : ∀ {m n} → IsProp (m < n)
<-IsProp = ≤-IsProp

ℕ-≡-Dec : (m n : ℕ) → Dec (m ≡ n)
ℕ-≡-Dec zero zero = yes refl
ℕ-≡-Dec zero (suc n) = no ¬zero≡suc
ℕ-≡-Dec (suc m) zero = no λ sucm≡zero → ¬zero≡suc (sym sucm≡zero)
ℕ-≡-Dec (suc m) (suc n) with ℕ-≡-Dec m n
ℕ-≡-Dec (suc m) (suc n) | yes m≡n = yes (ap suc m≡n)
ℕ-≡-Dec (suc m) (suc n) | no ¬m≡n = no (λ sm≡sn → ¬m≡n (suc-IsInjective sm≡sn))

<-Dec : ∀ m n → Dec (m < n)
<-Dec _ zero = no ¬-<-zero
<-Dec zero (suc n) = yes (suc-≤-suc zero-≤)  -- TODO: rename proof parts
<-Dec (suc m) (suc n) with <-Dec m n
<-Dec (suc m) (suc n) | yes m<n = yes (suc-preserves-< m<n)
<-Dec (suc m) (suc n) | no ¬m<n = no (λ sm<sn → contradiction (suc-reflects-< sm<sn) ¬m<n)

≤-Dec : ∀ m n → Dec (m ≤ n)
≤-Dec zero _ = yes zero-≤
≤-Dec (suc m) zero = no ¬-<-zero
≤-Dec (suc m) (suc n) with ≤-Dec m n
≤-Dec (suc m) (suc n) | yes m≤n = yes (suc-preserves-≤ m≤n)
≤-Dec (suc m) (suc n) | no ¬m≤n = no (λ sm≤sn → contradiction (suc-reflects-≤ sm≤sn) ¬m≤n)

<-ind : ∀ {ℓ} {P : ℕ → Type ℓ} → (∀ n → (∀ k → k < n → P k) → P n) → (n : ℕ) → P n
<-ind {P = P} = WFI.induction <-wellfounded {P = P}

<-ind-step : ∀ {ℓ} {P : ℕ → Type ℓ} (f : ∀ n → (∀ k → k < n → P k) → P n) (n : ℕ) → <-ind f n ≡ f n (λ i _ → <-ind f i)
<-ind-step {P = P} = WFI.induction-compute <-wellfounded {P = P}

<-rec : ∀ {ℓ} {A : Type ℓ} → (∀ n → (∀ k → k < n → A) → A) → ℕ → A
<-rec {A = A} = WFI.induction <-wellfounded {P = λ _ → A}

<-+k : ∀ {m n k} → m < n → m + k < n + k
<-+k = ≤-+k

-- Agda integer literals
instance
  Numberℕ : Number ℕ
  Numberℕ = record
    { Constraint = λ n → ⊤
    ; fromNat = λ n → n
    }
