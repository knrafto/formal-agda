{-# OPTIONS --cubical #-}
module Math.Int where

open import Cubical.Data.Int using (Int)
import Cubical.Data.Int as Int
open import Cubical.HITs.Ints.BiInvInt public using (zero; suc) renaming (predl to pred; BiInvInt to ℤ; isSetBiInvInt to ℤ-IsSet; discreteBiInvInt to ℤ-HasDecEq)
open import Cubical.HITs.Ints.BiInvInt using (predr; suc-predr; predl; predl-suc; suc-biinvequiv; predl≡predr) renaming (fwd to fromInt; bwd to toInt; fwd-bwd to fromInt-toInt; bwd-fwd to toInt-fromInt)
open import Cubical.Foundations.Equiv.BiInvertible using (biInvEquiv→Equiv-left)
open import Cubical.Foundations.Prelude using (PathP; toPathP)
open import Math.Dec
open import Math.Function
open import Math.Nat using (ℕ; ℕ-IsSet) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; _≤_ to _≤ℕ_; _<_ to _<ℕ_)
import Math.Nat as ℕ
open import Math.Type

infix 4 _≤_ _<_
infixl 6 _+_ _-_
infixl 7 _*_

suc-IsEquiv : IsEquiv suc
suc-IsEquiv = snd (biInvEquiv→Equiv-left suc-biinvequiv)

ℤ-ind-Prop : ∀ {ℓ} {P : ℤ → Type ℓ} → (∀ n → IsProp (P n)) → P zero → (∀ n → P n → P (suc n)) → (∀ n → P n → P (pred n)) → (n : ℤ) → P n
ℤ-ind-Prop {P = P} P-IsProp P-zero P-suc P-pred = φ
  where
  P-predr : ∀ n → P n → P (predr n)
  P-predr n x = subst P (predl≡predr n) (P-pred n x)

  P-predl : ∀ n → P n → P (predl n)
  P-predl = P-pred

  P-IsProp' : {a b : ℤ} (p : a ≡ b) (x : P a) (y : P b) → PathP (λ i → P (p i)) x y
  P-IsProp' _ _ _ = toPathP (P-IsProp _ _ _)

  φ : (n : ℤ) → P n
  φ zero = P-zero
  φ (suc n) = P-suc n (φ n)
  φ (predr n) = P-predr n (φ n)
  φ (suc-predr n i) = P-IsProp' (suc-predr n) (P-suc (predr n) (P-predr n (φ n))) (φ n) i
  φ (predl n) = P-predl n (φ n)
  φ (predl-suc n i) = P-IsProp' (predl-suc n) (P-predl (suc n) (P-suc n (φ n))) (φ n) i

-- Definitional equalities:
-- ℤ-rec a f _ zero = a
-- ℤ-rec a f _ (suc n) = f (ℤ-rec a f _ n)
-- ℤ-rec a f _ (pred n) = f⁻¹ (ℤ-rec a f _ n)
ℤ-rec : ∀ {ℓ} {A : Type ℓ} → A → (f : A → A) → IsEquiv f → ℤ → A
ℤ-rec {A = A} a f f-IsEquiv = φ
  where
  φ : ℤ → A
  φ zero = a
  φ (suc n) = f (φ n)
  φ (predr n) = inv f-IsEquiv (φ n)
  φ (suc-predr n i) = rightInv f-IsEquiv (φ n) i
  φ (predl n) = inv f-IsEquiv (φ n)
  φ (predl-suc n i) = leftInv f-IsEquiv (φ n) i

pos : ℕ → ℤ
pos ℕ.zero = zero
pos (ℕ.suc n) = suc (pos n)

_+_ : ℤ → ℤ → ℤ
_+_ = ℤ-rec id (suc ∘_) (f∘-IsEquiv suc-IsEquiv)

negate : ℤ → ℤ
negate = ℤ-rec zero pred (inv-IsEquiv suc-IsEquiv)

negate-negate : ∀ n → negate (negate n) ≡ n
negate-negate = ℤ-ind-Prop (λ _ → ℤ-IsSet _ _) refl (λ n p → ap suc p) (λ n p → ap pred p)

negate-IsEquiv : IsEquiv negate
negate-IsEquiv = HasInverse→IsEquiv negate negate-negate negate-negate

neg : ℕ → ℤ
neg n = negate (pos n)

_-_ : ℤ → ℤ → ℤ
m - n = m + negate n

+-zero : ∀ n → n + zero ≡ n
+-zero = ℤ-ind-Prop (λ _ → ℤ-IsSet _ _) refl (λ n p → ap suc p) (λ n p → ap pred p)

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc = ℤ-ind-Prop (λ _ → Π-IsProp λ _ → ℤ-IsSet _ _)
  (λ m → refl)
  (λ m p n → ap suc (p n))
  (λ m p n → ap pred (p n) ∙ leftInv suc-IsEquiv (m + n) ∙ sym (rightInv suc-IsEquiv (m + n)))

+-pred : ∀ m n → m + pred n ≡ pred (m + n)
+-pred = ℤ-ind-Prop (λ _ → Π-IsProp λ _ → ℤ-IsSet _ _)
  (λ m → refl)
  (λ m p n → ap suc (p n) ∙ rightInv suc-IsEquiv (m + n) ∙ sym (leftInv suc-IsEquiv (m + n)))
  (λ m p n → ap pred (p n))

+-comm : ∀ m n → m + n ≡ n + m
+-comm m n = +-comm' n m
  where
  +-comm' : ∀ n m → m + n ≡ n + m
  +-comm' = ℤ-ind-Prop (λ _ → Π-IsProp λ _ → ℤ-IsSet _ _)
    +-zero
    (λ n p m → +-suc m n ∙ ap suc (p m))
    (λ n p m → +-pred m n ∙ ap pred (p m))

+-assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
+-assoc = ℤ-ind-Prop (λ _ → Π-IsProp λ _ → Π-IsProp λ _ → ℤ-IsSet _ _)
  (λ n o → refl)
  (λ m p n o → ap suc (p n o))
  (λ m p n o → ap pred (p n o))

-- TODO: name?
negate-leftInv : ∀ n → negate n + n ≡ zero
negate-leftInv = ℤ-ind-Prop (λ _ → ℤ-IsSet _ _)
  refl
  (λ n p → ap pred (+-suc (negate n) n) ∙ leftInv suc-IsEquiv _ ∙ p)
  (λ n p → ap suc (+-pred (negate n) n) ∙ rightInv suc-IsEquiv _ ∙ p)

-- TODO: name?
negate-rightInv : ∀ n → n + negate n ≡ zero
negate-rightInv = ℤ-ind-Prop (λ _ → ℤ-IsSet _ _)
  refl
  (λ n p → ap suc (+-pred n (negate n)) ∙ rightInv suc-IsEquiv _ ∙ p)
  (λ n p → ap pred (+-suc n (negate n)) ∙ leftInv suc-IsEquiv _ ∙ p)

negate-+ : ∀ m n → negate (m + n) ≡ negate m + negate n
negate-+ = ℤ-ind-Prop (λ _ → Π-IsProp λ _ → ℤ-IsSet _ _)
  (λ m → refl)
  (λ m p n → ap pred (p n))
  (λ m p n → ap suc (p n))

n+-IsEquiv : ∀ n → IsEquiv (n +_)
n+-IsEquiv n = HasInverse→IsEquiv (negate n +_)
  (λ m → +-assoc (negate n) n m ∙ ap (_+ m) (negate-leftInv n))
  (λ m → +-assoc n (negate n) m ∙ ap (_+ m) (negate-rightInv n))

+n-IsEquiv : ∀ n → IsEquiv (_+ n)
+n-IsEquiv n = HasInverse→IsEquiv (_- n)
  (λ m → sym (+-assoc m n (negate n)) ∙ ap (m +_) (negate-rightInv n) ∙ +-zero m)
  (λ m → sym (+-assoc m (negate n) n) ∙ ap (m +_) (negate-leftInv n) ∙ +-zero m)

-- TODO: define cancellation lemmas instead of using IsEquiv→IsInjective (+n-IsEquiv n)

pos-+ : ∀ m n → pos (m +ℕ n) ≡ pos m + pos n
pos-+ ℕ.zero n = refl
pos-+ (ℕ.suc m) n = ap suc (pos-+ m n)

neg-+ : ∀ m n → neg (m +ℕ n) ≡ neg m + neg n
neg-+ m n = ap negate (pos-+ m n) ∙ negate-+ (pos m) (pos n)

_*_ : ℤ → ℤ → ℤ
m * n = ℤ-rec zero (n +_) (n+-IsEquiv n) m

*-zero : ∀ n → n * zero ≡ zero
*-zero = ℤ-ind-Prop (λ _ → ℤ-IsSet _ _) refl (λ n p → p) (λ n p → p)

*-suc : ∀ m n → m * suc n ≡ m + m * n
*-suc = ℤ-ind-Prop (λ _ → Π-IsProp λ _ → ℤ-IsSet _ _)
  (λ n → refl)
  (λ m p n → ap suc (ap (n +_) (p n) ∙ +-assoc n m (m * n) ∙ ap (_+ m * n) (+-comm n m) ∙ sym (+-assoc m n (m * n))))
  (λ m p n → ap pred (ap (negate n +_) (p n) ∙ +-assoc (negate n) m (m * n) ∙  ap (_+ m * n) (+-comm (negate n) m) ∙ sym (+-assoc m (negate n) (m * n))))

*-pred : ∀ m n → m * pred n ≡ negate m + m * n
*-pred = ℤ-ind-Prop (λ _ → Π-IsProp λ _ → ℤ-IsSet _ _)
  (λ n → refl)
  (λ m p n → ap pred (ap (n +_) (p n) ∙ +-assoc n (negate m) (m * n) ∙ ap (_+ m * n) (+-comm n (negate m)) ∙ sym (+-assoc (negate m) n (m * n))))
  (λ m p n → ap suc (ap (negate n +_) (p n) ∙ +-assoc (negate n) (negate m) (m * n) ∙ ap (_+ m * n) (+-comm (negate n) (negate m)) ∙ sym (+-assoc (negate m) (negate n) (m * n))))

*-comm : ∀ m n → m * n ≡ n * m
*-comm = ℤ-ind-Prop (λ _ → Π-IsProp λ _ → ℤ-IsSet _ _)
  (λ n → sym (*-zero n))
  (λ m p n → ap (n +_) (p n) ∙ sym (*-suc n m))
  (λ m p n → ap (negate n +_) (p n) ∙ sym (*-pred n m))

pos-* : ∀ m n → pos (m *ℕ n) ≡ pos m * pos n
pos-* ℕ.zero n = refl
pos-* (ℕ.suc m) n = pos-+ n (m *ℕ n) ∙ ap (pos n +_) (pos-* m n)

*-distrib-r : ∀ m n o → (m * o) + (n * o) ≡ (m + n) * o
*-distrib-r = ℤ-ind-Prop (λ _ → Π-IsProp λ _ → Π-IsProp λ _ → ℤ-IsSet _ _)
  (λ n o → refl)
  (λ m p n o → sym (+-assoc o (m * o) (n * o)) ∙ ap (o +_) (p n o))
  (λ m p n o → sym (+-assoc (negate o) (m * o) (n * o)) ∙ ap (negate o +_) (p n o))

negate-* : ∀ m n → negate m * n ≡ negate (m * n)
negate-* = ℤ-ind-Prop (λ _ → Π-IsProp λ _ → ℤ-IsSet _ _)
  (λ n → refl)
  (λ m p n → ap (negate n +_) (p n) ∙ sym (negate-+ n (m * n)))
  (λ m p n → ap (n +_) (p n) ∙ ap (_+ negate (m * n)) (sym (negate-negate n)) ∙ sym (negate-+ (negate n) (m * n)))

neg-*-pos : ∀ m n → neg m * pos n ≡ neg (m *ℕ n)
neg-*-pos m n = negate-* (pos m) (pos n) ∙ ap negate (sym (pos-* m n))

private
  toInt-IsEquiv : IsEquiv toInt
  toInt-IsEquiv = HasInverse→IsEquiv fromInt fromInt-toInt toInt-fromInt

  fromInt-pos : (n : ℕ) → fromInt (Int.pos n) ≡ pos n
  fromInt-pos ℕ.zero = refl
  fromInt-pos (ℕ.suc n) = ap suc (fromInt-pos n)

  fromInt-negsuc : (n : ℕ) → fromInt (Int.negsuc n) ≡ neg (ℕ.suc n)
  fromInt-negsuc ℕ.zero = refl
  fromInt-negsuc (ℕ.suc n) = ap pred (fromInt-negsuc n)

pos-IsInjective : IsInjective pos
pos-IsInjective {m} {n} p = Int.injPos (IsEquiv→IsInjective (inv-IsEquiv toInt-IsEquiv) (fromInt-pos m ∙ p ∙ sym (fromInt-pos n)))

neg-IsInjective : IsInjective neg
neg-IsInjective {m} {n} p = pos-IsInjective (IsEquiv→IsInjective negate-IsEquiv p)

¬pos≡negsuc : ∀ m n → ¬ pos m ≡ neg (ℕ.suc n)
¬pos≡negsuc m n p = Int.posNotnegsuc m n (IsEquiv→IsInjective (inv-IsEquiv toInt-IsEquiv) (fromInt-pos m ∙ p ∙ sym (fromInt-negsuc n)))

-- TODO: name
sign : (z : ℤ) → (Σ[ n ∈ ℕ ] pos n ≡ z) ⊎ (Σ[ n ∈ ℕ ] neg (ℕ.suc n) ≡ z)
sign z = sign-Int (toInt z) (fromInt-toInt z)
  where
  sign-Int : (x : Int) → fromInt x ≡ z → (Σ[ n ∈ ℕ ] pos n ≡ z) ⊎ (Σ[ n ∈ ℕ ] neg (ℕ.suc n) ≡ z)
  sign-Int (Int.pos n) p = inl (n , sym (fromInt-pos n) ∙ p)
  sign-Int (Int.negsuc n) p = inr (n , sym (fromInt-negsuc n) ∙ p)

_≤_ : ℤ → ℤ → Type₀
m ≤ n = Σ[ k ∈ ℕ ] pos k + m ≡ n

≤-IsProp : ∀ {m n} → IsProp (m ≤ n)
≤-IsProp {m} {n} (k₁ , p₁) (k₂ , p₂) = ΣProp≡ (λ _ → ℤ-IsSet _ _) (pos-IsInjective (IsEquiv→IsInjective (+n-IsEquiv m) (p₁ ∙ sym p₂)))

_<_ : ℤ → ℤ → Type₀
m < n = suc m ≤ n

<-IsProp : ∀ {m n} → IsProp (m < n)
<-IsProp = ≤-IsProp

data Trichotomy (m n : ℤ) : Type₀ where
  lt : m < n → Trichotomy m n
  eq : m ≡ n → Trichotomy m n
  gt : n < m → Trichotomy m n

_≟_ : ∀ m n → Trichotomy m n
m ≟ n = case sign (n - m) return Trichotomy m n of λ
  { (inl (ℕ.suc i , possuci≡n-m)) → lt (i , +-suc (pos i) m ∙ ap (_+ m) possuci≡n-m ∙ rightInv (+n-IsEquiv m) n)
  ; (inl (ℕ.zero , zero≡n-m)) → eq (ap (_+ m) zero≡n-m ∙ rightInv (+n-IsEquiv m) n)
  ; (inr (i , negsuci≡n-m)) → gt (i , +-suc (pos i) n ∙ ap (pos (ℕ.suc i) +_) (sym (rightInv (+n-IsEquiv m) n) ∙ ap (_+ m) (sym negsuci≡n-m)) ∙ rightInv (n+-IsEquiv (pos (ℕ.suc i))) m)
  }

≤-refl : ∀ {n} → n ≤ n
≤-refl = 0 , refl

≤-trans : ∀ {k m n} → k ≤ m → m ≤ n → k ≤ n
≤-trans {k} {m} {n} (i , p) (j , q) = j +ℕ i , ap (_+ k) (pos-+ j i) ∙ sym (+-assoc (pos j) (pos i) k) ∙ ap (pos j +_) p ∙ q

≤-antisym : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
≤-antisym {m} {n} (i , p) (j , q) = ap (λ i → pos i + m) (sym i≡0) ∙ p
  where
  j+i≡0 : j +ℕ i ≡ ℕ.zero
  j+i≡0 = pos-IsInjective (IsEquiv→IsInjective (+n-IsEquiv m) (snd (≤-trans (i , p) (j , q))))

  i≡0 : i ≡ 0
  i≡0 = snd (ℕ.m+n≡0→m≡0×n≡0 j+i≡0)

<-weaken : ∀ {m n} → m < n → m ≤ n
<-weaken {m} {n} (i , p) = ℕ.suc i , sym (+-suc (pos i) m) ∙ p

<-irrefl : ∀ {n} → ¬ n < n
<-irrefl {n} (i , p) = ¬pos≡negsuc i ℕ.zero posi≡neg1
  where
  posi≡neg1 : pos i ≡ neg 1
  posi≡neg1 = IsEquiv→IsInjective (+n-IsEquiv (suc n)) (p ∙ sym (rightInv suc-IsEquiv n) ∙ sym (+-suc (neg 1) n))

≤<-trans : ∀ {k m n} → k ≤ m → m < n → k < n
≤<-trans {k} {m} {n} (i , p) (j , q) = j +ℕ i , ap (_+ suc k) (pos-+ j i) ∙ sym (+-assoc (pos j) (pos i) (suc k)) ∙ ap (pos j +_) (+-suc (pos i) k) ∙ ap (λ n → pos j + suc n) p ∙ q

<≤-trans : ∀ {k m n} → k < m → m ≤ n → k < n
<≤-trans {k} {m} {n} (i , p) (j , q) = j +ℕ i , ap (_+ suc k) (pos-+ j i) ∙ sym (+-assoc (pos j) (pos i) (suc k)) ∙ ap (pos j +_) p ∙ q

<-trans : ∀ {k m n} → k < m → m < n → k < n
<-trans k<m m<n = <≤-trans k<m (<-weaken m<n)

<-asym : ∀ {m n} → m < n → ¬ n ≤ m
<-asym m<n n≤m = <-irrefl (<≤-trans m<n n≤m)

≤-Dec : ∀ m n → Dec (m ≤ n)
≤-Dec m n = case m ≟ n return Dec (m ≤ n) of λ
  { (lt m<n) → yes (<-weaken m<n)
  ; (eq m≡n) → yes (subst (m ≤_) m≡n ≤-refl)
  ; (gt n<m) → no (<-asym n<m)
  }

<-Dec : ∀ m n → Dec (m < n)
<-Dec m n = case m ≟ n return Dec (m < n) of λ
  { (lt m<n) → yes m<n
  ; (eq m≡n) → no λ m<n → <-irrefl (subst (_< n) m≡n m<n)
  ; (gt n<m) → no λ m<n → <-irrefl (<-trans n<m m<n)
  }

-- TODO: name
dichotomy : ∀ m n → (m < n) ⊎ (n ≤ m)
dichotomy m n = case m ≟ n return (m < n) ⊎ (n ≤ m) of λ
  { (lt m<n) → inl m<n
  ; (eq m≡n) → inr (subst (_≤ m) m≡n ≤-refl)
  ; (gt n<m) → inr (<-weaken n<m)
  }

pos-≤ : ∀ {m n} → m ≤ℕ n → pos m ≤ pos n
pos-≤ {m} {n} (i , p) = i , sym (pos-+ i m) ∙ ap pos p

pos-< : ∀ {m n} → m <ℕ n → pos m < pos n
pos-< {m} {n} = pos-≤

≤-+k : ∀ {m n k} → m ≤ n → m + k ≤ n + k
≤-+k {m} {n} {k} (i , p) = i , +-assoc (pos i) m k ∙ ap (_+ k) p

<-+k : ∀ {m n k} → m < n → m + k < n + k
<-+k = ≤-+k

<-k+ : ∀ {m n k} → m < n → k + m < k + n
<-k+ {m} {n} {k} m<n = subst (_< k + n) (+-comm m k) (subst (m + k <_) (+-comm n k) (<-+k m<n))

≤-*-pos : ∀ {m n} k → m ≤ n → m * pos k ≤ n * pos k
≤-*-pos {m} {n} k (l , l+m≡n) = l *ℕ k , ap (_+ m * pos k) (pos-* l k) ∙ *-distrib-r (pos l) m (pos k) ∙ ap (_* pos k) l+m≡n

open import Cubical.Data.Nat.Literals public

instance
  fromNatInt : HasFromNat ℤ
  fromNatInt = record { Constraint = λ _ → ⊤ ; fromNat = λ n → pos n }

instance
  fromNegInt : HasFromNeg ℤ
  fromNegInt = record { Constraint = λ _ → ⊤ ; fromNeg = λ n → neg n }
