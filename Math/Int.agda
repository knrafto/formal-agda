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
open import Math.Nat using (ℕ; ℕ-IsSet)
import Math.Nat as ℕ
open import Math.Type

infixl 6 _+_ _-_

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

_+_ : ℤ → ℤ → ℤ
_+_ = ℤ-rec id (suc ∘_) (f∘-IsEquiv suc-IsEquiv)

negate : ℤ → ℤ
negate = ℤ-rec zero pred (inv-IsEquiv suc-IsEquiv)

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

-- TODO: name?
negate-distrib : ∀ m n → negate (m + n) ≡ negate m + negate n
negate-distrib = ℤ-ind-Prop (λ _ → Π-IsProp λ _ → ℤ-IsSet _ _)
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

pos : ℕ → ℤ
pos ℕ.zero = zero
pos (ℕ.suc n) = suc (pos n)

neg : ℕ → ℤ
neg n = negate (pos n)

toInt-IsEquiv : IsEquiv toInt
toInt-IsEquiv = HasInverse→IsEquiv fromInt fromInt-toInt toInt-fromInt

toInt-pos : (n : ℕ) → toInt (pos n) ≡ Int.pos n
toInt-pos ℕ.zero = refl
toInt-pos (ℕ.suc n) = ap Int.sucInt (toInt-pos n)

pos-IsInjective : IsInjective pos
pos-IsInjective {m} {n} p = Int.injPos (sym (toInt-pos m) ∙ ap toInt p ∙ toInt-pos n)

IsNonnegative : ℤ → Type₀
IsNonnegative z = Σ[ n ∈ ℕ ] pos n ≡ z

IsNonnegative-IsProp : ∀ z → IsProp (IsNonnegative z)
IsNonnegative-IsProp = IsInjective→fiber-IsProp ℕ-IsSet ℤ-IsSet pos-IsInjective

IsNonnegative-Dec : ∀ z → Dec (IsNonnegative z)
IsNonnegative-Dec z = subst (λ z → Dec (IsNonnegative z)) (fromInt-toInt z) (fromInt-IsNonnegative-Dec (toInt z))
  where
  fromInt-IsNonnegative-Dec : ∀ i → Dec (IsNonnegative (fromInt i))
  fromInt-IsNonnegative-Dec (Int.pos n) = yes (n , IsEquiv→IsInjective toInt-IsEquiv (toInt-pos n ∙ sym (toInt-fromInt _)))
  fromInt-IsNonnegative-Dec (Int.negsuc n) = no λ { (m , p) → Int.posNotnegsuc m n (sym (toInt-pos _) ∙ ap toInt p ∙ toInt-fromInt (Int.negsuc n)) }

_≤_ : ℤ → ℤ → Type₀
m ≤ n = IsNonnegative (n - m)

≤-IsProp : ∀ m n → IsProp (m ≤ n)
≤-IsProp m n = IsNonnegative-IsProp (n - m)

≤-Dec : ∀ m n → Dec (m ≤ n)
≤-Dec m n = IsNonnegative-Dec (n - m)

_<_ : ℤ → ℤ → Type₀
m < n = suc m ≤ n

<-IsProp : ∀ m n → IsProp (m < n)
<-IsProp m n = ≤-IsProp (suc m) n

<-Dec : ∀ m n → Dec (m < n)
<-Dec m n = ≤-Dec (suc m) n

open import Cubical.Data.Nat.Literals public

instance
  fromNatInt : HasFromNat ℤ
  fromNatInt = record { Constraint = λ _ → ⊤ ; fromNat = λ n → pos n }

instance
  fromNegInt : HasFromNeg ℤ
  fromNegInt = record { Constraint = λ _ → ⊤ ; fromNeg = λ n → neg n }
