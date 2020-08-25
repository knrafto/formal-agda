{-# OPTIONS --cubical --allow-unsolved-metas #-}
module Math.Binary where

open import Math.Bit hiding (toℕ; toℕ-IsInjective)
import Math.Bit as Bit
open import Math.Dec
open import Math.Fin hiding (toℕ; toℕ-IsInjective)
import Math.Fin as Fin
open import Math.Function
open import Math.Int using (ℤ; ℤ-IsSet; pos; neg) renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; _<_ to _<ℤ_; _*_ to _*ℤ_; <-Dec to <ℤ-Dec; _≤_ to _≤ℤ_; ≤-Dec to ≤ℤ-Dec)
import Math.Int as ℤ
import Math.IntDivision as ℤ
open import Math.Mod using (Mod) renaming (_+_ to _+Mod_; _-_ to _-Mod_; _*_ to _*Mod_)
import Math.Mod as Mod
open import Math.Nat
import Math.Nat as ℕ
import Math.NatDivision as ℕ
open import Math.Prod
open import Math.Vec
open import Math.Type

infixr 5 _++_

-- A bit vector.
Word : ℕ → Type₀
Word n = Vec n Bit

Byte : Type₀
Byte = Word 8

Word-IsSet : ∀ {n} → IsSet (Word n)
Word-IsSet = Vec-IsSet Bit-IsSet

Word-HasDecEq : ∀ {n} → HasDecEq (Word n)
Word-HasDecEq = Vec-HasDecEq Bit-HasDecEq

_++_ : ∀ {m n} → Word m → Word n → Word (n + m)
x ++ y = concat (y , x)

slice : ∀ {n} → Word n → (j i : ℕ) → {True (<-Dec j n)} → {i≤j : True (≤-Dec i j)} → Word (suc (difference (witness i≤j)))
slice {n} w j i {j<n} {i≤j} (k , k<sl) = w (k + i , <≤-trans k+i<sj (witness j<n))
  where
  k+i<sj : k + i < suc j
  k+i<sj = subst (λ x → k + i < suc x) (snd (witness i≤j)) (<-+k k<sl)

0<1 : 0 < 1
0<1 = (0 , refl)

0<2 : 0 < 2
0<2 = (1 , refl)

0<2^n : (n : ℕ) → 0 < 2 ^ n
0<2^n zero = 0<1
0<2^n (suc n) = <≤-trans (0<2^n n) (subst (_≤ 2 ^ n * 2) (*-1 (2 ^ n)) (≤-k* {k = 2 ^ n} (1 , refl)))

--------------------------------------------------------------------------------
-- Bitwise operations
--------------------------------------------------------------------------------

bitwiseAnd : ∀ {n} → Word n → Word n → Word n
bitwiseAnd x y = λ i → and (x i) (y i)

bitwiseOr : ∀ {n} → Word n → Word n → Word n
bitwiseOr x y = λ i → or (x i) (y i)

bitwiseXor : ∀ {n} → Word n → Word n → Word n
bitwiseXor x y = λ i → xor (x i) (y i)

--------------------------------------------------------------------------------
-- Unsigned integer representation
--------------------------------------------------------------------------------

toℕ : ∀ {n} → Word n → ℕ
toℕ {zero}  w = 0
toℕ {suc n} w = toℕ (tail w) * 2 + Bit.toℕ (head w)

toℕ-IsInjective : ∀ {n} → IsInjective (toℕ {n = n})
toℕ-IsInjective {zero} = λ _ → IsContr→IsProp Vec0-IsContr _ _
toℕ-IsInjective {suc n} =
  ℕ.euclid-IsInjective 0<2 ∘-IsInjective
  ×-map-IsInjective toℕ-IsInjective (IsEquiv→IsInjective toFin2-IsEquiv) ∘-IsInjective
  IsEquiv→IsInjective ×-swap-IsEquiv ∘-IsInjective
  IsEquiv→IsInjective uncons-IsEquiv

toℕ-<2^n : ∀ {n} (w : Word n) → toℕ w < 2 ^ n
toℕ-<2^n {zero} w = 0<1
toℕ-<2^n {suc n} w = ℕ.euclid-< 0<2 (toℕ (tail w)) (toFin2 (head w)) (toℕ-<2^n (tail w))

Unsigned : ℕ → Type₀
Unsigned n = Fin (2 ^ n)

toUnsigned : ∀ {n} → Word n → Unsigned n
toUnsigned w = toℕ w , toℕ-<2^n w

toUnsigned-IsEquiv : ∀ {n} → IsEquiv (toUnsigned {n = n})
toUnsigned-IsEquiv {zero} = IsContr→IsContr→IsEquiv Vec0-IsContr Fin1-IsContr
toUnsigned-IsEquiv {suc n} = addBit-IsEquiv ∘-IsEquiv ×-map-IsEquiv toFin2-IsEquiv toUnsigned-IsEquiv ∘-IsEquiv uncons-IsEquiv
  where
  addBit : Fin 2 × Unsigned n → Unsigned (suc n)
  addBit (r , (q , q<2^n)) = ℕ.euclid 0<2 (q , r) , ℕ.euclid-< 0<2 q r q<2^n

  removeBit : Unsigned (suc n) → Fin 2 × Unsigned n
  removeBit (m , m<2^sn) = ℕ.remainder 0<2 m , ℕ.quotient 0<2 m , ℕ.quotient-< 0<2 m<2^sn

  removeBit-addBit : ∀ x → removeBit (addBit x) ≡ x
  removeBit-addBit (r , (q , _)) = ×≡ (ap snd (leftInv (ℕ.euclid-IsEquiv 0<2) (q , r)) , ΣProp≡ (λ _ → <-IsProp) (ap fst (leftInv (ℕ.euclid-IsEquiv 0<2) (q , r))))

  addBit-removeBit : ∀ x → addBit (removeBit x) ≡ x
  addBit-removeBit (m , _) = Fin.toℕ-IsInjective (rightInv (ℕ.euclid-IsEquiv 0<2) m)

  addBit-IsEquiv : IsEquiv addBit
  addBit-IsEquiv = HasInverse→IsEquiv removeBit removeBit-addBit addBit-removeBit

fromUnsigned : ∀ {n} → Unsigned n → Word n
fromUnsigned = inv toUnsigned-IsEquiv

constant : ∀ {n} (k : ℕ) → {True (<-Dec k (2 ^ n))} → Word n
constant k {k<2^n} = fromUnsigned (k , witness k<2^n)

toℕ-replicate-0₂ : ∀ n → toℕ (replicate n 0₂) ≡ 0
toℕ-replicate-0₂ zero = refl
toℕ-replicate-0₂ (suc n) = ap (λ n → n * 2 + 0) (toℕ-replicate-0₂ n)

--------------------------------------------------------------------------------
-- Signed integer representation (two's complement)
--------------------------------------------------------------------------------

toℤ : ∀ {n} → Word (suc n) → ℤ
toℤ {zero} w = neg (Bit.toℕ (head w))
toℤ {suc n} w = toℤ (tail w) *ℤ 2 +ℤ pos (Bit.toℕ (head w))

toℤ-IsInjective : ∀ {n} → IsInjective (toℤ {n = n})
toℤ-IsInjective {zero} = ℤ.neg-IsInjective ∘-IsInjective Bit.toℕ-IsInjective ∘-IsInjective IsEquiv→IsInjective (inv-IsEquiv singleton-IsEquiv)
toℤ-IsInjective {suc n} =
  ℤ.euclid-IsInjective 0<2 ∘-IsInjective
  ×-map-IsInjective toℤ-IsInjective (IsEquiv→IsInjective toFin2-IsEquiv) ∘-IsInjective
  IsEquiv→IsInjective ×-swap-IsEquiv ∘-IsInjective
  IsEquiv→IsInjective uncons-IsEquiv

-2^n≤-toℤ : ∀ {n} (w : Word (suc n)) → neg (2 ^ n) ≤ℤ toℤ w
-2^n≤-toℤ {zero} w = ℤ.neg-≤ (ℕ.suc-reflects-≤ (snd (toFin2 (head w))))
-2^n≤-toℤ {suc n} w = subst (_≤ℤ toℤ w) (ℤ.neg-*-pos (2 ^ n) 2) (ℤ.≤-euclid 0<2 (toℤ (tail w)) (toFin2 (head w)) (-2^n≤-toℤ (tail w)))

toℤ-<2^n : ∀ {n} (w : Word (suc n)) → toℤ w <ℤ pos (2 ^ n)
toℤ-<2^n {zero} w = ℤ.suc-preserves-≤ (ℤ.neg-≤-zero (Bit.toℕ (head w)))
toℤ-<2^n {suc n} w = subst (toℤ w <ℤ_) (sym (ℤ.pos-* (2 ^ n) 2)) (ℤ.euclid-< 0<2 (toℤ (tail w)) (toFin2 (head w)) (toℤ-<2^n (tail w)))

Signed : ℕ → Type₀
Signed n = Σ[ k ∈ ℤ ] (neg (2 ^ n) ≤ℤ k) × (k <ℤ pos (2 ^ n))

toSigned : ∀ {n} → Word (suc n) → Signed n
toSigned w = toℤ w , -2^n≤-toℤ w , toℤ-<2^n w

toSigned-IsEquiv : ∀ {n} → IsEquiv (toSigned {n = n})
toSigned-IsEquiv {zero} = toSigned0-IsEquiv ∘-IsEquiv toFin2-IsEquiv ∘-IsEquiv inv-IsEquiv singleton-IsEquiv
  where
  toSigned0 : Fin 2 → Signed 0
  toSigned0 (i , i<2) = neg i , ℤ.neg-≤ (ℕ.suc-reflects-≤ i<2) , ℤ.suc-preserves-≤ (ℤ.neg-≤-zero i)

  toSigned0-IsInjective : IsInjective toSigned0
  toSigned0-IsInjective p = Fin.toℕ-IsInjective (ℤ.neg-IsInjective (ap fst p))

  toSigned0-IsSurjective : IsSurjective toSigned0
  toSigned0-IsSurjective x@(m , -1≤m , m<1) = case ℤ.sign (ℤ.negate m) return fiber toSigned0 x of λ
    { (inl (i , posi≡negatem)) →
      let i<2 : i < 2
          i<2 = ℤ.pos-≤-inv (ℤ.suc-preserves-≤ (subst (_≤ℤ 1) (sym posi≡negatem) (ℤ.negate-≤ -1≤m)))
      in (i , i<2) , ΣProp≡ (λ _ → ×-IsProp ℤ.≤-IsProp ℤ.<-IsProp) (ap ℤ.negate posi≡negatem ∙ ℤ.negate-negate m)
    ; (inr (i , negsuci≡negatem)) →
      let i<0 : i < 0
          i<0 = ℤ.pos-≤-inv (ℤ.suc-reflects-≤ (subst (_<ℤ 1) (sym (IsEquiv→IsInjective ℤ.negate-IsEquiv negsuci≡negatem)) m<1))
      in ⊥-rec (¬-<-zero i<0)
    }

  toSigned0-IsEquiv : IsEquiv toSigned0
  toSigned0-IsEquiv = IsInjective×IsSurjective→IsEquiv Fin-IsSet (Σ-IsSet ℤ-IsSet (λ _ → IsProp→IsSet (×-IsProp ℤ.≤-IsProp ℤ.<-IsProp))) toSigned0-IsInjective toSigned0-IsSurjective

toSigned-IsEquiv {suc n} = addBit-IsEquiv ∘-IsEquiv ×-map-IsEquiv toFin2-IsEquiv toSigned-IsEquiv ∘-IsEquiv uncons-IsEquiv
  where
  addBit : Fin 2 × Signed n → Signed (suc n)
  addBit (r , (q , -2^n≤q , q<2^n)) =
    ℤ.euclid 0<2 (q , r) ,
    subst (_≤ℤ ℤ.euclid 0<2 (q , r)) (ℤ.neg-*-pos (2 ^ n) 2) (ℤ.≤-euclid 0<2 q r -2^n≤q) ,
    subst (ℤ.euclid 0<2 (q , r) <ℤ_) (sym (ℤ.pos-* (2 ^ n) 2)) (ℤ.euclid-< 0<2 q r q<2^n)

  removeBit : Signed (suc n) → Fin 2 × Signed n
  removeBit (m , -2^n≤m , m<2^n) =
    ℤ.remainder 0<2 m ,
     (ℤ.quotient 0<2 m ,
      ℤ.≤-quotient 0<2 (subst (_≤ℤ m) (sym (ℤ.neg-*-pos (2 ^ n) 2)) -2^n≤m) ,
      ℤ.quotient-< 0<2 (subst (m <ℤ_) (ℤ.pos-* (2 ^ n) 2) m<2^n))

  removeBit-addBit : ∀ x → removeBit (addBit x) ≡ x
  removeBit-addBit (r , (q , _)) = ×≡ (ap snd (leftInv (ℤ.euclid-IsEquiv 0<2) (q , r)) , ΣProp≡ (λ _ → ×-IsProp ℤ.≤-IsProp ℤ.<-IsProp) (ap fst (leftInv (ℤ.euclid-IsEquiv 0<2) (q , r))))

  addBit-removeBit : ∀ x → addBit (removeBit x) ≡ x
  addBit-removeBit (m , _) = ΣProp≡ (λ _ → ×-IsProp ℤ.≤-IsProp ℤ.<-IsProp) (rightInv (ℤ.euclid-IsEquiv 0<2) m)

  addBit-IsEquiv : IsEquiv addBit
  addBit-IsEquiv = HasInverse→IsEquiv removeBit removeBit-addBit addBit-removeBit

fromSigned : ∀ {n} → Signed n → Word (suc n)
fromSigned = inv toSigned-IsEquiv

signBit : ∀ {n} → Word (suc n) → Bit
signBit = last

signBit≡0₂ : ∀ {n} (w : Word (suc n)) → last w ≡ 0₂ → 0 ≤ℤ toℤ w
signBit≡0₂ {zero} w s≡0₂ = subst (0 ≤ℤ_) (ap (neg ∘ Bit.toℕ) (sym s≡0₂)) ℤ.≤-refl
signBit≡0₂ {suc n} w s≡0₂ = ℤ.≤-euclid 0<2 (toℤ (tail w)) (Bit.toFin2 (head w)) (signBit≡0₂ (tail w) (last-tail w ∙ s≡0₂))

signBit≡1₂ : ∀ {n} (w : Word (suc n)) → last w ≡ 1₂ → toℤ w <ℤ 0
signBit≡1₂ {zero} w s≡1₂ = subst (_<ℤ 0) (ap (neg ∘ Bit.toℕ) (sym s≡1₂)) (0 , rightInv ℤ.suc-IsEquiv 0)
signBit≡1₂ {suc n} w s≡1₂ = ℤ.euclid-< 0<2 (toℤ (tail w)) (Bit.toFin2 (head w)) (signBit≡1₂ (tail w) (last-tail w ∙ s≡1₂))

toℤ-replicate : ∀ n b → toℤ (replicate (suc n) b) ≡ neg (Bit.toℕ b)
toℤ-replicate zero b = refl
toℤ-replicate (suc n) b =
  ap (λ n → n *ℤ 2 +ℤ pos (Bit.toℕ b)) (toℤ-replicate n b) ∙
  ap (_+ℤ pos (Bit.toℕ b)) (n*2≡n+n (neg (Bit.toℕ b))) ∙
  rightInv (ℤ.+n-IsEquiv (pos (Bit.toℕ b))) (neg (Bit.toℕ b))
  where
  n*2≡n+n : ∀ n → n *ℤ 2 ≡ n +ℤ n
  n*2≡n+n n = ℤ.*-comm n 2 ∙ ap (n +ℤ_) (ℤ.+-zero n)

--------------------------------------------------------------------------------
-- Modular representation
--------------------------------------------------------------------------------

toMod : ∀ {n} → Word n → Mod (2 ^ n)
toMod {n} w = Mod.fromℕ {d = 2 ^ n} (toℕ w)

toMod-IsEquiv : ∀ {n} → IsEquiv (toMod {n = n})
toMod-IsEquiv {n} = Mod.fromFin-IsEquiv (0<2^n n) ∘-IsEquiv toUnsigned-IsEquiv

fromMod : ∀ {n} → Mod (2 ^ n) → Word n
fromMod = inv toMod-IsEquiv

--------------------------------------------------------------------------------
-- Extension
--------------------------------------------------------------------------------

zeroExtend : ∀ {m} n → Word m → Word (m + n)
zeroExtend {m} n w = replicate n 0₂ ++ w

zeroExtend-toℕ : ∀ {m} n (w : Word m) → toℕ (zeroExtend n w) ≡ toℕ w
zeroExtend-toℕ {zero} n w = {!!}
zeroExtend-toℕ {suc m} n w = ap (λ n → n * 2 + Bit.toℕ (head w)) (ap toℕ (tail-concat w (replicate n 0₂)) ∙ zeroExtend-toℕ n (tail w))

signExtend : ∀ {m} n → Word (suc m) → Word (suc m + n)
signExtend {m} n w = replicate n (signBit w) ++ w

signExtend-toℤ : ∀ {m} n (w : Word (suc m)) → toℤ (signExtend n w) ≡ toℤ w
signExtend-toℤ {zero} n w = ap toℤ lemma ∙ toℤ-replicate n (signBit w)
  where
  lemma : signExtend n w ≡ replicate (suc n) (signBit w)
  lemma = {!!}

signExtend-toℤ {suc m} n w = ap (λ n → n *ℤ 2 +ℤ pos (Bit.toℕ (head w))) (ap toℤ tail-signExtend ∙ signExtend-toℤ n (tail w))
  where
  tail-signExtend : tail (signExtend n w) ≡ signExtend n (tail w)
  tail-signExtend = tail-concat w (replicate n (signBit w)) ∙ ap (λ b → replicate n b ++ tail w) (sym (last-tail w))

--------------------------------------------------------------------------------
-- Shifts
--------------------------------------------------------------------------------

shiftLeftOnce : ∀ {m} → Word m → Word m
shiftLeftOnce w = tail (cons (0₂ , w))

shiftLeft : ∀ {m n} → Word m → Word n → Word m
shiftLeft w shamt = iterate (toℕ shamt) shiftLeftOnce w

shiftLeft-*2^n : ∀ {m n} (w : Word m) (shamt : Word n) → toMod (shiftLeft w shamt) ≡ Mod.fromℕ {d = 2 ^ m} (toℕ w * 2 ^ toℕ shamt)
shiftLeft-*2^n = {!!}

shiftRightOnce : ∀ {m} → Word m → Word m
shiftRightOnce w = init (snoc (w , 0₂))

shiftRight : ∀ {m n} → Word m → Word n → Word m
shiftRight w shamt = iterate (toℕ shamt) shiftRightOnce w

shiftRight-/2^n : ∀ {m n} (w : Word m) (shamt : Word n) → toℕ (shiftRight w shamt) ≡ ℕ.quotient (0<2^n (toℕ shamt)) (toℕ w)
shiftRight-/2^n = {!!}

shiftRightArithmeticOnce : ∀ {m} → Word (suc m) → Word (suc m)
shiftRightArithmeticOnce w = init (snoc (w , signBit w))

shiftRightArithmetic : ∀ {m n} → Word (suc m) → Word n → Word (suc m)
shiftRightArithmetic w shamt = iterate (toℕ shamt) shiftRightArithmeticOnce w

shiftRightArithmetic-/2^n : ∀ {m n} (w : Word (suc m)) (shamt : Word n) → toℤ (shiftRightArithmetic w shamt) ≡ ℤ.quotient (0<2^n (toℕ shamt)) (toℤ w)
shiftRightArithmetic-/2^n = {!!}

--------------------------------------------------------------------------------
-- Arithmetic
--------------------------------------------------------------------------------

add : ∀ {n} → Word n → Word n → Word n
add {n} x y = fromMod (_+Mod_ {d = 2 ^ n} (toMod x) (toMod y))

sub : ∀ {n} → Word n → Word n → Word n
sub {n} x y = fromMod (_-Mod_ {d = 2 ^ n} (toMod x) (toMod y))

--------------------------------------------------------------------------------
-- Comparison
--------------------------------------------------------------------------------

decide : ∀ {ℓ} {P : Type ℓ} → Dec P → Word 1
decide (yes p) = λ _ → 1₂
decide (no ¬p) = λ _ → 0₂

decideEq : ∀ {n} → Word n → Word n → Word 1
decideEq x y = decide (Word-HasDecEq x y)

decideNe : ∀ {n} → Word n → Word n → Word 1
decideNe x y = decide (¬-Dec (Word-HasDecEq x y))

decideLt : ∀ {n} → Word (suc n) → Word (suc n) → Word 1
decideLt x y = decide (<ℤ-Dec (toℤ x) (toℤ y))

decideLtUnsigned : ∀ {n} → Word n → Word n → Word 1
decideLtUnsigned x y = decide (<-Dec (toℕ x) (toℕ y))

decideGe : ∀ {n} → Word (suc n) → Word (suc n) → Word 1
decideGe x y = decide (≤ℤ-Dec (toℤ y) (toℤ x))

decideGeUnsigned : ∀ {n} → Word n → Word n → Word 1
decideGeUnsigned x y = decide (≤-Dec (toℕ y) (toℕ x))

