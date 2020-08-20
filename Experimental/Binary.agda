{-# OPTIONS --cubical --allow-unsolved-metas #-}
module Experimental.Binary where

open import Math.Dec
open import Math.Fin hiding (toℕ)
open import Math.Function
open import Math.Int renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; _<_ to _<ℤ_; <-Dec to <ℤ-Dec; _≤_ to _≤ℤ_; ≤-Dec to ≤ℤ-Dec)
open import Math.Mod using (Mod) renaming (_+_ to _+Mod_; _-_ to _-Mod_)
import Math.Mod as Mod
open import Math.Nat
open import Math.Vec
open import Math.Type

infixr 5 _++_

-- A bit.
data Bit : Type₀ where
  0₂ : Bit
  1₂ : Bit

Bit-HasDecEq : HasDecEq Bit
Bit-HasDecEq = {!!}

-- A bit vector.
Word : ℕ → Type₀
Word n = Vec n Bit

Word-HasDecEq : ∀ {n} → HasDecEq (Word n)
Word-HasDecEq = Vec-HasDecEq Bit-HasDecEq

_++_ : ∀ {m n} → Word m → Word n → Word (n + m)
x ++ y = concat (y , x)

slice : ∀ {n} → Word n → (j i : ℕ) → {True (<-Dec j n)} → {i≤j : True (≤-Dec i j)} → Word (suc (difference (witness i≤j)))
slice {n} w j i {j<n} {i≤j} (k , k<sl) = w (k + i , <≤-trans k+i<sj (witness j<n))
  where
  k+i<sj : k + i < suc j
  k+i<sj = subst (λ x → k + i < suc x) (snd (witness i≤j)) (<-+k k<sl)

--------------------------------------------------------------------------------
-- Bitwise operations
--------------------------------------------------------------------------------

and : Bit → Bit → Bit
and 0₂ _ = 0₂
and 1₂ y = y

bitwiseAnd : ∀ {n} → Word n → Word n → Word n
bitwiseAnd x y = λ i → and (x i) (y i)

or : Bit → Bit → Bit
or 0₂ y = y
or 1₂ _ = 1₂

bitwiseOr : ∀ {n} → Word n → Word n → Word n
bitwiseOr x y = λ i → or (x i) (y i)

xor : Bit → Bit → Bit
xor 0₂ 0₂ = 0₂
xor 0₂ 1₂ = 1₂
xor 1₂ 0₂ = 1₂
xor 1₂ 1₂ = 0₂

bitwiseXor : ∀ {n} → Word n → Word n → Word n
bitwiseXor x y = λ i → xor (x i) (y i)

--------------------------------------------------------------------------------
-- Unsigned integer representation
--------------------------------------------------------------------------------

Unsigned : ℕ → Type₀
Unsigned n = Fin (2 ^ n)

toUnsigned : ∀ {n} → Word n → Unsigned n
toUnsigned = {!!}

toUnsigned-IsEquiv : ∀ {n} → IsEquiv (toUnsigned {n = n})
toUnsigned-IsEquiv = {!!}

fromUnsigned : ∀ {n} → Unsigned n → Word n
fromUnsigned = inv toUnsigned-IsEquiv

toℕ : ∀ {n} → Word n → ℕ
toℕ w = fst (toUnsigned w)

constant : ∀ {n} (k : ℕ) → {True (<-Dec k (2 ^ n))} → Word n
constant k {k<2^n} = fromUnsigned (k , witness k<2^n)

--------------------------------------------------------------------------------
-- Signed integer representation (two's complement)
--------------------------------------------------------------------------------

Signed : ℕ → Type₀
Signed n = Σ[ k ∈ ℤ ] (neg (2 ^ n) ≤ℤ k) × (k <ℤ pos (2 ^ n))

toSigned : ∀ {n} → Word (suc n) → Signed n
toSigned = {!!}

toSigned-IsEquiv : ∀ {n} → IsEquiv (toSigned {n = n})
toSigned-IsEquiv = {!!}

fromSigned : ∀ {n} → Signed n → Word (suc n)
fromSigned = inv toSigned-IsEquiv

toℤ : ∀ {n} → Word (suc n) → ℤ
toℤ w = {!!}

--------------------------------------------------------------------------------
-- Modular representation
--------------------------------------------------------------------------------

toMod : ∀ {n} → Word n → Mod (2 ^ n)
toMod w = {!!}

toMod-IsEquiv : ∀ {n} → IsEquiv (toMod {n = n})
toMod-IsEquiv = {!!}

fromMod : ∀ {n} → Mod (2 ^ n) → Word n
fromMod = inv toMod-IsEquiv

--------------------------------------------------------------------------------
-- Extension
--------------------------------------------------------------------------------

zeroExtend : ∀ {m n} → Word n → Word (n + m)
zeroExtend w = {!!}

signExtend : ∀ {m n} → Word (suc n) → Word (suc n + m)
signExtend w = {!!}

--------------------------------------------------------------------------------
-- Shifts
--------------------------------------------------------------------------------

shiftLeft : ∀ {m n} → Word n → Word m → Word n
shiftLeft = {!!}

shiftRight : ∀ {m n} → Word n → Word m → Word n
shiftRight = {!!}

shiftRightArithmetic : ∀ {m n} → Word (suc n) → Word m → Word (suc n)
shiftRightArithmetic = {!!}

--------------------------------------------------------------------------------
-- Arithmetic
--------------------------------------------------------------------------------

add : ∀ {n} → Word n → Word n → Word n
add x y = fromMod (toMod x +Mod toMod y)

sub : ∀ {n} → Word n → Word n → Word n
sub x y = fromMod (toMod x -Mod toMod y)

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

