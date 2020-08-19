{-# OPTIONS --cubical #-}
module Experimental.Binary where

open import Math.Dec
open import Math.Fin
open import Math.Function
open import Math.Int renaming (_+_ to _+ℤ_; _<_ to _<ℤ_; _≤_ to _≤ℤ_)
open import Math.Nat
open import Math.Vec
open import Math.Type

infixr 5 _++_

-- A bit.
data Bit : Type₀ where
  0₂ : Bit
  1₂ : Bit

-- A sequence of bits.
Word : ℕ → Type₀
Word b = Vec b Bit

-- Concatenation of two bit-vectors. Concatenation is big-endian, like Verilog.
_++_ : ∀ {b₁ b₂} → Word b₁ → Word b₂ → Word (b₂ + b₁)
x ++ y = concat (y , x)

-- Bit-selection.
slice : ∀ {n} → Word n → (j i : ℕ) → {True (<-Dec j n)} → {i≤j : True (≤-Dec i j)} → Word (suc (difference (witness i≤j)))
slice {n} w j i {j<n} {i≤n} (k , k<sl) = w (k + i , <≤-trans k+i<sj (witness j<n))
  where
  k+i<sj : k + i < suc j
  k+i<sj = subst (λ x → k + i < suc x) (snd (witness i≤n)) (<-+k k<sl)

and : Bit → Bit → Bit
and 0₂ _ = 0₂
and 1₂ y = y

or : Bit → Bit → Bit
or 0₂ y = y
or 1₂ _ = 1₂

xor : Bit → Bit → Bit
xor 0₂ 0₂ = 0₂
xor 0₂ 1₂ = 1₂
xor 1₂ 0₂ = 1₂
xor 1₂ 1₂ = 0₂

bitwiseAnd : ∀ {b} → Word b → Word b → Word b
bitwiseAnd x y = λ i → and (x i) (y i)

bitwiseOr : ∀ {b} → Word b → Word b → Word b
bitwiseOr x y = λ i → or (x i) (y i)

bitwiseXor : ∀ {b} → Word b → Word b → Word b
bitwiseXor x y = λ i → xor (x i) (y i)

Unsigned : ℕ → Type₀
Unsigned b = Fin (2 ^ b)

toUnsigned : ∀ {b} → Word b → Unsigned b
toUnsigned = {!!}

toUnsigned-IsEquiv : ∀ {b} → IsEquiv (toUnsigned {b = b})
toUnsigned-IsEquiv = {!!}

fromUnsigned : ∀ {b} → Unsigned b → Word b
fromUnsigned = inv toUnsigned-IsEquiv

Signed : ℕ → Type₀
Signed b = Σ[ n ∈ ℤ ] (neg (2 ^ b) ≤ℤ n) × (n <ℤ pos (2 ^ b))

toSigned : ∀ {b} → Word (suc b) → Signed b
toSigned = {!!}

toSigned-IsEquiv : ∀ {b} → IsEquiv (toSigned {b = b})
toSigned-IsEquiv = {!!}

fromSigned : ∀ {b} → Signed b → Word (suc b)
fromSigned = inv toSigned-IsEquiv

constant : ∀ {b} (n : ℕ) → {True (<-Dec n (2 ^ b))} → Word b
constant n {n<2^b} = fromUnsigned (n , witness n<2^b)

zeroExtend : ∀ {b i} → Word b → Word (b + i)
zeroExtend = {!!}

signExtend : ∀ {b i} → Word (suc b) → Word (suc b + i)
signExtend {b} {i} = {!!}

add : ∀ {b} → Word (suc b) → Word (suc b) → Word (suc (suc b))
add {b} w₁ w₂ =
  let (x , -2^b≤x , x<2^b) = toSigned w₁
      (y , -2^b≤y , y<2^b) = toSigned w₂
  in fromSigned (x +ℤ y , {!!} , {!!})

test : ∀ {b} → 2 ^ suc b ≡ 2 ^ b + 2 ^ b
test = refl

sub : ∀ {b} → Word b → Word b → Word b
sub = {!!}
