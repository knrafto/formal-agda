{-# OPTIONS --cubical #-}
module Unicode.Char where

open import Math.Nat
open import Math.Type

IsSurrogateCodePoint : ℕ → Type₀
IsSurrogateCodePoint n = (0xD800 ≤ n) × (n ≤ 0xDFFF)

IsValidCodePoint : ℕ → Type₀
IsValidCodePoint n = (n ≤ 0x10FFFF) × (¬ IsSurrogateCodePoint n)

Char : Type₀
Char = Σ ℕ IsValidCodePoint

codePoint : Char → ℕ
codePoint = fst
