{-# OPTIONS --cubical #-}
module Unicode.Utf8 where

open import Math.Bit
open import Math.Decidable
open import Math.Fin
open import Math.List
open import Math.Nat
open import Math.Type
open import Math.Vec
open import Unicode.Char

continuationByte : Vec 6 Bit → Byte
continuationByte bs = concat (2-vector 1₂ 0₂ , bs)

encode1Byte : Fin 0x0080 → List Byte
encode1Byte n = concat (1-vector 0₂ , digits) ∷ []
  where
  digits : Vec 7 Bit
  digits = toBits n

encode2Bytes : Fin 0x0800 → List Byte
encode2Bytes n = concat (3-vector 1₂ 1₂ 0₂ , fst splitDigits) ∷ continuationByte (snd splitDigits) ∷ []
  where
  digits : Vec 11 Bit
  digits = toBits n

  splitDigits : Vec 5 Bit × Vec 6 Bit
  splitDigits = split digits

encode3Bytes : Fin 0x10000 → List Byte
encode3Bytes n = concat (4-vector 1₂ 1₂ 1₂ 0₂ , fst splitDigits₁) ∷ continuationByte (snd splitDigits₁) ∷ continuationByte (snd splitDigits₀)  ∷ []
  where
  digits : Vec 16 Bit
  digits = toBits n

  splitDigits₀ : Vec 10 Bit × Vec 6 Bit
  splitDigits₀ = split digits

  splitDigits₁ : Vec 4 Bit × Vec 6 Bit
  splitDigits₁ = split (fst splitDigits₀)

encode4Bytes : Fin 0x200000 → List Byte
encode4Bytes n = concat (5-vector 0₂ 1₂ 1₂ 1₂ 1₂ , fst splitDigits₂)
  ∷ continuationByte (snd splitDigits₂) ∷ continuationByte (snd splitDigits₁) ∷ continuationByte (snd splitDigits₀) ∷ []
  where
  digits : Vec 21 Bit
  digits = toBits n

  splitDigits₀ : Vec 15 Bit × Vec 6 Bit
  splitDigits₀ = split digits

  splitDigits₁ : Vec 9 Bit × Vec 6 Bit
  splitDigits₁ = split (fst splitDigits₀)

  splitDigits₂ : Vec 3 Bit × Vec 6 Bit
  splitDigits₂ = split (fst splitDigits₁)

encodeChar : Char → List Byte
encodeChar (n , _) with <-Dec n 0x0080 | <-Dec n 0x0800 | <-Dec n 0x10000
encodeChar (n , _) | yes p | _ | _ = encode1Byte (n , p)
encodeChar (n , _) | no _ | yes p | _ = encode2Bytes (n , p)
encodeChar (n , _) | no _ | no _ | yes p = encode3Bytes (n , p)
encodeChar (n , isValid) | no _ | no _ | no _  = encode4Bytes (n , ≤<-trans (fst isValid) 0x10FFFF<0x200000)
  where
  0x10FFFF<0x200000 : 0x10FFFF < 0x200000
  0x10FFFF<0x200000 = (0xF0000 , refl)
