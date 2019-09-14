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
continuationByte bs = concat (bs , 2-vector 0₂ 1₂)

encode1Byte : Fin 0x0080 → List Byte
encode1Byte n = concat (digits , 1-vector 0₂) ∷ []
  where
  digits : Vec 7 Bit
  digits = toBits n

encode2Bytes : Fin 0x0800 → List Byte
encode2Bytes n = concat (snd splitDigits , 3-vector 0₂ 1₂ 1₂) ∷ continuationByte (fst splitDigits) ∷ []
  where
  digits : Vec 11 Bit
  digits = toBits n

  splitDigits : Vec 6 Bit × Vec 5 Bit
  splitDigits = split digits

encode3Bytes : Fin 0x10000 → List Byte
encode3Bytes n = concat (snd splitDigits₁ , 4-vector 0₂ 1₂ 1₂ 1₂) ∷ continuationByte (fst splitDigits₁) ∷ continuationByte (fst splitDigits₀)  ∷ []
  where
  digits : Vec 16 Bit
  digits = toBits n

  splitDigits₀ : Vec 6 Bit × Vec 10 Bit
  splitDigits₀ = split digits

  splitDigits₁ : Vec 6 Bit × Vec 4 Bit
  splitDigits₁ = split (snd splitDigits₀)

encode4Bytes : Fin 0x200000 → List Byte
encode4Bytes n = concat (snd splitDigits₂ , 5-vector 0₂ 1₂ 1₂ 1₂ 1₂)
  ∷ continuationByte (fst splitDigits₂) ∷ continuationByte (fst splitDigits₁) ∷ continuationByte (fst splitDigits₀) ∷ []
  where
  digits : Vec 21 Bit
  digits = toBits n

  splitDigits₀ : Vec 6 Bit × Vec 15 Bit
  splitDigits₀ = split digits

  splitDigits₁ : Vec 6 Bit × Vec 9 Bit
  splitDigits₁ = split (snd splitDigits₀)

  splitDigits₂ : Vec 6 Bit × Vec 3 Bit
  splitDigits₂ = split (snd splitDigits₁)

encodeChar : Char → List Byte
encodeChar (n , _) with <-Dec n 0x0080 | <-Dec n 0x0800 | <-Dec n 0x10000
encodeChar (n , _) | yes p | _ | _ = encode1Byte (n , p)
encodeChar (n , _) | no _ | yes p | _ = encode2Bytes (n , p)
encodeChar (n , _) | no _ | no _ | yes p = encode3Bytes (n , p)
encodeChar (n , isValid) | no _ | no _ | no _  = encode4Bytes (n , ≤<-trans (fst isValid) 0x10FFFF<0x200000)
  where
  0x10FFFF<0x200000 : 0x10FFFF < 0x200000
  0x10FFFF<0x200000 = (0xF0000 , refl)
