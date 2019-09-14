{-# OPTIONS --cubical #-}
module Unicode.Utf8 where

open import Math.Bit
open import Math.Decidable
open import Math.Fin
open import Math.Function
open import Math.List
open import Math.Nat
open import Math.Prod
open import Math.Type
open import Math.Vec
open import Unicode.Char

leadingByte1 : Vec 7 Bit → Byte
leadingByte1 bs = concat (1-vector 0₂ , bs)

leadingByte2 : Vec 5 Bit → Byte
leadingByte2 bs = concat (3-vector 1₂ 1₂ 0₂ , bs)

leadingByte3 : Vec 4 Bit → Byte
leadingByte3 bs = concat (4-vector 1₂ 1₂ 1₂ 0₂ , bs)

leadingByte4 : Vec 3 Bit → Byte
leadingByte4 bs = concat (5-vector 1₂ 1₂ 1₂ 1₂ 0₂ , bs)

continuationByte : Vec 6 Bit → Byte
continuationByte bs = concat (2-vector 1₂ 0₂ , bs)

encode1Byte : Fin 0x0080 → List Byte
encode1Byte = List-singleton ∘ leadingByte1 ∘ toBits

encode2Bytes : Fin 0x0800 → List Byte
encode2Bytes =
  List-cons ∘ ×-map leadingByte2 (List-singleton ∘ continuationByte) ∘ split ∘ toBits

encode3Bytes : Fin 0x10000 → List Byte
encode3Bytes =
  List-cons ∘ ×-map leadingByte3
    (List-cons ∘ ×-map continuationByte
      (List-singleton ∘ continuationByte) ∘ split) ∘ split ∘ toBits

encode4Bytes : Fin 0x200000 → List Byte
encode4Bytes =
  List-cons ∘ ×-map leadingByte4
    (List-cons ∘ ×-map continuationByte
      (List-cons ∘ ×-map continuationByte
        (List-singleton ∘ continuationByte) ∘ split) ∘ split) ∘ split ∘ toBits

encodeChar : Char → List Byte
encodeChar (n , _) with <-Dec n 0x0080 | <-Dec n 0x0800 | <-Dec n 0x10000
encodeChar (n , _) | yes p | _ | _ = encode1Byte (n , p)
encodeChar (n , _) | no _ | yes p | _ = encode2Bytes (n , p)
encodeChar (n , _) | no _ | no _ | yes p = encode3Bytes (n , p)
encodeChar (n , isValid) | no _ | no _ | no _  = encode4Bytes (n , ≤<-trans (fst isValid) 0x10FFFF<0x200000)
  where
  0x10FFFF<0x200000 : 0x10FFFF < 0x200000
  0x10FFFF<0x200000 = (0xF0000 , refl)
