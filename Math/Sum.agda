{-# OPTIONS --cubical #-}
module Math.Sum where

open import Cubical.Data.Sum using (isOfHLevelSum)

open import Math.Type

private
  variable
    ℓ ℓ′ ℓ″ ℓ‴ : Level
    A : Type ℓ
    B : Type ℓ′
    C : Type ℓ″

⊎-IsSet : IsSet A → IsSet B → IsSet (A ⊎ B)
⊎-IsSet = isOfHLevelSum 0
