{-# OPTIONS --cubical #-}
module Math.Fin where

open import Cubical.Data.Fin public using (Fin; toℕ; fzero; fsuc)

open import Math.Type

private
  variable
    ℓ : Level
