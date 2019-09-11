{-# OPTIONS --cubical #-}
module Math.Decidable where

open import Cubical.Relation.Nullary public using (Dec; yes; no) renaming (isPropDec to Dec-IsProp)
