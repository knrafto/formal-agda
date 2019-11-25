{-# OPTIONS --cubical #-}
module Math.Dec where

open import Cubical.Relation.Nullary public using (Dec; yes; no) renaming (isPropDec to Dec-IsProp)
