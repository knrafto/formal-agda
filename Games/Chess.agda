{-# OPTIONS --cubical #-}
module Games.Chess where

open import Math.Fin
open import Math.Type

Rank : Type₀
Rank = Fin 8

File : Type₀
File = Fin 8

Square : Type₀
Square = Rank × File

data Player : Type₀ where
  white : Player
  black : Player

data PieceType : Type₀ where
  king   : PieceType
  queen  : PieceType
  rook   : PieceType
  knight : PieceType
  pawn   : PieceType
