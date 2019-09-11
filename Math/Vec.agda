{-# OPTIONS --cubical #-}
module Math.Vec where

open import Math.Fin
open import Math.Nat
open import Math.Type

private
  variable
    ℓ ℓ′ : Level
    A : Type ℓ

Vec : ℕ → Type ℓ → Type ℓ
Vec n A = Fin n → A

Vec-IsSet : {n : ℕ} → IsSet A → IsSet (Vec n A)
Vec-IsSet A-IsSet = Π-IsSet (λ _ → A-IsSet)

head : {n : ℕ} → Vec (suc n) A → A
head v = v fzero

tail : {n : ℕ} → Vec (suc n) A → Vec n A
tail v = λ i → v (fsuc i)
