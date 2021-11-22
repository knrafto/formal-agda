module Math.Rat where

-- TODO: Using QuoQ for now, but there might be a better definition.

open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.HITs.Rationals.QuoQ public using (ℚ; _+_; _-_; fromNatℚ)
open import Cubical.HITs.Rationals.QuoQ using ([_/_])
open import Cubical.HITs.Ints.QuoInt renaming (ℤ to QuoInt; pos to QuoInt-pos; neg to QuoInt-neg)
open import Math.Dec
open import Math.Int using (ℤ; fromSigned-IsEquiv)
open import Math.Nat
open import Math.Sum
open import Math.Type

infixl 7 _/_

_/_ : (n : ℤ) (d : ℕ) → {{True (<-Dec 0 d)}} → ℚ
n / suc d = cases fromSigned-IsEquiv
  (λ n → [ QuoInt-pos n / 1+ d ])
  (λ n → [ QuoInt-neg (suc n) / 1+ d ])
  n
