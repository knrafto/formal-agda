-- Modeling error handling via a "Result" monad
-- (e.g. Haskell Either, OCaml Or_error.t, Rust Result, Go err pairs, absl::StatusOr<T>, ...)
module Experimental.Error where

open import Math.Dec
open import Math.Type

Result : Type → Type → Type₁
Result E A = Σ[ P ∈ Type ] IsProp P × Dec P × (¬ P → E) × (P → A)

IsOk : ∀ {E A} → Result E A → Type
IsOk (P , _) = P

IsOk-IsProp : ∀ {E A} → (r : Result E A) → IsProp (IsOk r)
IsOk-IsProp (_ , P-IsProp , _) = P-IsProp

IsOk-Dec : ∀ {E A} → (r : Result E A) → Dec (IsOk r)
IsOk-Dec (_ , _ , P-Dec , _) = P-Dec

error : ∀ {E A} → (r : Result E A) → ¬ IsOk r → E
error (_ , _ , _ , f , _) p = f p

value : ∀ {E A} → (r : Result E A) → IsOk r → A
value (_ , _ , _ , _ , g) p = g p

-- Represents true
return : ∀ {E A} → A → Result E A
return a = ⊤ , ⊤-IsProp , ⊤-Dec , (λ ¬⊤ → ⊥-rec (¬⊤ tt)) , λ _ → a

-- Represents false
throw : ∀ {E A} → E → Result E A
throw e = ⊥ , ⊥-IsProp , ⊥-Dec , (λ _ → e) , ⊥-rec

-- Represents Σ A B (A and B)
bind : ∀ {E A B} → Result E A → (A → Result E B) → Result E B
bind {E = E} {A = A} {B = B} r k = P , P-IsProp , P-Dec , f , g
  where
  P : Type
  P = Σ[ p ∈ IsOk r ] IsOk (k (value r p))

  P-IsProp : IsProp P
  P-IsProp = Σ-IsProp (IsOk-IsProp r) λ p → IsOk-IsProp (k (value r p))

  P-Dec : Dec P
  P-Dec = Σ-Dec (IsOk-IsProp r) (IsOk-Dec r) λ p → IsOk-Dec (k (value r p))

  f : ¬ P → E
  f ¬p with IsOk-Dec r
  f ¬p | yes a with IsOk-Dec (k (value r a))
  f ¬p | yes a | yes b = ⊥-rec (¬p (a , b))
  f ¬p | yes a | no ¬b = error (k (value r a)) ¬b
  f ¬p | no ¬a = error r ¬a

  g : P → B
  g (p , q) = value (k (value r p)) q
