module Experimental.Order where

open import Math.Dec
open import Math.Fin
open import Math.Function
open import Math.Nat renaming (_<_ to _<ℕ_)
open import Math.Type

Rel : Type₀ → Type₁
Rel A = A → A → Type₀

IsOrdSet : (A : Type₀) → Rel A → Type₀
IsOrdSet A _<_
  = IsSet A
  × (∀ {a b} → IsProp (a < b))
  × (∀ {a} → ¬ (a < a))
  × (∀ {a b c} → a < b → b < c → a < c)

ℕ-IsOrdSet : IsOrdSet ℕ _<ℕ_
ℕ-IsOrdSet = ℕ-IsSet , <-IsProp , <-irrefl , <-trans

_<Fin_ : ∀ {n} → Rel (Fin n)
i <Fin j = toℕ i <ℕ toℕ j

Fin-IsOrdSet : ∀ {n} → IsOrdSet (Fin n) _<Fin_
Fin-IsOrdSet = Fin-IsSet , <-IsProp , <-irrefl , <-trans

IsMonotone : {A B : Type₀} → Rel A → Rel B → (A → B) → Type₀
IsMonotone _<A_ _<B_ f = ∀ {a b} → a <A b → f a <B f b

-- TODO: IsOrdIso?
IsOrderIso : {A B : Type₀} → Rel A → Rel B → (A → B) → Type₀
IsOrderIso _<A_ _<B_ f = IsMonotone _<A_ _<B_ f × IsEquiv f

IsFinOrdSet : (A : Type₀) → Rel A → Type₀
IsFinOrdSet A _<_ = Σ[ n ∈ ℕ ] Σ[ f ∈ (Fin n → A) ] IsOrderIso _<Fin_ _<_ f

_<Σ_ : {A : Type₀} {P : A → Type₀} → Rel A → Rel (Σ[ a ∈ A ] P a)
_<Σ_ _<_ (a , _) (b , _) = a < b

Σ-IsFinOrdSet : {A : Type₀} {P : A → Type₀} (_<_ : Rel A)
  → (∀ a → IsProp (P a)) → (∀ a → Dec (P a)) → IsFinOrdSet (Σ[ a ∈ A ] P a) (_<Σ_ _<_)
Σ-IsFinOrdSet _<_ P-IsProp P-Dec = {!!}
