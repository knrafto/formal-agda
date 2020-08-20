{-# OPTIONS --cubical --allow-unsolved-metas #-}
module Math.Mod where

open import Agda.Builtin.FromNat
open import Math.Division
open import Math.Fin
open import Math.Function
open import Math.Int using (ℤ)
open import Math.Nat using (ℕ-IsSet; _<_)
import Math.Nat as ℕ
open import Math.Quotient
open import Math.Type

-- TODO: most of this belongs in a Math.Quotient file

-- TODO: d should go on the left?
Mod : ℕ → Type₀
Mod d = ℕ / (λ m n → m ℕ.+ d ≡ n)

module _ {d : ℕ} where
  -- "remainder"
  r : ℕ → Mod d
  r n = [ n ]

  fromℕ : ℕ → Mod d
  fromℕ = r

  fromℤ : ℤ → Mod d
  fromℤ = {!!}

  r-+d : ∀ {m n} → m ℕ.+ d ≡ n → r m ≡ r n
  r-+d {m} {n} = /-≡ m n

  Mod-IsSet : IsSet (Mod d)
  Mod-IsSet = /-IsSet

  Mod-ind-IsProp
    : ∀ {ℓ} {P : Mod d → Type ℓ}
    → (∀ a → IsProp (P a))
    → (f : ∀ a → P (r a))
    → (a : Mod d) → P a
  Mod-ind-IsProp = /-ind-IsProp

  Mod-ind-IsProp-2
    : ∀ {ℓ} {P : Mod d → Mod d → Type ℓ}
    → (∀ a b → IsProp (P a b))
    → (f : ∀ a b → P (r a) (r b))
    → (a b : Mod d) → P a b
  Mod-ind-IsProp-2 P-IsProp f = Mod-ind-IsProp (λ a → Π-IsProp (P-IsProp a)) λ a → Mod-ind-IsProp (P-IsProp _) λ b → f a b

  Mod-ind-IsProp-3
    : ∀ {ℓ} {P : Mod d → Mod d → Mod d → Type ℓ}
    → (∀ a b c → IsProp (P a b c))
    → (f : ∀ a b c → P (r a) (r b) (r c))
    → (a b c : Mod d) → P a b c
  Mod-ind-IsProp-3 P-IsProp f = Mod-ind-IsProp-2 (λ a b → Π-IsProp (P-IsProp a b)) λ a b → Mod-ind-IsProp (P-IsProp _ _) λ c → f a b c

  -- Computes on r: Mod-rec A-IsSet f p (r n) is definitionally equal to f n
  Mod-rec : ∀ {ℓ} {A : Type ℓ} → IsSet A → (f : ℕ → A) → (∀ n → f (n ℕ.+ d) ≡ f n) → Mod d → A
  Mod-rec A-IsSet f p = /-rec A-IsSet f λ a b a~b → sym (p a) ∙ ap f a~b

  -- Recursion on two Mod d arguments
  Mod-rec-2
    : ∀ {ℓ} {A : Type ℓ} → IsSet A → (f : ℕ → ℕ → A)
    → (∀ m n → f (m ℕ.+ d) n ≡ f m n)
    → (∀ m n → f m (n ℕ.+ d) ≡ f m n)
    → Mod d → Mod d → A
  Mod-rec-2 A-IsSet f pl pr = Mod-rec (→-IsSet A-IsSet) (λ m → Mod-rec A-IsSet (λ n → f m n) (pr m))
    λ m → funExt (Mod-ind-IsProp (λ n → A-IsSet _ _) (pl m))

  _+_ : Mod d → Mod d → Mod d
  _+_ = Mod-rec-2 Mod-IsSet (λ m n → r (m ℕ.+ n)) left right
    where
    right : (m n : ℕ) → r (m ℕ.+ (n ℕ.+ d)) ≡ r (m ℕ.+ n)
    right m n = sym (r-+d (sym (ℕ.+-assoc m n d)))

    left : (m n : ℕ) → r ((m ℕ.+ d) ℕ.+ n) ≡ r (m ℕ.+ n)
    left m n = ap r (ℕ.+-comm (m ℕ.+ d) n) ∙ right n m ∙ ap r (ℕ.+-comm n m)

  _-_ : Mod d → Mod d → Mod d
  _-_ = {!!}

  zero : Mod d
  zero = r ℕ.zero

  zero-+ : ∀ n → zero + n ≡ n
  zero-+ = Mod-ind-IsProp (λ _ → Mod-IsSet _ _) λ n → refl

  +-zero : ∀ n → n + zero ≡ n
  +-zero = Mod-ind-IsProp (λ _ → Mod-IsSet _ _) λ n → ap r (ℕ.+-zero n)

  +-comm : ∀ m n → m + n ≡ n + m
  +-comm = Mod-ind-IsProp-2 (λ _ _ → Mod-IsSet _ _) λ m n → ap r (ℕ.+-comm m n)

  +-assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
  +-assoc = Mod-ind-IsProp-3 (λ _ _ _ → Mod-IsSet _ _) λ m n o → ap r (ℕ.+-assoc m n o)

  r-+-hom : ∀ {m n} → r (m ℕ.+ n) ≡ r m + r n
  r-+-hom = refl

  -- TODO: name?
  -- "canonical representative" in terms of finite sets
  rep : Fin d → Mod d
  rep i = r (toℕ i)

  rep-IsEquiv : 0 < d → IsEquiv rep
  rep-IsEquiv 0<d = HasInverse→IsEquiv g g-rep rep-g
    where
    -- TODO: open division with 0<d
    remainder-+d : ∀ n → remainder 0<d (n ℕ.+ d) ≡ remainder 0<d n
    remainder-+d n =
      ap (λ n → remainder 0<d (n ℕ.+ d)) (sym (rightInv (euclid-IsEquiv 0<d) n)) ∙
      ap (remainder 0<d) (euclid-+d 0<d (quotient 0<d n) (remainder 0<d n)) ∙
      ap snd (leftInv (euclid-IsEquiv 0<d) (ℕ.suc (quotient 0<d n) , remainder 0<d n))

    g : Mod d → Fin d
    g = Mod-rec Fin-IsSet (remainder 0<d) remainder-+d

    g-rep : (i : Fin d) → g (rep i) ≡ i
    g-rep i = ap snd (leftInv (euclid-IsEquiv 0<d) (0 , i))

    r-euclid : ∀ q i → r (toℕ i) ≡ r (euclid 0<d (q , i))
    r-euclid ℕ.zero i = refl
    r-euclid (ℕ.suc q) i = r-euclid q i ∙ r-+d (euclid-+d 0<d q i)

    rep-remainder : ∀ n → rep (remainder 0<d n) ≡ r n
    rep-remainder n = r-euclid (quotient 0<d n) (remainder 0<d n) ∙ ap r (rightInv (euclid-IsEquiv 0<d) n)

    rep-g : (n : Mod d) → rep (g n) ≡ n
    rep-g = Mod-ind-IsProp (λ _ → Mod-IsSet _ _) rep-remainder

-- Agda integer literals
instance
  NumberMod : ∀ {d} → Number (Mod d)
  NumberMod = record
    { Constraint = λ n → ⊤  -- TODO: n < d for safety
    ; fromNat = λ n → r n
    }
