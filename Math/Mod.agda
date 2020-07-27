{-# OPTIONS --cubical #-}
module Math.Mod where

open import Agda.Builtin.FromNat
open import Math.Division
open import Math.Fin
open import Math.Function
open import Math.Nat using (ℕ-IsSet; _<_)
import Math.Nat as ℕ
-- TODO: Math.Quotient?
open import Cubical.HITs.SetQuotients using (_/_; [_]; elim; elimProp)
open import Math.Type

-- TODO: most of this belongs in a Math.Quotient file

Mod : ℕ → Type₀
Mod d = ℕ / (λ m n → m ℕ.+ d ≡ n)

module _ {d : ℕ} where
  -- "remainder"
  r : ℕ → Mod d
  r n = [ n ]

  r-+d : ∀ {m n} → m ℕ.+ d ≡ n → r m ≡ r n
  r-+d {m} {n} = _/_.eq/ m n

  Mod-IsSet : IsSet (Mod d)
  Mod-IsSet = _/_.squash/

  Mod-ind-prop
    : ∀ {ℓ} {P : Mod d → Type ℓ}
    → (∀ a → IsProp (P a))
    → (f : ∀ a → P (r a))
    → (a : Mod d) → P a
  Mod-ind-prop = elimProp

  Mod-ind-prop-2
    : ∀ {ℓ} {P : Mod d → Mod d → Type ℓ}
    → (∀ a b → IsProp (P a b))
    → (f : ∀ a b → P (r a) (r b))
    → (a b : Mod d) → P a b
  Mod-ind-prop-2 P-IsProp f = Mod-ind-prop (λ a → Π-IsProp (P-IsProp a)) λ a → Mod-ind-prop (P-IsProp _) λ b → f a b

  Mod-ind-prop-3
    : ∀ {ℓ} {P : Mod d → Mod d → Mod d → Type ℓ}
    → (∀ a b c → IsProp (P a b c))
    → (f : ∀ a b c → P (r a) (r b) (r c))
    → (a b c : Mod d) → P a b c
  Mod-ind-prop-3 P-IsProp f = Mod-ind-prop-2 (λ a b → Π-IsProp (P-IsProp a b)) λ a b → Mod-ind-prop (P-IsProp _ _) λ c → f a b c

  -- Computes on r: Mod-rec A-IsSet f p (r n) is definitionally equal to f n
  Mod-rec : ∀ {ℓ} {A : Type ℓ} → IsSet A → (f : ℕ → A) → (∀ n → f (n ℕ.+ d) ≡ f n) → Mod d → A
  Mod-rec A-IsSet f p = elim (λ _ → A-IsSet) f λ a b a~b → sym (p a) ∙ ap f a~b

  -- Recursion on two Mod d arguments
  Mod-rec-2
    : ∀ {ℓ} {A : Type ℓ} → IsSet A → (f : ℕ → ℕ → A)
    → (∀ m n → f (m ℕ.+ d) n ≡ f m n)
    → (∀ m n → f m (n ℕ.+ d) ≡ f m n)
    → Mod d → Mod d → A
  Mod-rec-2 A-IsSet f pl pr = Mod-rec (→-IsSet A-IsSet) (λ m → Mod-rec A-IsSet (λ n → f m n) (pr m))
    λ m → funExt (Mod-ind-prop (λ n → A-IsSet _ _) (pl m))

  _+_ : Mod d → Mod d → Mod d
  _+_ = Mod-rec-2 Mod-IsSet (λ m n → r (m ℕ.+ n)) left right
    where
    right : (m n : ℕ) → r (m ℕ.+ (n ℕ.+ d)) ≡ r (m ℕ.+ n)
    right m n = sym (r-+d (sym (ℕ.+-assoc m n d)))

    left : (m n : ℕ) → r ((m ℕ.+ d) ℕ.+ n) ≡ r (m ℕ.+ n)
    left m n = ap r (ℕ.+-comm (m ℕ.+ d) n) ∙ right n m ∙ ap r (ℕ.+-comm n m)

  zero : Mod d
  zero = r ℕ.zero

  zero-+ : ∀ n → zero + n ≡ n
  zero-+ = Mod-ind-prop (λ _ → Mod-IsSet _ _) λ n → refl

  +-zero : ∀ n → n + zero ≡ n
  +-zero = Mod-ind-prop (λ _ → Mod-IsSet _ _) λ n → ap r (ℕ.+-zero n)

  +-comm : ∀ m n → m + n ≡ n + m
  +-comm = Mod-ind-prop-2 (λ _ _ → Mod-IsSet _ _) λ m n → ap r (ℕ.+-comm m n)

  +-assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
  +-assoc = Mod-ind-prop-3 (λ _ _ _ → Mod-IsSet _ _) λ m n o → ap r (ℕ.+-assoc m n o)

  r-+-hom : ∀ {m n} → r (m ℕ.+ n) ≡ r m + r n
  r-+-hom = refl

  -- TODO: name?
  -- "canonical representative" in terms of finite sets
  rep : Fin d → Mod d
  rep i = r (toℕ i)

  rep-IsEquiv : d < 0 → IsEquiv rep
  rep-IsEquiv d<0 = HasInverse→IsEquiv g g-rep rep-g
    where
    euclid-+d : ∀ q i → euclid d<0 (q , i) ℕ.+ d ≡ euclid d<0 (ℕ.suc q , i)
    euclid-+d q i = ℕ.+-comm (q ℕ.* d ℕ.+ toℕ i) d ∙ ℕ.+-assoc d (q ℕ.* d) (toℕ i)

    remainder-+d : ∀ n → remainder d<0 (n ℕ.+ d) ≡ remainder d<0 n
    remainder-+d n =
      ap (λ n → remainder d<0 (n ℕ.+ d)) (sym (rightInv (euclid-IsEquiv d<0) n)) ∙
      ap (remainder d<0) (euclid-+d (quotient d<0 n) (remainder d<0 n)) ∙
      ap snd (leftInv (euclid-IsEquiv d<0) (ℕ.suc (quotient d<0 n) , remainder d<0 n))

    g : Mod d → Fin d
    g = Mod-rec Fin-IsSet (remainder d<0) remainder-+d

    g-rep : (i : Fin d) → g (rep i) ≡ i
    g-rep i = ap snd (leftInv (euclid-IsEquiv d<0) (0 , i))

    r-euclid : ∀ q i → r (toℕ i) ≡ r (euclid d<0 (q , i))
    r-euclid ℕ.zero i = refl
    r-euclid (ℕ.suc q) i = r-euclid q i ∙ r-+d (euclid-+d q i)

    rep-remainder : ∀ n → rep (remainder d<0 n) ≡ r n
    rep-remainder n = r-euclid (quotient d<0 n) (remainder d<0 n) ∙ ap r (rightInv (euclid-IsEquiv d<0) n)

    rep-g : (n : Mod d) → rep (g n) ≡ n
    rep-g = Mod-ind-prop (λ _ → Mod-IsSet _ _) rep-remainder

-- Agda integer literals
instance
  NumberMod : ∀ {d} → Number (Mod d)
  NumberMod = record
    { Constraint = λ n → ⊤  -- TODO: n < d for safety
    ; fromNat = λ n → r n
    }
