{-# OPTIONS --cubical --allow-unsolved-metas #-}
module Math.Mod where

open import Math.Division
open import Math.Fin
open import Math.Function
open import Math.Int using (ℤ; pos) renaming (_+_ to _+ℤ_)
import Math.Int as ℤ
open import Math.Nat using (ℕ-IsSet; _<_)
open import Math.Quotient
open import Math.Type

-- TODO: d should go on the left?
Mod : ℕ → Type₀
Mod d = ℤ / (λ m n → pos d +ℤ m ≡ n)

module _ {d : ℕ} where
  fromℤ : ℤ → Mod d
  fromℤ n = [ n ]

  fromℤ-≡ : ∀ {m n} → pos d +ℤ m ≡ n → fromℤ m ≡ fromℤ n
  fromℤ-≡ {m} {n} = /-≡ m n

  fromℕ : ℕ → Mod d
  fromℕ n = fromℤ (pos n)

  Mod-IsSet : IsSet (Mod d)
  Mod-IsSet = /-IsSet

  Mod-ind-IsProp
    : ∀ {ℓ} {P : Mod d → Type ℓ}
    → (∀ a → IsProp (P a))
    → (f : ∀ a → P (fromℤ a))
    → (a : Mod d) → P a
  Mod-ind-IsProp = /-ind-IsProp

  Mod-ind-IsProp-2
    : ∀ {ℓ} {P : Mod d → Mod d → Type ℓ}
    → (∀ a b → IsProp (P a b))
    → (f : ∀ a b → P (fromℤ a) (fromℤ b))
    → (a b : Mod d) → P a b
  Mod-ind-IsProp-2 P-IsProp f = Mod-ind-IsProp (λ a → Π-IsProp (P-IsProp a)) λ a → Mod-ind-IsProp (P-IsProp _) λ b → f a b

  Mod-ind-IsProp-3
    : ∀ {ℓ} {P : Mod d → Mod d → Mod d → Type ℓ}
    → (∀ a b c → IsProp (P a b c))
    → (f : ∀ a b c → P (fromℤ a) (fromℤ b) (fromℤ c))
    → (a b c : Mod d) → P a b c
  Mod-ind-IsProp-3 P-IsProp f = Mod-ind-IsProp-2 (λ a b → Π-IsProp (P-IsProp a b)) λ a b → Mod-ind-IsProp (P-IsProp _ _) λ c → f a b c

  -- Mod-rec _ f _ (fromℤ n) is definitionally equal to f n
  Mod-rec : ∀ {ℓ} {A : Type ℓ} → IsSet A → (f : ℤ → A) → (∀ n → f (pos d +ℤ n) ≡ f n) → Mod d → A
  Mod-rec A-IsSet f p = /-rec A-IsSet f λ a b a~b → sym (p a) ∙ ap f a~b

  Mod-rec-2
    : ∀ {ℓ} {A : Type ℓ} → IsSet A → (f : ℤ → ℤ → A)
    → (∀ m n → f (pos d +ℤ m) n ≡ f m n)
    → (∀ m n → f m (pos d +ℤ n) ≡ f m n)
    → Mod d → Mod d → A
  Mod-rec-2 A-IsSet f pl pr = Mod-rec (→-IsSet A-IsSet) (λ m → Mod-rec A-IsSet (λ n → f m n) (pr m))
    λ m → funExt (Mod-ind-IsProp (λ n → A-IsSet _ _) (pl m))

  _+_ : Mod d → Mod d → Mod d
  _+_ = Mod-rec-2 Mod-IsSet (λ m n → fromℤ (m +ℤ n)) left right
    where
    left : (m n : ℤ) → fromℤ ((pos d +ℤ m) +ℤ n) ≡ fromℤ (m +ℤ n)
    left m n = sym (fromℤ-≡ (ℤ.+-assoc (pos d) m n))

    right : (m n : ℤ) → fromℤ (m +ℤ (pos d +ℤ n)) ≡ fromℤ (m +ℤ n)
    right m n = ap fromℤ (ℤ.+-comm m (pos d +ℤ n)) ∙ left n m ∙ ap fromℤ (ℤ.+-comm n m)

  -_ : Mod d → Mod d
  -_ = Mod-rec Mod-IsSet (λ n → fromℤ (ℤ.negate n)) λ n → fromℤ-≡ {!!}

  _-_ : Mod d → Mod d → Mod d
  m - n = m + (- n)

{-
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
-}
