module Math.Mod where

open import Math.Fin
open import Math.Function
open import Math.Int using (ℤ; ℤ-ind-IsProp; pos; neg) renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
import Math.Int as ℤ
open import Math.IntDivision
open import Math.Nat using (ℕ-IsSet; _<_)
open import Math.Quotient
open import Math.Type

open import Agda.Builtin.FromNat using (fromNat)

Mod : ℕ → Type₀
Mod d = ℤ / (λ m n → pos d +ℤ m ≡ n)

module _ {d : ℕ} where
  Mod-IsSet : IsSet (Mod d)
  Mod-IsSet = /-IsSet

  fromℤ : ℤ → Mod d
  fromℤ n = [ n ]

  fromℕ : ℕ → Mod d
  fromℕ n = fromℤ (pos n)

  fromℤ-≡ : ∀ {m n} → pos d +ℤ m ≡ n → fromℤ m ≡ fromℤ n
  fromℤ-≡ {m} {n} = /-≡ m n

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

  negate : Mod d → Mod d
  negate = Mod-rec Mod-IsSet (λ n → fromℤ (ℤ.negate n))
    λ n → fromℤ-≡ (ap (pos d +ℤ_) (ℤ.negate-+ (pos d) n) ∙ ℤ.+-assoc (pos d) (ℤ.negate (pos d)) (ℤ.negate n) ∙ ap (_+ℤ ℤ.negate n) (ℤ.negate-rightInv (pos d)))

  _-_ : Mod d → Mod d → Mod d
  m - n = m + negate n

  _*_ : Mod d → Mod d → Mod d
  _*_ = Mod-rec-2 Mod-IsSet (λ m n → fromℤ (m *ℤ n)) left right
    where
    fromℤ-*d : ∀ m n → fromℤ (m *ℤ pos d +ℤ n) ≡ fromℤ n
    fromℤ-*d = ℤ-ind-IsProp (λ _ → Π-IsProp λ _ → Mod-IsSet _ _)
      (λ n → refl)
      (λ m p n → sym (fromℤ-≡ (ℤ.+-assoc (pos d) (m *ℤ pos d) n)) ∙ p n)
      (λ m p n → fromℤ-≡ (ap (pos d +ℤ_) (sym (ℤ.+-assoc (neg d) (m *ℤ pos d) n)) ∙ rightInv (ℤ.n+-IsEquiv (pos d)) (m *ℤ pos d +ℤ n)) ∙ p n)

    right : (m n : ℤ) → fromℤ (m *ℤ (pos d +ℤ n)) ≡ fromℤ (m *ℤ n)
    right m n = ap fromℤ (sym (ℤ.*-distrib-l m (pos d) n)) ∙ fromℤ-*d m (m *ℤ n)

    left : (m n : ℤ) → fromℤ ((pos d +ℤ m) *ℤ n) ≡ fromℤ (m *ℤ n)
    left m n = ap fromℤ (ℤ.*-comm (pos d +ℤ m) n) ∙ right n m ∙ ap fromℤ (ℤ.*-comm n m)

  fromFin : Fin d → Mod d
  fromFin i = fromℕ (toℕ i)

  fromFin-IsEquiv : 0 < d → IsEquiv fromFin
  fromFin-IsEquiv 0<d = HasInverse→IsEquiv g g-fromFin fromFin-g
    where
    remainder-+d : ∀ n → remainder 0<d (pos d +ℤ n) ≡ remainder 0<d n
    remainder-+d n =
      ap (remainder 0<d) (ℤ.+-comm (pos d) n) ∙
      ap (λ n → remainder 0<d (n +ℤ pos d)) (sym (rightInv (euclid-IsEquiv 0<d) n)) ∙
      ap (remainder 0<d) (euclid-suc 0<d (quotient 0<d n) (remainder 0<d n)) ∙
      ap snd (leftInv (euclid-IsEquiv 0<d) (ℤ.suc (quotient 0<d n) , remainder 0<d n))

    g : Mod d → Fin d
    g = Mod-rec Fin-IsSet (remainder 0<d) remainder-+d

    g-fromFin : (i : Fin d) → g (fromFin i) ≡ i
    g-fromFin i = ap snd (leftInv (euclid-IsEquiv 0<d) (0 , i))

    fromℤ-euclid : ∀ q i → fromℕ (toℕ i) ≡ fromℤ (euclid 0<d (q , i))
    fromℤ-euclid = ℤ-ind-IsProp (λ _ → Π-IsProp λ _ → Mod-IsSet _ _)
      (λ i → refl)
      (λ q p i → p i ∙ fromℤ-≡ (ℤ.+-comm (pos d) (euclid 0<d (q , i)) ∙ euclid-suc 0<d q i))
      (λ q p i → p i ∙ sym (fromℤ-≡ (ℤ.+-comm (pos d) (euclid 0<d (ℤ.pred q , i)) ∙ ap (_+ℤ pos d) (sym (euclid-pred 0<d q i)) ∙ rightInv (ℤ.+n-IsEquiv (pos d)) (euclid 0<d (q , i)))))

    fromFin-remainder : ∀ n → fromFin (remainder 0<d n) ≡ fromℤ n
    fromFin-remainder n = fromℤ-euclid (quotient 0<d n) (remainder 0<d n) ∙ ap fromℤ (rightInv (euclid-IsEquiv 0<d) n)

    fromFin-g : (n : Mod d) → fromFin (g n) ≡ n
    fromFin-g = Mod-ind-IsProp (λ _ → Mod-IsSet _ _) fromFin-remainder
