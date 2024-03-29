-- Euclidean division of natural numbers.
module Math.NatDivision where

open import Math.Fin
open import Math.Function
open import Math.Nat
open import Math.Prod
open import Math.Type

module _ {d} (0<d : 0 < d) where
  -- The map (q, r) ↦ qd + r
  euclid : ℕ × Fin d → ℕ
  euclid (q , r) = q * d + toℕ r

  euclid-suc : ∀ q r → euclid (q , r) + d ≡ euclid (suc q , r)
  euclid-suc q r = +-comm (euclid (q , r)) d ∙ +-assoc d (q * d) (toℕ r)

  euclid-< : ∀ {n} q r → q < n → euclid (q , r) < n * d
  euclid-< {n} q r q<n = <≤-trans (<-k+ (toℕ-< r)) (subst (_≤ n * d) (+-comm d (q * d)) (≤-*k q<n))

  ≤-euclid : ∀ {n} q r → n ≤ q → n * d ≤ euclid (q , r)
  ≤-euclid {n} q r n≤q = ≤-trans (≤-*k n≤q) (toℕ r , +-comm (toℕ r) (q * d))

  euclid-IsInjective : IsInjective euclid
  euclid-IsInjective {zero , r₁} {zero , r₂} p = ×≡ (refl , toℕ-IsInjective p)
  euclid-IsInjective {zero , r₁} {suc q₂ , r₂} p = ⊥-rec (<-asym (toℕ-< r₁) (subst (d ≤_) (sym p) (euclid (q₂ , r₂) , euclid-suc q₂ r₂)))
  euclid-IsInjective {suc q₁ , r₁} {zero , r₂} p = ⊥-rec (<-asym (toℕ-< r₂) (subst (d ≤_) p (euclid (q₁ , r₁) , euclid-suc q₁ r₁)))
  euclid-IsInjective {suc q₁ , r₁} {suc q₂ , r₂} p = ap (λ (q , r) → (suc q , r)) (euclid-IsInjective (+m-IsInjective {m = d} (euclid-suc q₁ r₁ ∙ p ∙ sym (euclid-suc q₂ r₂))))

  euclid-IsSurjective : IsSurjective euclid
  euclid-IsSurjective = <-ind λ n rec → case dichotomy n d return fiber euclid n of λ
    { (inl n<d) → (zero , fromℕ n n<d) , toℕ-fromℕ n n<d
    ; (inr d≤n) →
      let k = fst d≤n
          ((q , r) , p) = rec k (subst (k <_) (+-comm d k ∙ snd d≤n) (<-+k 0<d))
      in (suc q , r) , sym (euclid-suc q r) ∙ ap (_+ d) p ∙ snd d≤n
    }

  euclid-IsEquiv : IsEquiv euclid
  euclid-IsEquiv = IsInjective×IsSurjective→IsEquiv (×-IsSet ℕ-IsSet Fin-IsSet) ℕ-IsSet euclid-IsInjective euclid-IsSurjective

  divmod : ℕ → ℕ × Fin d
  divmod = inv euclid-IsEquiv

  quotient : ℕ → ℕ
  quotient n = fst (divmod n)

  remainder : ℕ → Fin d
  remainder n = snd (divmod n)

  quotient-< : ∀ {m n} → m < n * d → quotient m < n
  quotient-< {m} {n} m<n*d = case dichotomy (quotient m) n return quotient m < n of λ
    { (inl q<n) → q<n
    ; (inr n≤q) →
      let (q , r) = divmod m
      in ⊥-rec (<-asym m<n*d (subst (n * d ≤_) (rightInv euclid-IsEquiv m) (≤-euclid {n = n} q r n≤q)))
    }
