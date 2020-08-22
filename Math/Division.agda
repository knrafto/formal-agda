{-# OPTIONS --cubical --allow-unsolved-metas #-}
-- Euclidean division of natural numbers.
module Math.Division where

open import Cubical.Data.Fin.Properties using (Residue; isContrResidue)
open import Math.Dec
open import Math.Fin
open import Math.Function
open import Math.Id
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
  euclid-< {n} q r q<n = <≤-trans (<-k+ (snd r)) (subst (_≤ n * d) (+-comm d (q * d)) (≤-*k q<n))

  ≤-euclid : ∀ {n} q r → n ≤ q → n * d ≤ euclid (q , r)
  ≤-euclid {n} q r n≤q = ≤-trans (≤-*k n≤q) (toℕ r , +-comm (toℕ r) (q * d))

  euclid-IsInjective : IsInjective euclid
  euclid-IsInjective {zero , r₁} {zero , r₂} p = ×≡ (refl , toℕ-IsInjective p)
  euclid-IsInjective {zero , r₁} {suc q₂ , r₂} p = ⊥-rec (<-asym (snd r₁) (subst (d ≤_) (sym p) (euclid (q₂ , r₂) , euclid-suc q₂ r₂)))
  euclid-IsInjective {suc q₁ , r₁} {zero , r₂} p = ⊥-rec (<-asym (snd r₂) (subst (d ≤_) p (euclid (q₁ , r₁) , euclid-suc q₁ r₁)))
  euclid-IsInjective {suc q₁ , r₁} {suc q₂ , r₂} p = ap (λ { (q , r) → (suc q , r) }) (euclid-IsInjective (+m-IsInjective {m = d} (euclid-suc q₁ r₁ ∙ p ∙ sym (euclid-suc q₂ r₂))))

  euclid-IsSurjective : IsSurjective euclid
  euclid-IsSurjective = <-ind λ n rec → case <-Dec n d return fiber euclid n of λ
    { (yes n<d) → (zero , (n , n<d)) , refl
    ; (no ¬n<d) →
      let d≤n : d ≤ n
          d≤n = case d ≟ n return d ≤ n of λ
            { (lt d<n) → <-weaken d<n
            ; (eq d≡n) → subst (d ≤_) d≡n ≤-refl
            ; (gt n<d) → ⊥-rec (¬n<d n<d)
            }
          k = fst d≤n
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

  quotient-< : ∀ {n m} → n < m * d → quotient n < m
  quotient-< = {!!}
