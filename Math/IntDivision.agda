{-# OPTIONS --cubical #-}
module Math.IntDivision where

open import Math.Fin
open import Math.Function
open import Math.Int
open import Math.Nat using () renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; _<_ to _<ℕ_)
import Math.Nat as ℕ
import Math.NatDivision as ℕ
open import Math.Prod
open import Math.Type

module _ {d} (0<d : 0 <ℕ d) where
  -- The map (q, r) ↦ qd + r
  euclid : ℤ × Fin d → ℤ
  euclid (q , r) = q * pos d + pos (toℕ r)

  euclid-suc : ∀ q r → euclid (q , r) + pos d ≡ euclid (suc q , r)
  euclid-suc q r = +-comm (euclid (q , r)) (pos d) ∙ +-assoc (pos d) (q * pos d) (pos (toℕ r))

  euclid-< : ∀ {n} q r → q < n → euclid (q , r) < n * pos d
  euclid-< {n} q r q<n = <≤-trans (<-k+ {k = q * pos d} (pos-< (snd r))) (subst (_≤ n * pos d) (+-comm (pos d) (q * pos d)) (≤-*-pos d q<n))

  ≤-euclid : ∀ {n} q r → n ≤ q → n * pos d ≤ euclid (q , r)
  ≤-euclid {n} q r n≤q = ≤-trans (≤-*-pos d n≤q) (toℕ r , +-comm (pos (toℕ r)) (q * pos d))

  euclid-pos : ∀ q r → euclid (pos q , r) ≡ pos (ℕ.euclid 0<d (q , r))
  euclid-pos q r = ap (_+ pos (toℕ r)) (sym (pos-* q d)) ∙ sym (pos-+ (q *ℕ d) (toℕ r))

  euclid-negsuc : ∀ q r → euclid (neg (ℕ.suc q) , r) ≡ neg (ℕ.suc (ℕ.euclid 0<d (q , reflect r)))
  euclid-negsuc q r =
    -- TODO: use ≡⟨⟩ reasoning to make this mess slightly more readable?
    ap (_+ pos (toℕ r)) (+-comm (neg d) (neg q * pos d)) ∙
    sym (+-assoc (neg q * pos d) (neg d) (pos (toℕ r))) ∙
    ap (neg q * pos d +_) reflect-toℕ' ∙
    ap (_+ neg (ℕ.suc (toℕ (reflect r)))) (neg-*-pos q d) ∙
    sym (neg-+ (q *ℕ d) (ℕ.suc (toℕ (reflect r)))) ∙
    ap neg (ℕ.+-suc (q *ℕ d) (toℕ (reflect r)))
    where
    reflect-toℕ' : neg d + pos (toℕ r) ≡ neg (ℕ.suc (toℕ (reflect r)))
    reflect-toℕ' =
      ap (λ n → neg n + pos (toℕ r)) (sym (reflect-toℕ r)) ∙
      ap (_+ pos (toℕ r)) (neg-+ (ℕ.suc (toℕ (reflect r))) (toℕ r)) ∙
      rightInv (+n-IsEquiv (pos (toℕ r))) (neg (ℕ.suc (toℕ (reflect r))))

  -- TODO: is there a slicker proof of euclid-IsEquiv by composing equivalences?

  euclid-IsInjective : IsInjective euclid
  euclid-IsInjective {q₁ , r₁} {q₂ , r₂} p = case (sign q₁ , sign q₂) return (q₁ , r₁) ≡ (q₂ , r₂) of λ
    { (inl (i₁ , posi₁≡q₁) , inl (i₂ , posi₂≡q₂)) →
      let p' : pos (ℕ.euclid 0<d (i₁ , r₁)) ≡ pos (ℕ.euclid 0<d (i₂ , r₂))
          p' = sym (euclid-pos i₁ r₁) ∙ ap (λ n → euclid (n , r₁)) posi₁≡q₁ ∙ p ∙ ap (λ n → euclid (n , r₂)) (sym posi₂≡q₂) ∙ euclid-pos i₂ r₂

          p'' : (i₁ , r₁) ≡ (i₂ , r₂)
          p'' = ℕ.euclid-IsInjective 0<d (pos-IsInjective p')
      in ×≡ (sym posi₁≡q₁ ∙ ap (pos ∘ fst) p'' ∙ posi₂≡q₂ , ap snd p'')
    ; (inl (i₁ , posi₁≡q₁) , inr (i₂ , negsuci₂≡q₂)) →
      let p' : pos (ℕ.euclid 0<d (i₁ , r₁)) ≡ neg (ℕ.suc (ℕ.euclid 0<d (i₂ , reflect r₂)))
          p' = sym (euclid-pos i₁ r₁) ∙ ap (λ n → euclid (n , r₁)) posi₁≡q₁ ∙ p ∙ ap (λ n → euclid (n , r₂)) (sym negsuci₂≡q₂) ∙ euclid-negsuc i₂ r₂
      in ⊥-rec (¬pos≡negsuc (ℕ.euclid 0<d (i₁ , r₁)) (ℕ.euclid 0<d (i₂ , reflect r₂)) p')
    ; (inr (i₁ , negsuci₁≡q₁) , inl (i₂ , posi₂≡q₂)) →
      let p' : neg (ℕ.suc (ℕ.euclid 0<d (i₁ , reflect r₁))) ≡ pos (ℕ.euclid 0<d (i₂ , r₂))
          p' = sym (euclid-negsuc i₁ r₁) ∙ ap (λ n → euclid (n , r₁)) negsuci₁≡q₁ ∙ p ∙ ap (λ n → euclid (n , r₂)) (sym posi₂≡q₂) ∙ euclid-pos i₂ r₂
      in ⊥-rec (¬pos≡negsuc (ℕ.euclid 0<d (i₂ , r₂)) (ℕ.euclid 0<d (i₁ , reflect r₁)) (sym p'))
    ; (inr (i₁ , negsuci₁≡q₁) , inr (i₂ , negsuci₂≡q₂)) →
      let p' : neg (ℕ.suc (ℕ.euclid 0<d (i₁ , reflect r₁))) ≡ neg (ℕ.suc (ℕ.euclid 0<d (i₂ , reflect r₂)))
          p' = sym (euclid-negsuc i₁ r₁) ∙ ap (λ n → euclid (n , r₁)) negsuci₁≡q₁ ∙ p ∙ ap (λ n → euclid (n , r₂)) (sym negsuci₂≡q₂) ∙ euclid-negsuc i₂ r₂

          p'' : (i₁ , reflect r₁) ≡ (i₂ , reflect r₂)
          p'' = ℕ.euclid-IsInjective 0<d (ℕ.suc-IsInjective (neg-IsInjective p'))
      in ×≡ (sym negsuci₁≡q₁ ∙ ap (neg ∘ ℕ.suc ∘ fst) p'' ∙ negsuci₂≡q₂ , IsEquiv→IsInjective reflect-IsEquiv (ap snd p''))
    }

  euclid-IsSurjective : IsSurjective euclid
  euclid-IsSurjective n = case sign n return fiber euclid n of λ
    { (inl (i , posi≡n)) →
      let ((q , r) , p) = ℕ.euclid-IsSurjective 0<d i
      in (pos q , r) , euclid-pos q r ∙ ap pos p ∙ posi≡n
    ; (inr (i , negsuci≡n)) →
      let ((q , r) , p) = ℕ.euclid-IsSurjective 0<d i
      in (neg (ℕ.suc q) , reflect r) , euclid-negsuc q (reflect r) ∙ ap (λ r → neg (ℕ.suc (ℕ.euclid 0<d (q , r)))) (reflect-reflect r) ∙ ap (neg ∘ ℕ.suc) p ∙ negsuci≡n
    }

  euclid-IsEquiv : IsEquiv euclid
  euclid-IsEquiv = IsInjective×IsSurjective→IsEquiv (×-IsSet ℤ-IsSet Fin-IsSet) ℤ-IsSet euclid-IsInjective euclid-IsSurjective

  divmod : ℤ → ℤ × Fin d
  divmod = inv euclid-IsEquiv

  quotient : ℤ → ℤ
  quotient n = fst (divmod n)

  remainder : ℤ → Fin d
  remainder n = snd (divmod n)

  quotient-< : ∀ {m n} → m < n * pos d → quotient m < n
  quotient-< {m} {n} m<n*posd = case dichotomy (quotient m) n return quotient m < n of λ
    { (inl q<n) → q<n
    ; (inr n≤q) →
      let (q , r) = divmod m
      in ⊥-rec (<-asym m<n*posd (subst (n * pos d ≤_) (rightInv euclid-IsEquiv m) (≤-euclid {n = n} q r n≤q)))
    }
