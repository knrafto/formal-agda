module Math.IntDivision where

open import Math.Fin
open import Math.Function
open import Math.Int
open import Math.Nat using () renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; _<_ to _<ℕ_)
import Math.Nat as ℕ
import Math.NatDivision as ℕ
open import Math.Prod
open import Math.Sum
open import Math.Type

module _ {d} (0<d : 0 <ℕ d) where
  -- The map (q, r) ↦ qd + r
  euclid : ℤ × Fin d → ℤ
  euclid (q , r) = q * pos d + pos (toℕ r)

  euclid-suc : ∀ q r → euclid (q , r) + pos d ≡ euclid (suc q , r)
  euclid-suc q r = +-comm (euclid (q , r)) (pos d) ∙ +-assoc (pos d) (q * pos d) (pos (toℕ r))

  euclid-pred : ∀ q r → euclid (q , r) + neg d ≡ euclid (pred q , r)
  euclid-pred q r = +-comm (euclid (q , r)) (neg d) ∙ +-assoc (neg d) (q * pos d) (pos (toℕ r))

  euclid-< : ∀ {n} q r → q < n → euclid (q , r) < n * pos d
  euclid-< {n} q r q<n = <≤-trans (<-k+ {k = q * pos d} (pos-< (toℕ-< r))) (subst (_≤ n * pos d) (+-comm (pos d) (q * pos d)) (≤-*-pos d q<n))

  ≤-euclid : ∀ {n} q r → n ≤ q → n * pos d ≤ euclid (q , r)
  ≤-euclid {n} q r n≤q = ≤-trans (≤-*-pos d n≤q) (toℕ r , +-comm (pos (toℕ r)) (q * pos d))

  euclid-pos : ∀ q r → euclid (pos q , r) ≡ pos (ℕ.euclid 0<d (q , r))
  euclid-pos q r = ap (_+ pos (toℕ r)) (sym (pos-* q d)) ∙ sym (pos-+ (q *ℕ d) (toℕ r))

  euclid-negsuc : ∀ q r → euclid (negsuc q , r) ≡ negsuc (ℕ.euclid 0<d (q , reflect r))
  euclid-negsuc q r =
    -- TODO: use ≡⟨⟩ reasoning to make this mess slightly more readable?
    ap (_+ pos (toℕ r)) (+-comm (neg d) (neg q * pos d)) ∙
    sym (+-assoc (neg q * pos d) (neg d) (pos (toℕ r))) ∙
    ap (neg q * pos d +_) reflect-toℕ' ∙
    ap (_+ negsuc (toℕ (reflect r))) (neg-*-pos q d) ∙
    sym (neg-+ (q *ℕ d) (ℕ.suc (toℕ (reflect r)))) ∙
    ap neg (ℕ.+-suc (q *ℕ d) (toℕ (reflect r)))
    where
    reflect-toℕ' : neg d + pos (toℕ r) ≡ negsuc (toℕ (reflect r))
    reflect-toℕ' =
      ap (λ n → neg n + pos (toℕ r)) (sym (toℕ-reflect r)) ∙
      ap (λ n → negsuc n + pos (toℕ r)) (ℕ.+-comm (toℕ r) (toℕ (reflect r))) ∙
      ap (_+ pos (toℕ r)) (neg-+ (ℕ.suc (toℕ (reflect r))) (toℕ r)) ∙
      rightInv (+n-IsEquiv (pos (toℕ r))) (negsuc (toℕ (reflect r)))

  -- TODO: is there a slicker proof of euclid-IsEquiv by composing equivalences?

  euclid-IsInjective : IsInjective euclid
  euclid-IsInjective {q₁ , r₁} {q₂ , r₂} =
    cases {P = λ q₁ → (q₂ : ℤ) (p : euclid (q₁ , r₁) ≡ euclid (q₂ , r₂)) → (q₁ , r₁) ≡ (q₂ , r₂)} fromSigned-IsEquiv
      (λ i₁ → cases fromSigned-IsEquiv
        (λ i₂ p →
          let p' : (i₁ , r₁) ≡ (i₂ , r₂)
              p' = ℕ.euclid-IsInjective 0<d (pos-IsInjective (sym (euclid-pos i₁ r₁) ∙ p ∙ euclid-pos i₂ r₂))
          in ×≡ (ap (pos ∘ fst) p' , ap snd p'))
        (λ i₂ p →
          let p' : pos (ℕ.euclid 0<d (i₁ , r₁)) ≡ negsuc (ℕ.euclid 0<d (i₂ , reflect r₂))
              p' = sym (euclid-pos i₁ r₁) ∙ p ∙ euclid-negsuc i₂ r₂
          in ⊥-rec (¬pos≡negsuc (ℕ.euclid 0<d (i₁ , r₁)) (ℕ.euclid 0<d (i₂ , reflect r₂)) p')))
      (λ i₁ → cases {P = λ q₂ → (p : euclid (negsuc i₁ , r₁) ≡ euclid (q₂ , r₂)) → (negsuc i₁ , r₁) ≡ (q₂ , r₂)} fromSigned-IsEquiv
        (λ i₂ p →
          let p' : negsuc (ℕ.euclid 0<d (i₁ , reflect r₁)) ≡ pos (ℕ.euclid 0<d (i₂ , r₂))
              p' = sym (euclid-negsuc i₁ r₁) ∙ p ∙ euclid-pos i₂ r₂
          in ⊥-rec (¬pos≡negsuc (ℕ.euclid 0<d (i₂ , r₂)) (ℕ.euclid 0<d (i₁ , reflect r₁)) (sym p')))
        (λ i₂ p →
          let p' : (i₁ , reflect r₁) ≡ (i₂ , reflect r₂)
              p' = ℕ.euclid-IsInjective 0<d (ℕ.suc-IsInjective (neg-IsInjective (sym (euclid-negsuc i₁ r₁) ∙ p ∙ euclid-negsuc i₂ r₂)))
          in ×≡ (ap (negsuc ∘ fst) p' , IsEquiv→IsInjective reflect-IsEquiv (ap snd p'))))
      q₁ q₂

  euclid-IsSurjective : IsSurjective euclid
  euclid-IsSurjective = cases fromSigned-IsEquiv
    (λ n →
      let ((q , r) , p) = ℕ.euclid-IsSurjective 0<d n
      in (pos q , r) , euclid-pos q r ∙ ap pos p)
    (λ n →
      let ((q , r) , p) = ℕ.euclid-IsSurjective 0<d n
      in (negsuc q , reflect r) , euclid-negsuc q (reflect r) ∙ ap (λ r → negsuc (ℕ.euclid 0<d (q , r))) (reflect-reflect r) ∙ ap (negsuc) p)

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

  ≤-quotient : ∀ {m n} → n * pos d ≤ m → n ≤ quotient m
  ≤-quotient {m} {n} n*posd≤m = case dichotomy (quotient m) n return n ≤ quotient m of λ
    { (inl q<n) →
      let (q , r) = divmod m
      in ⊥-rec (<-asym (subst (_< n * pos d) (rightInv euclid-IsEquiv m) (euclid-< {n = n} q r q<n)) n*posd≤m)
    ; (inr n≤q) → n≤q
    }
