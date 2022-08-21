module Math.Finite where

open import Math.Dec
open import Math.Fin
open import Math.Function
open import Math.Id
open import Math.Nat
open import Math.Sigma
open import Math.Sum
open import Math.Type

IsFinite : Type₀ → Type₀
IsFinite A = Σ[ n ∈ ℕ ] ∥ Fin n ≃ A ∥

card : ∀ {A : Type₀} → IsFinite A → ℕ
card = fst

⊤⊎-cancel : {A B : Type} → ⊤ ⊎ A ≃ ⊤ ⊎ B → A ≃ B
⊤⊎-cancel {A} {B} (f , f-IsEquiv) = {!!}

-- TODO: Can we derive this from pigeonhole principles instead?
-- For a general f : Fin m → Fin n
--   f is injective  ⟹ m ≤ n
--   f is surjective ⟹ m ≥ n
Fin-cancel : ∀ {m n} → Fin m ≃ Fin n → m ≡ n
Fin-cancel {m = zero } {n = zero } (f , f-IsEquiv) = refl
Fin-cancel {m = zero } {n = suc n} (f , f-IsEquiv) = ⊥-rec (inv f-IsEquiv fzero)
Fin-cancel {m = suc m} {n = zero } (f , f-IsEquiv) = ⊥-rec (f fzero)
Fin-cancel {m = suc m} {n = suc n} (f , f-IsEquiv) = ap suc (Fin-cancel (⊤⊎-cancel (f , f-IsEquiv)))

IsFinite-IsProp : ∀ {A : Type₀} → IsProp (IsFinite A)
IsFinite-IsProp (m , |Finm≃A|) (n , |Finn≃A|) = ΣProp≡ (λ _ → ∥∥-IsProp) m≡n
  where
  m≡n : m ≡ n
  m≡n =
    with-∥∥ |Finm≃A| (ℕ-IsSet _ _) λ (f , f-IsEquiv) →
    with-∥∥ |Finn≃A| (ℕ-IsSet _ _) λ (g , g-IsEquiv) →
    Fin-cancel (inv g-IsEquiv ∘ f , inv-IsEquiv g-IsEquiv ∘-IsEquiv f-IsEquiv)

IsFinite→IsSet : ∀ {A : Type₀} → IsFinite A → IsSet A
IsFinite→IsSet (n , |Finm≃A|) = with-∥∥ |Finm≃A| IsSet-IsProp λ Finm≃A →
  subst IsSet (≃→≡ Finm≃A) Fin-IsSet

IsFinite-rec : ∀ {ℓ} {A} {P : Type → Type ℓ} → (∀ {A} → IsProp (P A)) → (∀ n → P (Fin n)) → IsFinite A → P A
IsFinite-rec {P = P} P-IsProp Fin-P (n , e) = with-∥∥ e P-IsProp λ { (e , e-IsEquiv) → subst P (ua e e-IsEquiv) (Fin-P n) }

-- TODO: name
IsFinite-≃ : ∀ {A B} {f : A → B} → IsEquiv f → IsFinite A → IsFinite B
IsFinite-≃ f-IsEquiv (n , e) =
  with-∥∥ e IsFinite-IsProp λ { (g , g-IsEquiv) → n , ∣ _ , f-IsEquiv ∘-IsEquiv g-IsEquiv ∣ }

IsFinite-∀-Dec : ∀ {ℓ} {A : Type₀} {P : A → Type ℓ} → IsFinite A → (∀ a → IsProp (P a)) → (∀ a → Dec (P a)) → Dec (∀ a → P a)
IsFinite-∀-Dec {P = P} (n , |Finn≃A|) P-IsProp P-Dec = with-∥∥ |Finn≃A| (Dec-IsProp (Π-IsProp P-IsProp)) λ Finn≃A → lemma (≃→≡ Finn≃A) P P-Dec
  where
  lemma : ∀ {ℓ} {n} {A : Type₀} → Fin n ≡ A → (P : A → Type ℓ) → (∀ a → Dec (P a)) → Dec (∀ a → P a)
  lemma {ℓ} = pathInd (λ A p → (P : A → Type ℓ) → ((a : A) → Dec (P a)) → Dec (∀ a → P a)) λ P → Fin-∀-Dec {P = P}

IsFinite-∃-Dec : ∀ {ℓ} {A : Type₀} {P : A → Type ℓ} → IsFinite A → (∀ a → Dec (P a)) → Dec ∥ Σ[ a ∈ A ] P a ∥
IsFinite-∃-Dec {P = P} (n , |Finn≃A|) P-Dec = with-∥∥ |Finn≃A| (Dec-IsProp ∥∥-IsProp) λ Finn≃A → lemma (≃→≡ Finn≃A) P P-Dec
  where
  lemma : ∀ {ℓ} {n} {A : Type₀} → Fin n ≡ A → (P : A → Type ℓ) → (∀ a → Dec (P a)) → Dec ∥ Σ[ a ∈ A ] P a ∥
  lemma {ℓ} = pathInd (λ A p → (P : A → Type ℓ) → ((a : A) → Dec (P a)) → Dec ∥ Σ[ a ∈ A ] P a ∥) λ P → Fin-∃-Dec {P = P}

¬→IsFinite : ∀ {A} → ¬ A → IsFinite A
¬→IsFinite ¬A = 0 , ∣ inv (¬-IsEquiv ¬A) , inv-IsEquiv (¬-IsEquiv ¬A) ∣

⊥-IsFinite : IsFinite ⊥
⊥-IsFinite = ¬→IsFinite id

IsContr→IsFinite : ∀ {A} → IsContr A → IsFinite A
IsContr→IsFinite {A} (a , p) = 1 , ∣ (λ _ → a) , HasInverse→IsEquiv (λ _ → fzero) (λ { (inl tt) → refl }) p ∣

⊤-IsFinite : IsFinite ⊤
⊤-IsFinite = IsContr→IsFinite ⊤-IsContr

IsDecProp→IsFinite : ∀ {A} → IsProp A → Dec A → IsFinite A
IsDecProp→IsFinite A-IsProp (yes a) = IsContr→IsFinite (a , A-IsProp a)
IsDecProp→IsFinite A-IsProp (no ¬A) = ¬→IsFinite ¬A

Fin-IsFinite : ∀ {n} → IsFinite (Fin n)
Fin-IsFinite {n = n} = n , ∣ id , id-IsEquiv ∣

⊤⊎-IsFinite : ∀ {A} → IsFinite A → IsFinite (⊤ ⊎ A)
⊤⊎-IsFinite = IsFinite-rec IsFinite-IsProp λ n → Fin-IsFinite {n = suc n}

Fin-⊎-IsFinite : ∀ {n B} → IsFinite B → IsFinite (Fin n ⊎ B)
Fin-⊎-IsFinite {n = zero } B-IsFinite = IsFinite-≃ ⊥-inr-IsEquiv B-IsFinite
Fin-⊎-IsFinite {n = suc n} B-IsFinite = IsFinite-≃ ⊎-unassoc-IsEquiv (⊤⊎-IsFinite (Fin-⊎-IsFinite {n = n} B-IsFinite))

⊎-IsFinite : ∀ {A B} → IsFinite A → IsFinite B → IsFinite (A ⊎ B)
⊎-IsFinite {B = B} = IsFinite-rec (→-IsProp IsFinite-IsProp) λ n → Fin-⊎-IsFinite {n = n} {B = B}

Fin-Σ-IsFinite : ∀ {n B} → (∀ i → IsFinite (B i)) → IsFinite (Σ (Fin n) B)
Fin-Σ-IsFinite {n = zero } B-IsFinite = IsFinite-≃ (inv-IsEquiv ⊥-fst-IsEquiv) ⊥-IsFinite
Fin-Σ-IsFinite {n = suc n} B-IsFinite = IsFinite-≃ ⊎-factor-IsEquiv
  (⊎-IsFinite
    (IsFinite-≃ (inv-IsEquiv Σ-⊤-extract-IsEquiv) (B-IsFinite _))
    (Fin-Σ-IsFinite (λ _ → B-IsFinite _)))

Σ-IsFinite : ∀ {A B} → IsFinite A → (∀ a → IsFinite (B a)) → IsFinite (Σ A B)
Σ-IsFinite {A = A} {B = B} A-IsFinite =
  (IsFinite-rec (Π-IsProp λ _ → →-IsProp IsFinite-IsProp) (λ n B → Fin-Σ-IsFinite {n = n} {B = B}))
  A-IsFinite B

×-IsFinite : ∀ {A B} → IsFinite A → IsFinite B → IsFinite (A × B)
×-IsFinite A-IsFinite B-IsFinite = Σ-IsFinite A-IsFinite λ _ → B-IsFinite

Fin-Π-IsFinite : ∀ {n B} → (∀ i → IsFinite (B i)) → IsFinite (Π (Fin n) B)
Fin-Π-IsFinite {n = zero } B-IsFinite = IsContr→IsFinite Π-⊥-IsContr
Fin-Π-IsFinite {n = suc n} B-IsFinite = IsFinite-≃ pair-IsEquiv
  (×-IsFinite
    (IsFinite-≃ ⊤-ind-IsEquiv (B-IsFinite _))
    (Fin-Π-IsFinite (λ _ → B-IsFinite _)))

Π-IsFinite : ∀ {A B} → IsFinite A → (∀ a → IsFinite (B a)) → IsFinite (Π A B)
Π-IsFinite {A = A} {B = B} A-IsFinite =
  (IsFinite-rec (Π-IsProp λ _ → →-IsProp IsFinite-IsProp) (λ n B → Fin-Π-IsFinite {n = n} {B = B}))
  A-IsFinite B

→-IsFinite : ∀ {A B} → IsFinite A → IsFinite B → IsFinite (A → B)
→-IsFinite A-IsFinite B-IsFinite = Π-IsFinite A-IsFinite λ _ → B-IsFinite

-- TODO: move to own module?
-- TODO: "permutation" might be a more intuitive name
Aut : Type → Type
Aut A = (A ≃ A)

Fin-Aut-IsFinite : ∀ {n} → IsFinite (Aut (Fin n))
Fin-Aut-IsFinite = {!!}

Aut-IsFinite : ∀ {A} → IsFinite A → IsFinite (Aut A)
Aut-IsFinite = IsFinite-rec IsFinite-IsProp λ n → Fin-Aut-IsFinite {n = n}
