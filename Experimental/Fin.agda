module Experimental.Fin where

open import Math.Dec
open import Math.Function
open import Math.Nat
open import Math.Prod
open import Math.Sigma
open import Math.Sum
open import Math.Type

private
  variable
    ℓ : Level

Fin : ℕ → Type
Fin zero = ⊥
Fin (suc n) = ⊤ ⊎ Fin n

fzero : ∀ {n} → Fin (suc n)
fzero = inl tt

fsuc : ∀ {n} → Fin n → Fin (suc n)
fsuc = inr

Fin-IsSet : ∀ {n} → IsSet (Fin n)
Fin-IsSet {zero } = ⊥-IsSet
Fin-IsSet {suc n} = ⊎-IsSet ⊤-IsSet Fin-IsSet

Fin1-IsContr : IsContr (Fin 1)
Fin1-IsContr = fzero , λ { (inl tt) → refl }

⊤⊎-cancel : {A B : Type} → ⊤ ⊎ A ≃ ⊤ ⊎ B → A ≃ B
⊤⊎-cancel {A} {B} (f , f-IsEquiv) = {!!}

Fin-cancel : ∀ {m n} → Fin m ≃ Fin n → m ≡ n
Fin-cancel {m = zero } {n = zero } (f , f-IsEquiv) = refl
Fin-cancel {m = zero } {n = suc n} (f , f-IsEquiv) = ⊥-rec (inv f-IsEquiv fzero)
Fin-cancel {m = suc m} {n = zero } (f , f-IsEquiv) = ⊥-rec (f fzero)
Fin-cancel {m = suc m} {n = suc n} (f , f-IsEquiv) = ap suc (Fin-cancel (⊤⊎-cancel (f , f-IsEquiv)))

IsFinite : Type → Type
IsFinite A = Σ[ n ∈ ℕ ] ∥ A ≃ Fin n ∥

IsFinite-rec : ∀ {A} {P : Type → Type ℓ} → (∀ {A} → IsProp (P A)) → (∀ n → P (Fin n)) → IsFinite A → P A
IsFinite-rec {P = P} P-IsProp Fin-P (n , e) = with-∥∥ e P-IsProp λ { (e , e-IsEquiv) → subst P (sym (ua e e-IsEquiv)) (Fin-P n) }

card : ∀ {A} → IsFinite A → ℕ
card = fst

IsFinite-IsSet : ∀ {A} → IsSet (IsFinite A)
IsFinite-IsSet = Σ-IsSet ℕ-IsSet λ _ → IsProp→IsSet ∥∥-IsProp

IsFinite-IsProp : ∀ {A} → IsProp (IsFinite A)
IsFinite-IsProp (n₁ , e₁) (n₂ , e₂) =
  with-∥∥ e₁ (IsFinite-IsSet _ _) λ { (e₁ , e₁-IsEquiv) →
  with-∥∥ e₂ (IsFinite-IsSet _ _) λ { (e₂ , e₂-IsEquiv) →
  Σ≡ (Fin-cancel (_ , e₂-IsEquiv ∘-IsEquiv (inv-IsEquiv e₁-IsEquiv))) (∥∥-IsProp _ _) }}

-- TODO: name
IsFinite-≃ : ∀ {A B} {f : A → B} → IsEquiv f → IsFinite B → IsFinite A
IsFinite-≃ f-IsEquiv (n , e) =
  with-∥∥ e IsFinite-IsProp λ { (g , g-IsEquiv) → n , ∣ _ , g-IsEquiv ∘-IsEquiv f-IsEquiv ∣ }

¬→IsFinite : ∀ {A} → ¬ A → IsFinite A
¬→IsFinite ¬A = 0 , ∣ ¬A , ¬-IsEquiv ¬A ∣

⊥-IsFinite : IsFinite ⊥
⊥-IsFinite = ¬→IsFinite id

IsContr→IsFinite : ∀ {A} → IsContr A → IsFinite A
IsContr→IsFinite {A} (a , p) = 1 , ∣ (λ _ → fzero) , HasInverse→IsEquiv (λ _ → a) p (λ { (inl tt) → refl }) ∣

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
Fin-⊎-IsFinite {n = zero } B-IsFinite = IsFinite-≃ (inv-IsEquiv ⊥-inr-IsEquiv) B-IsFinite
Fin-⊎-IsFinite {n = suc n} B-IsFinite = IsFinite-≃ ⊎-assoc-IsEquiv (⊤⊎-IsFinite (Fin-⊎-IsFinite {n = n} B-IsFinite))

⊎-IsFinite : ∀ {A B} → IsFinite A → IsFinite B → IsFinite (A ⊎ B)
⊎-IsFinite {B = B} = IsFinite-rec (→-IsProp IsFinite-IsProp) λ n → Fin-⊎-IsFinite {n = n} {B = B}

Fin-Σ-IsFinite : ∀ {n B} → (∀ i → IsFinite (B i)) → IsFinite (Σ (Fin n) B)
Fin-Σ-IsFinite {n = zero } B-IsFinite = IsFinite-≃ ⊥-fst-IsEquiv ⊥-IsFinite
Fin-Σ-IsFinite {n = suc n} B-IsFinite = IsFinite-≃ ⊎-distribute-IsEquiv
  (⊎-IsFinite
    (IsFinite-≃ Σ-⊤-extract-IsEquiv (B-IsFinite _))
    (Fin-Σ-IsFinite (λ _ → B-IsFinite _)))

Σ-IsFinite : ∀ {A B} → IsFinite A → (∀ a → IsFinite (B a)) → IsFinite (Σ A B)
Σ-IsFinite {A = A} {B = B} A-IsFinite =
  (IsFinite-rec (Π-IsProp λ _ → →-IsProp IsFinite-IsProp) (λ n B → Fin-Σ-IsFinite {n = n} {B = B}))
  A-IsFinite B

×-IsFinite : ∀ {A B} → IsFinite A → IsFinite B → IsFinite (A × B)
×-IsFinite A-IsFinite B-IsFinite = Σ-IsFinite A-IsFinite λ _ → B-IsFinite

Fin-Π-IsFinite : ∀ {n B} → (∀ i → IsFinite (B i)) → IsFinite (Π (Fin n) B)
Fin-Π-IsFinite {n = zero } B-IsFinite = IsContr→IsFinite Π-⊥-IsContr
Fin-Π-IsFinite {n = suc n} B-IsFinite = IsFinite-≃ (inv-IsEquiv pair-IsEquiv)
  (×-IsFinite
    (IsFinite-≃ (inv-IsEquiv ⊤-ind-IsEquiv) (B-IsFinite _))
    (Fin-Π-IsFinite (λ _ → B-IsFinite _)))

Π-IsFinite : ∀ {A B} → IsFinite A → (∀ a → IsFinite (B a)) → IsFinite (Π A B)
Π-IsFinite {A = A} {B = B} A-IsFinite =
  (IsFinite-rec (Π-IsProp λ _ → →-IsProp IsFinite-IsProp) (λ n B → Fin-Π-IsFinite {n = n} {B = B}))
  A-IsFinite B

→-IsFinite : ∀ {A B} → IsFinite A → IsFinite B → IsFinite (A → B)
→-IsFinite A-IsFinite B-IsFinite = Π-IsFinite A-IsFinite λ _ → B-IsFinite

-- TODO: move to own module
Aut : Type → Type
Aut A = (A ≃ A)

Fin-Aut-IsFinite : ∀ {n} → IsFinite (Aut (Fin n))
Fin-Aut-IsFinite = {!!}

Aut-IsFinite : ∀ {A} → IsFinite A → IsFinite (Aut A)
Aut-IsFinite = IsFinite-rec IsFinite-IsProp λ n → Fin-Aut-IsFinite {n = n}
