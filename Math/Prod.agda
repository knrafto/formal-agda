{-# OPTIONS --cubical #-}
module Math.Prod where

open import Math.Function
open import Math.Type

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    A : Type ℓ
    B : Type ℓ'
    C : Type ℓ''
    D : Type ℓ'''

×-IsSet : IsSet A → IsSet B → IsSet (A × B)
×-IsSet A-IsSet B-IsSet = Σ-IsSet A-IsSet λ _ → B-IsSet

×≡ : {x y : A × B} → (fst x ≡ fst y) × (snd x ≡ snd y) → x ≡ y
×≡ (p₁ , p₂) = λ i → (p₁ i , p₂ i)

×≡-IsEquiv : {x y : A × B} → IsEquiv (×≡ {x = x} {y = y})
×≡-IsEquiv = HasInverse→IsEquiv (λ p → (λ i → fst (p i)) , (λ i → snd (p i))) (λ _ → refl) (λ _ → refl)

⊤-fst-IsEquiv : {A : Type ℓ} → IsEquiv (fst {A = A} {B = λ _ → ⊤})
⊤-fst-IsEquiv = HasInverse→IsEquiv (λ a → (a , tt)) (λ { (a , tt) → refl }) (λ _ → refl)

⊤-snd-IsEquiv : {A : Type ℓ} → IsEquiv (snd {A = ⊤} {B = λ _ → A})
⊤-snd-IsEquiv = HasInverse→IsEquiv (λ a → (tt , a)) (λ { (tt , a) → refl }) (λ _ → refl)

×-map : (A → C) → (B → D) → (A × B → C × D)
×-map f g c = (f (fst c) , g (snd c))

×-map-IsEquiv : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''} {f : A → C} {g : B → D} → IsEquiv f → IsEquiv g → IsEquiv (×-map f g)
×-map-IsEquiv {A = A} {B = B} {C = C} {D = D} {f = f} {g = g} f-IsEquiv g-IsEquiv =
  HasInverse→IsEquiv (×-map (inv f-IsEquiv) (inv g-IsEquiv)) ×-map-leftInv ×-map-rightInv
  where
  ×-map-leftInv : (x : A × B) → ×-map (inv f-IsEquiv) (inv g-IsEquiv) (×-map f g x) ≡ x
  ×-map-leftInv (a , b) = ×≡ (leftInv f-IsEquiv a , leftInv g-IsEquiv b)

  ×-map-rightInv : (x : C × D) → ×-map f g (×-map (inv f-IsEquiv) (inv g-IsEquiv) x) ≡ x
  ×-map-rightInv (c , d) = ×≡ (rightInv f-IsEquiv c , rightInv g-IsEquiv d)

×-map-IsEmbedding : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''} {f : A → C} {g : B → D} → IsEmbedding f → IsEmbedding g → IsEmbedding (×-map f g)
×-map-IsEmbedding {A = A} {B = B} {C = C} {D = D} {f = f} {g = g} f-IsEmbedding g-IsEmbedding _ _ =
  ×≡-IsEquiv ∘-IsEquiv (×-map-IsEquiv (f-IsEmbedding _ _) (g-IsEmbedding _ _)) ∘-IsEquiv (inv-IsEquiv ×≡-IsEquiv)

×-swap : {A : Type ℓ} {B : Type ℓ'} → A × B → B × A
×-swap (a , b) = (b , a)

×-swap-IsEquiv : {A : Type ℓ} {B : Type ℓ'} → IsEquiv (×-swap {A = A} {B = B})
×-swap-IsEquiv = HasInverse→IsEquiv ×-swap (λ { (a , b) → refl }) (λ { (b , a) → refl })

c,-IsEmbedding : {A : Type ℓ} {B : Type ℓ'} → IsSet A → {c : A} → IsEmbedding {A = B} (c ,_)
c,-IsEmbedding A-IsSet = ×-map-IsEmbedding (⊤-rec-IsEmbedding A-IsSet) (IsEquiv→IsEmbedding id-IsEquiv) ∘-IsEmbedding IsEquiv→IsEmbedding (inv-IsEquiv ⊤-snd-IsEquiv)

,c-IsEmbedding : {A : Type ℓ} {B : Type ℓ'} → IsSet B → {c : B} → IsEmbedding {A = A} (_, c)
,c-IsEmbedding B-IsSet = ×-map-IsEmbedding (IsEquiv→IsEmbedding id-IsEquiv) (⊤-rec-IsEmbedding B-IsSet) ∘-IsEmbedding IsEquiv→IsEmbedding (inv-IsEquiv ⊤-fst-IsEquiv)
