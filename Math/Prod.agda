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

×≡ : {x y : A × B} → (fst x ≡ fst y) × (snd x ≡ snd y) → x ≡ y
×≡ (p₁ , p₂) = λ i → (p₁ i , p₂ i)

×≡-IsEquiv : {x y : A × B} → IsEquiv (×≡ {x = x} {y = y})
×≡-IsEquiv = HasInverse→IsEquiv (λ p → (λ i → fst (p i)) , (λ i → snd (p i))) (λ _ → refl) (λ _ → refl)

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
