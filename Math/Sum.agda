{-# OPTIONS --cubical #-}
module Math.Sum where

open import Cubical.Data.Sum using (isOfHLevelSum)

open import Math.Function
open import Math.Type

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    A : Type ℓ
    B : Type ℓ'
    C : Type ℓ''
    D : Type ℓ'''

⊎-IsSet : IsSet A → IsSet B → IsSet (A ⊎ B)
⊎-IsSet = isOfHLevelSum 0

⊥-inr-IsEquiv : {A : Type ℓ} → IsEquiv (inr {A = ⊥} {B = A})
⊥-inr-IsEquiv {A = A} = HasInverse→IsEquiv ⊥-inr-inv ⊥-inr-leftInv ⊥-inr-rightInv
  where
  ⊥-inr-inv : ⊥ ⊎ A → A
  ⊥-inr-inv (inr a) = a

  ⊥-inr-leftInv : (a : A) → ⊥-inr-inv (inr a) ≡ a
  ⊥-inr-leftInv a = refl

  ⊥-inr-rightInv : (b : ⊥ ⊎ A) → inr (⊥-inr-inv b) ≡ b
  ⊥-inr-rightInv (inr a) = refl

⊎-map : (A → C) → (B → D) → (A ⊎ B → C ⊎ D)
⊎-map f g (inl a) = inl (f a)
⊎-map f g (inr b) = inr (g b)

⊎-map-IsEquiv : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''} {f : A → C} {g : B → D} → IsEquiv f → IsEquiv g → IsEquiv (⊎-map f g)
⊎-map-IsEquiv {A = A} {B = B} {C = C} {D = D} {f = f} {g = g} f-IsEquiv g-IsEquiv = HasInverse→IsEquiv (⊎-map (inv f-IsEquiv) (inv g-IsEquiv)) ⊎-map-leftInv ⊎-map-rightInv
  where
  ⊎-map-leftInv : (x : A ⊎ B) → ⊎-map (inv f-IsEquiv) (inv g-IsEquiv) (⊎-map f g x) ≡ x
  ⊎-map-leftInv (inl a) = ap inl (leftInv f-IsEquiv a)
  ⊎-map-leftInv (inr b) = ap inr (leftInv g-IsEquiv b)

  ⊎-map-rightInv : (y : C ⊎ D) → ⊎-map f g (⊎-map (inv f-IsEquiv) (inv g-IsEquiv) y) ≡ y
  ⊎-map-rightInv (inl c) = ap inl (rightInv f-IsEquiv c)
  ⊎-map-rightInv (inr d) = ap inr (rightInv g-IsEquiv d)

⊎-assoc : (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
⊎-assoc (inl (inl a)) = inl a
⊎-assoc (inl (inr b)) = inr (inl b)
⊎-assoc (inr c) = inr (inr c)

⊎-assoc-IsEquiv : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → IsEquiv (⊎-assoc {A = A} {B = B} {C = C})
⊎-assoc-IsEquiv {A = A} {B = B} {C = C} = HasInverse→IsEquiv ⊎-unassoc ⊎-unassoc-assoc ⊎-assoc-unassoc
  where
  ⊎-unassoc : A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
  ⊎-unassoc (inl a) = inl (inl a)
  ⊎-unassoc (inr (inl b)) = inl (inr b)
  ⊎-unassoc (inr (inr c)) = inr c

  ⊎-unassoc-assoc : (x : (A ⊎ B) ⊎ C) → ⊎-unassoc (⊎-assoc x) ≡ x
  ⊎-unassoc-assoc (inl (inl a)) = refl
  ⊎-unassoc-assoc (inl (inr b)) = refl
  ⊎-unassoc-assoc (inr c) = refl

  ⊎-assoc-unassoc : (x : A ⊎ (B ⊎ C)) → ⊎-assoc (⊎-unassoc x) ≡ x
  ⊎-assoc-unassoc (inl a) = refl
  ⊎-assoc-unassoc (inr (inl b)) = refl
  ⊎-assoc-unassoc (inr (inr c)) = refl

⊎-distribute : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → (A ⊎ B) × C → (A × C) ⊎ (B × C)
⊎-distribute (inl a , c) = inl (a , c)
⊎-distribute (inr b , c) = inr (b , c)

⊎-distribute-IsEquiv : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → IsEquiv (⊎-distribute {A = A} {B = B} {C = C})
⊎-distribute-IsEquiv = HasInverse→IsEquiv ⊎-factor ⊎-factor-distribute ⊎-distribute-factor
  where
  ⊎-factor : (A × C) ⊎ (B × C) → (A ⊎ B) × C
  ⊎-factor (inl (a , c)) = (inl a , c)
  ⊎-factor (inr (b , c)) = (inr b , c)

  ⊎-factor-distribute : (a : (A ⊎ B) × C) → ⊎-factor (⊎-distribute a) ≡ a
  ⊎-factor-distribute (inl a , c) = refl
  ⊎-factor-distribute (inr b , c) = refl

  ⊎-distribute-factor : (b : (A × C) ⊎ (B × C)) → ⊎-distribute (⊎-factor b) ≡ b
  ⊎-distribute-factor (inl (a , c)) = refl
  ⊎-distribute-factor (inr (b , c)) = refl

pair : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → (A → C) × (B → C) → (A ⊎ B → C)
pair (f , g) (inl a) = f a
pair (f , g) (inr b) = g b

pair-IsEquiv : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → IsEquiv (pair {A = A} {B = B} {C = C})
pair-IsEquiv = HasInverse→IsEquiv unpair unpair-pair pair-unpair
  where
  unpair : (A ⊎ B → C) → (A → C) × (B → C)
  unpair h = (λ a → h (inl a)), (λ b → h (inr b))

  unpair-pair : (fg : (A → C) × (B → C)) → unpair (pair fg) ≡ fg
  unpair-pair (f , g) = refl

  pair-unpair : (h : A ⊎ B → C) → pair (unpair h) ≡ h
  pair-unpair h = funExt λ { (inl a) → refl ; (inr b) → refl }

pair-IsInjective : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {f : A → C} {g : B → C} → IsInjective f → IsInjective g → (∀ a b → ¬ f a ≡ g b) → IsInjective (pair (f , g))
pair-IsInjective f-IsInjective g-IsInjective ¬f≡g {inl _} {inl _} p = ap inl (f-IsInjective p)
pair-IsInjective f-IsInjective g-IsInjective ¬f≡g {inl a} {inr b} p = ⊥-rec (¬f≡g a b p)
pair-IsInjective f-IsInjective g-IsInjective ¬f≡g {inr b} {inl a} p = ⊥-rec (¬f≡g a b (sym p))
pair-IsInjective f-IsInjective g-IsInjective ¬f≡g {inr _} {inr _} p = ap inr (g-IsInjective p)
