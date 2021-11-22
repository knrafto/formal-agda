module Math.Sum where

open import Cubical.Data.Sum using (isOfHLevelSum)

open import Math.Function
open import Math.Id
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

⊎-unassoc : A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
⊎-unassoc (inl a) = inl (inl a)
⊎-unassoc (inr (inl b)) = inl (inr b)
⊎-unassoc (inr (inr c)) = inr c

⊎-assoc-IsEquiv : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → IsEquiv (⊎-assoc {A = A} {B = B} {C = C})
⊎-assoc-IsEquiv {A = A} {B = B} {C = C} = HasInverse→IsEquiv ⊎-unassoc ⊎-unassoc-assoc ⊎-assoc-unassoc
  where
  ⊎-unassoc-assoc : (x : (A ⊎ B) ⊎ C) → ⊎-unassoc (⊎-assoc x) ≡ x
  ⊎-unassoc-assoc (inl (inl a)) = refl
  ⊎-unassoc-assoc (inl (inr b)) = refl
  ⊎-unassoc-assoc (inr c) = refl

  ⊎-assoc-unassoc : (x : A ⊎ (B ⊎ C)) → ⊎-assoc (⊎-unassoc x) ≡ x
  ⊎-assoc-unassoc (inl a) = refl
  ⊎-assoc-unassoc (inr (inl b)) = refl
  ⊎-assoc-unassoc (inr (inr c)) = refl

⊎-unassoc-IsEquiv : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → IsEquiv (⊎-unassoc {A = A} {B = B} {C = C})
⊎-unassoc-IsEquiv = inv-IsEquiv ⊎-assoc-IsEquiv

⊎-distribute : {A : Type ℓ} {B : Type ℓ'} {C : A ⊎ B → Type ℓ''} → Σ (A ⊎ B) C → (Σ A (C ∘ inl)) ⊎ (Σ B (C ∘ inr))
⊎-distribute (inl a , c) = inl (a , c)
⊎-distribute (inr b , c) = inr (b , c)

⊎-distribute-IsEquiv : {A : Type ℓ} {B : Type ℓ'} {C : A ⊎ B → Type ℓ''} → IsEquiv (⊎-distribute {A = A} {B = B} {C = C})
⊎-distribute-IsEquiv {A = A} {B = B} {C = C} = HasInverse→IsEquiv ⊎-factor ⊎-factor-distribute ⊎-distribute-factor
  where
  ⊎-factor : (Σ A (C ∘ inl)) ⊎ (Σ B (C ∘ inr)) → Σ (A ⊎ B) C
  ⊎-factor (inl (a , c)) = (inl a , c)
  ⊎-factor (inr (b , c)) = (inr b , c)

  ⊎-factor-distribute : (a : Σ (A ⊎ B) C) → ⊎-factor (⊎-distribute a) ≡ a
  ⊎-factor-distribute (inl a , c) = refl
  ⊎-factor-distribute (inr b , c) = refl

  ⊎-distribute-factor : (b : (Σ A (C ∘ inl)) ⊎ (Σ B (C ∘ inr))) → ⊎-distribute (⊎-factor b) ≡ b
  ⊎-distribute-factor (inl (a , c)) = refl
  ⊎-distribute-factor (inr (b , c)) = refl

pair : {A : Type ℓ} {B : Type ℓ'} {C : A ⊎ B → Type ℓ''} → (Π A (C ∘ inl)) × (Π B (C ∘ inr)) → Π (A ⊎ B) C
pair (f , g) (inl a) = f a
pair (f , g) (inr b) = g b

pair-IsEquiv : {A : Type ℓ} {B : Type ℓ'} {C : A ⊎ B → Type ℓ''} → IsEquiv (pair {A = A} {B = B} {C = C})
pair-IsEquiv {A = A} {B = B} {C = C} = HasInverse→IsEquiv unpair unpair-pair pair-unpair
  where
  unpair : Π (A ⊎ B) C → (Π A (C ∘ inl)) × (Π B (C ∘ inr))
  unpair h = (λ a → h (inl a)), (λ b → h (inr b))

  unpair-pair : (fg : (Π A (C ∘ inl)) × (Π B (C ∘ inr))) → unpair (pair fg) ≡ fg
  unpair-pair (f , g) = refl

  pair-unpair : (h : Π (A ⊎ B) C) → pair (unpair h) ≡ h
  pair-unpair h = funExt λ { (inl a) → refl ; (inr b) → refl }

pair-IsInjective : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {f : A → C} {g : B → C} → IsInjective f → IsInjective g → (∀ a b → ¬ f a ≡ g b) → IsInjective (pair (f , g))
pair-IsInjective f-IsInjective g-IsInjective ¬f≡g {inl _} {inl _} p = ap inl (f-IsInjective p)
pair-IsInjective f-IsInjective g-IsInjective ¬f≡g {inl a} {inr b} p = ⊥-rec (¬f≡g a b p)
pair-IsInjective f-IsInjective g-IsInjective ¬f≡g {inr b} {inl a} p = ⊥-rec (¬f≡g a b (sym p))
pair-IsInjective f-IsInjective g-IsInjective ¬f≡g {inr _} {inr _} p = ap inr (g-IsInjective p)

-- Case analysis. Especially helpful if h is of the form pair (f , g)
module _
  {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {P : C → Type ℓ'''}
  {h : A ⊎ B → C} (h-IsEquiv : IsEquiv h)
  (P-inl : ∀ a → P (h (inl a)))
  (P-inr : ∀ b → P (h (inr b)))
  where

  P-pair : (x : A ⊎ B) → P (h x)
  P-pair (inl a) = P-inl a
  P-pair (inr b) = P-inr b

  cases : ∀ c → P c
  cases c = subst P (rightInv h-IsEquiv c) (P-pair (inv h-IsEquiv c))

  cases-h : ∀ x → cases (h x) ≡ P-pair x
  cases-h x =
    ap (λ p → subst P p (P-pair (inv h-IsEquiv (h x)))) (sym (comInv h-IsEquiv x)) ∙
    apd P-pair (leftInv h-IsEquiv x)

  cases-inl : ∀ a → cases (h (inl a)) ≡ P-inl a
  cases-inl a = cases-h (inl a)

  cases-inr : ∀ b → cases (h (inr b)) ≡ P-inr b
  cases-inr b = cases-h (inr b)
