{-# OPTIONS --cubical #-}
-- See https://www.cs.bham.ac.uk/~mhe/agda/Dcpo.html#2802
module Systems.Dcpo where

open import Math.Nat
open import Math.Type

-- TODO: move to Math.Type
Sigma : {ℓ ℓ' : Level} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
Sigma A B = Σ A B

syntax Sigma A (λ x → b) = Σ x ∈ A , b

infixr -1 Sigma

module _ {ℓ} {A : Type ℓ} (_≤_ : A → A → Type ℓ) where
  IsReflexive : Type ℓ
  IsReflexive = ∀ a → a ≤ a

  IsTransitive : Type ℓ
  IsTransitive = ∀ a b c → a ≤ b → b ≤ c → a ≤ c

  IsAntisymmetric : Type ℓ
  IsAntisymmetric = ∀ a b → a ≤ b → b ≤ a → a ≡ b

  IsPoset : Type ℓ
  IsPoset = IsSet A × (∀ a b → IsProp (a ≤ b)) × IsReflexive × IsTransitive × IsAntisymmetric

  Col : Type (ℓ-suc ℓ)
  Col = Σ I ∈ Type ℓ , I → A

  IsMin : (S : Col) → A → Type ℓ
  IsMin S m = {!!}

  {-
  IsMin : A → Type ℓ
  IsMin m = ∀ a → m ≤ a

  IsMin-IsProp : IsPoset → (m : A) → IsProp (IsMin m)
  IsMin-IsProp (_ , ≤-IsProp , _) m = Π-IsProp λ a → ≤-IsProp m a

  HasMin : Type ℓ
  HasMin = Σ m ∈ A , IsMin m

  HasMin-IsProp : IsPoset → IsProp HasMin
  HasMin-IsProp ≤-IsPoset@(_ , _ , _ , _ , ≤-antisym) (m₁ , m₁-IsMin) (m₂ , m₂-IsMin) =
    ΣProp≡ (IsMin-IsProp ≤-IsPoset) (≤-antisym _ _ (m₁-IsMin m₂) (m₂-IsMin m₁))

  IsUpperBound : {I : Type ℓ} → (I → A) → A → Type ℓ
  IsUpperBound {I} S m = ∀ i → S i ≤ m

  IsSup : {I : Type ℓ} → (I → A) → A → Type ℓ
  IsSup {I} S m = IsUpperBound S m × (∀ m' → IsUpperBound S m' → m ≤ m)

  HasSup : {I : Type ℓ} → (I → A) → Type ℓ
  HasSup S = Σ m ∈ A , IsSup S m

  HasSup-IsProp : {I : Type ℓ} (S : I → A) → IsProp (HasSup S)
  HasSup-IsProp = {!!}
  -}

F : Type₀ → Type₁
F A = Σ P ∈ Type₀ , IsProp P × (P → A)

module _ (A : Type₀) where
  F-IsSet : IsSet A → IsSet (F A)
  F-IsSet A-IsSet = {!!}

  IsDef : F A → Type₀
  IsDef (P , _ , _) = P

  IsDef-IsProp : (x : F A) → IsProp (IsDef x)
  IsDef-IsProp (P , P-IsProp , _) = P-IsProp

  value : (x : F A) → IsDef x → A
  value (_ , _ , f) p = f p

  undef : F A
  undef = ⊥ , ⊥-IsProp , ⊥-rec

  def : A → F A
  def a = ⊤ , ⊤-IsProp , ⊤-rec a

  _⊑_ : F A → F A → Type₁
  x ⊑ y = IsDef x → x ≡ y

  ⊑-IsReflexive : IsReflexive _⊑_
  ⊑-IsReflexive x p = refl

  ⊑-IsTransitive : IsTransitive _⊑_
  ⊑-IsTransitive x y z x⊑y y⊑z p = x≡y ∙ y⊑z (subst IsDef x≡y p)
    where
    x≡y : x ≡ y
    x≡y = x⊑y p

  ⊑-IsAntisymmetric : IsAntisymmetric _⊑_
  ⊑-IsAntisymmetric x y x⊑y y⊑x = {!!}
    -- IsDef x ⟺ IsDef y

  undef-⊑ : ∀ x → undef ⊑ x
  undef-⊑ x = ⊥-rec

  ω-colimit : (f : ℕ → F A) → (∀ {i j} → i ≤ j → f i ⊑ f j) → F A
  ω-colimit f f-IsMonotone = DefIndex , DefIndex-IsProp , λ { (n , fn-IsDef , _) → value (f n) fn-IsDef }
    where
    DefIndex : Type₀
    DefIndex = Σ n ∈ ℕ , IsDef (f n) × (∀ i → IsDef (f i) → n ≤ i)

    DefIndex-IsProp : IsProp DefIndex
    DefIndex-IsProp = {!!}


module _ {I : Type₀} where

{-

  IsSup : {I : Type ℓ} → (I → A) → A → Type ℓ
  IsSup m = {!!}

  HasSup : {I : Type ℓ} → (I → A) → Type ℓ
  HasSup = {!Σ[ m ∈ A ] IsSup m!}

  IsDirectedComplete : Type ℓ
  IsDirectedComplete = (I : Type ℓ) (α : I → A) → IsDirected α → HasSup α

  IsDcpo : ∀ {i} → Type (ℓ-max (ℓ-suc i) ℓ)
  IsDcpo {i} = IsPoset × IsDirectedComplete {i = i}
  -}
