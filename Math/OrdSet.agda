module Math.OrdSet where

open import Math.Function
open import Math.Type

IsOrdSet : (A : Type₀) → (A → A → Type₀) → Type₀
IsOrdSet A R = IsSet A × (∀ a b → IsProp (R a b)) × {!!}

IsOrdSet-IsProp : ∀ A R → IsProp (IsOrdSet A R)
IsOrdSet-IsProp A R = {!!}

OrdSet : Type₁
OrdSet = Σ[ A ∈ Type₀ ] Σ[ R ∈ (A → A → Type₀) ] IsOrdSet A R

⟨_⟩ : OrdSet → Type₀
⟨ A ⟩ = fst A

order : (A : OrdSet) → ⟨ A ⟩ → ⟨ A ⟩ → Type₀
order A = fst (snd A)

-- TODO: ⟺
IsIso : (A B : OrdSet) → (⟨ A ⟩ → ⟨ B ⟩) → Type₁
IsIso A B f = IsEquiv f × (∀ x y → x <A y ≡ f x <B f y)
  where
  _<A_ = order A
  _<B_ = order B

Iso : OrdSet → OrdSet → Type₁
Iso A B = Σ[ f ∈ (⟨ A ⟩ → ⟨ B ⟩)] IsIso A B f

≡→Iso : (A B : OrdSet) → A ≡ B → Iso A B
≡→Iso A B p = f , f-IsEquiv , {!!}
  where
  ⟨A⟩≃⟨B⟩ = ≡→≃ ⟨ A ⟩ ⟨ B ⟩ (ap ⟨_⟩ p)
  f = fst ⟨A⟩≃⟨B⟩
  f-IsEquiv = snd ⟨A⟩≃⟨B⟩
  _<A_ = order A
  _<B_ = order B

≡→Iso-IsEquiv : (A B : OrdSet) → IsEquiv (≡→Iso A B)
≡→Iso-IsEquiv = {!!}

IsHom : (A B : OrdSet) → (⟨ A ⟩ → ⟨ B ⟩) → Type₀
IsHom A B f = {!!}

id-IsHom : (A : OrdSet) → IsHom A A id
id-IsHom = {!!}

∘-IsHom : (A B C : OrdSet) → ∀ g f → IsHom B C g → IsHom A B f → IsHom A C (g ∘ f)
∘-IsHom = {!!}

Hom : OrdSet → OrdSet → Type₀
Hom A B = Σ[ f ∈ (⟨ A ⟩ → ⟨ B ⟩)] IsHom A B f
