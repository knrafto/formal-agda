module Experimental.Order where

open import Math.Dec
open import Math.Fin
open import Math.Function
open import Math.Nat renaming (_<_ to _<ℕ_)
open import Math.Type
open import Experimental.Fin

Rel : Type₀ → Type₁
Rel A = A → A → Type₀

-- "Ordered" types.
Ord : Type₁
Ord = Σ[ A ∈ Type₀ ] Rel A

⟨_⟩ : Ord → Type₀
⟨ A , _ ⟩ = A

rel : (A : Ord) → Rel ⟨ A ⟩
rel (_ , <) = <

-- TODO: name
emptyRel : ∀ {A} → Rel A
emptyRel = λ _ _ → ⊥

⊥< : Ord
⊥< = ⊥ , emptyRel

⊤< : Ord
⊤< = ⊤ , emptyRel

-- TODO: infix operator precedence

-- Perhaps this would be easier if we defined coproducts in terms of Σ and 2
⊎-< : ∀ {A B} → Rel A → Rel B → Rel (A ⊎ B)
⊎-< A-< B-< (inl a₁) (inl a₂) = A-< a₁ a₂
⊎-< A-< B-< (inl a₁) (inr b₂) = ⊤
⊎-< A-< B-< (inr b₁) (inl a₂) = ⊥
⊎-< A-< B-< (inr b₁) (inr b₂) = B-< b₁ b₂

_⊎<_ : Ord → Ord → Ord
A ⊎< B = ⟨ A ⟩ ⊎ ⟨ B ⟩ , ⊎-< (rel A) (rel B)

Σ-< : ∀ {A B} → Rel A → (∀ a → Rel (B a)) → Rel (Σ A B)
Σ-< = {!!}

_Σ<_ : (A : Ord) → (⟨ A ⟩ → Ord) → Ord
A Σ< B = Σ ⟨ A ⟩ (λ a → ⟨ B a ⟩) , Σ-< (rel A) (λ a → rel (B a))

IsTotallyOrdered : Ord → Type₀
IsTotallyOrdered = {!!}

IsList : Ord → Type₀
IsList A = IsTotallyOrdered A × IsFinite ⟨ A ⟩

IsStream : Ord → Type₀
IsStream A = {!!}
