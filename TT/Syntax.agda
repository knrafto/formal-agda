{-# OPTIONS --cubical #-}
module TT.Syntax where

open import Math.Type hiding (Π)

infixl 5 _,c_
infixl 7 _[_]T
infixl 5 _,s_
infixl 6 _∘_
infixl 8 _[_]t
infixl 7 _↑_

-- Constructors.
postulate
  Con : Type₀
  Ty : Con → Type₀
  Subst : Con → Con → Type₀
  Tm : (Γ : Con) → Ty Γ → Type₀

  ∙ : Con
  _,c_ : (Γ : Con) → Ty Γ → Con

  _[_]T : ∀{Γ Δ} → Ty Δ → Subst Γ Δ → Ty Γ
  Π : ∀{Γ} → (A : Ty Γ) → (B : Ty (Γ ,c A)) → Ty Γ
  U : ∀{Γ} → Ty Γ
  El : ∀{Γ} → (t : Tm Γ U) → Ty Γ

  id : ∀{Γ} → Subst Γ Γ
  _∘_ : ∀{Γ Δ Σ} → Subst Δ Σ → Subst Γ Δ → Subst Γ Σ
  ε : ∀{Γ} → Subst Γ ∙
  _,s_ : ∀{Γ Δ}(σ : Subst Γ Δ){A : Ty Δ} → Tm Γ (A [ σ ]T) → Subst Γ (Δ ,c A)
  π₁ : ∀{Γ Δ}{A : Ty Δ} → Subst Γ (Δ ,c A) → Subst Γ Δ
  π₂ : ∀{Γ Δ}{A : Ty Δ} → (σ : Subst Γ (Δ ,c A)) → Tm Γ (A [ π₁ σ ]T)

  _[_]t : ∀{Γ Δ}{A : Ty Δ} → Tm Δ A → (σ : Subst Γ Δ) → Tm Γ (A [ σ ]T)
  app : ∀{Γ}{A : Ty Γ}{B : Ty (Γ ,c A)} → Tm Γ (Π A B) → Tm (Γ ,c A) B
  lam : ∀{Γ}{A : Ty Γ}{B : Ty (Γ ,c A)} → Tm (Γ ,c A) B → Tm Γ (Π A B)

TmΓ≡ : ∀{Γ}{A B : Ty Γ} → A ≡ B → Tm Γ A ≡ Tm Γ B
TmΓ≡ = ap (Tm _)

-- Substitution laws.
postulate
  idl : ∀{Γ Δ}{σ : Subst Γ Δ} → id ∘ σ ≡ σ
  idr : ∀{Γ Δ}{σ : Subst Γ Δ} → σ ∘ id ≡ σ
  assoc : ∀{Γ Δ Σ Ω}{σ : Subst Γ Δ}{δ : Subst Δ Σ}{θ : Subst Σ Ω}
    → (θ ∘ δ) ∘ σ ≡ θ ∘ (δ ∘ σ)

  [id]T : ∀{Γ}{A : Ty Γ} → A [ id ]T ≡ A
  [][]T : ∀{Γ Δ Σ}{A : Ty Σ}{σ : Subst Γ Δ}{δ : Subst Δ Σ}
    → A [ δ ]T [ σ ]T ≡ A [ δ ∘ σ ]T

  [id]t : ∀{Γ}{A : Ty Γ}{t : Tm Γ A} → t [ id ]t ≡[ TmΓ≡ [id]T ]≡ t
  [][]t : ∀{Γ Δ Σ}{A : Ty Σ}{t : Tm Σ A}{σ : Subst Γ Δ}{δ : Subst Δ Σ}
    → t [ δ ]t [ σ ]t ≡[ TmΓ≡ [][]T ]≡ t [ δ ∘ σ ]t

  εη : ∀{Γ}{σ : Subst Γ ∙} → σ ≡ ε
  ,s∘ : ∀{Γ Δ Σ}{σ : Subst Γ Δ}{δ : Subst Δ Σ}{A : Ty Σ}{t : Tm Δ (A [ δ ]T)}
    → (δ ,s t) ∘ σ ≡ (δ ∘ σ) ,s coe (TmΓ≡ [][]T) (t [ σ ]t)
  π₁β : ∀{Γ Δ}{σ : Subst Γ Δ}{A : Ty Δ}{t : Tm Γ (A [ σ ]T)} → π₁ (σ ,s t) ≡ σ
  π₂β : ∀{Γ Δ}{σ : Subst Γ Δ}{A : Ty Δ}{t : Tm Γ (A [ σ ]T)}
    → π₂ (σ ,s t) ≡[ TmΓ≡ (ap (_[_]T A) π₁β) ]≡ t
  πη : ∀{Γ Δ}{A : Ty Δ}{σ : Subst Γ (Δ ,c A)} → (π₁ σ ,s π₂ σ) ≡ σ

wk : ∀{Γ}{A : Ty Γ} → Subst (Γ ,c A) Γ
wk = π₁ id

_↑_ : ∀{Γ Δ} → (σ : Subst Γ Δ) (A : Ty Δ) → Subst (Γ ,c A [ σ ]T) (Δ ,c A)
σ ↑ A = σ ∘ wk ,s coe (TmΓ≡ [][]T) (π₂ id)

-- Computation rules for functions.
postulate
  Πβ : ∀{Γ}{A : Ty Γ}{B : Ty (Γ ,c A)}{t : Tm (Γ ,c A) B} → app (lam t) ≡ t
  Πη : ∀{Γ}{A : Ty Γ}{B : Ty (Γ ,c A)}{t : Tm Γ (Π A B)} → lam (app t) ≡ t

-- Action of substitution.
postulate
  Π[] : ∀{Γ Δ}{σ : Subst Γ Δ}{A : Ty Δ}{B : Ty (Δ ,c A)}
    → (Π A B) [ σ ]T ≡ Π (A [ σ ]T) (B [ σ ↑ A ]T)
  U[] : ∀{Γ Δ}{σ : Subst Γ Δ} → U [ σ ]T ≡ U
  El[] : ∀{Γ Δ}{σ : Subst Γ Δ}{t : Tm Δ U} → El t [ σ ]T ≡ U

  lam[] : ∀{Γ Δ}{σ : Subst Γ Δ}{A : Ty Δ}{B : Ty (Δ ,c A)}{t : Tm (Δ ,c A) B}
    → (lam t) [ σ ]t ≡[ TmΓ≡ Π[] ]≡ lam (t [ σ ↑ A ]t)
