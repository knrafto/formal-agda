{-# OPTIONS --cubical #-}
module TT.Nf where

open import Math.Dec
open import Math.Id
open import Math.Type hiding (Π)
open import TT.Term

-- See Agda's internal representation:
-- https://github.com/agda/agda/blob/4ed20e8548f5ce88b5f68d0b284002cd8a5bd1d4/src/full/Agda/Syntax/Internal.hs#L188
-- See also nbe-for-tt-in-tt: https://arxiv.org/pdf/1612.02462.pdf

,c-IsInjective : ∀ {Γ₀ A₀ Γ₁ A₁} → (Γ₀ ,c A₀) ≡ (Γ₁ ,c A₁) → Σ (Γ₀ ≡ Γ₁) λ p → A₀ ≡[ ap Ty p ]≡ A₁
,c-IsInjective {Γ₀ = Γ₀} {A₀ = A₀} p = subst Code p (refl , transport-refl)
  where
    Code : Con → Type₀
    Code [] = ⊥
    Code (Γ ,c A) = Σ (Γ₀ ≡ Γ) λ p → A₀ ≡[ ap Ty p ]≡ A

data Var : (Γ : Con) → Ty Γ → Type₀ where
  vz : ∀ {Γ A} → Var (Γ ,c A) (A [ wk ]T)
  vs : ∀ {Γ A B} → Var Γ A → Var (Γ ,c B) (A [ wk ]T)

varTerm : ∀ {Γ A} → Var Γ A → Tm Γ A
varTerm vz     = π₂ id
varTerm (vs v) = varTerm v [ wk ]t

data Ne : (Γ : Con) → Ty Γ → Type₀
data Nf : (Γ : Con) → Ty Γ → Type₀

neTerm : ∀ {Γ A} → Ne Γ A → Tm Γ A
nfTerm : ∀ {Γ A} → Nf Γ A → Tm Γ A

data Ne where
  neVar : ∀ {Γ A} → Var Γ A → Ne Γ A
  neApp : ∀ {Γ A B} → Ne Γ (Π A B) → (a : Nf Γ A) → Ne Γ (B [ ⟨ nfTerm a ⟩ ]T)

data Nf where
  nfU : ∀ {Γ} → Ne Γ U → Nf Γ U
  nfEl : ∀ {Γ t} → Ne Γ (El t) → Nf Γ (El t)
  nfLam : ∀ {Γ A B} → Nf (Γ ,c A) B → Nf Γ (Π A B)

neTerm (neVar v) = varTerm v
neTerm (neApp f a) = app (neTerm f) [ ⟨ nfTerm a ⟩ ]t

nfTerm (nfU t) = neTerm t
nfTerm (nfEl t) = neTerm t
nfTerm (nfLam t) = lam (nfTerm t)

¬vz≡vs : ∀ {Γ A₀ A₁} → (x : Var Γ A₁) (p : A₀ [ wk ]T ≡ A₁ [ wk ]T) → vz ≡[ ap (Var (Γ ,c A₀)) p ]≡ vs x → ⊥
¬vz≡vs = {!!}

decVar : ∀ {Γ A₀ A₁} → (x₀ : Var Γ A₀) → (x₁ : Var Γ A₁)
  → Dec (Σ (A₀ ≡ A₁) λ p → x₀ ≡[ ap (Var Γ) p ]≡ x₁)
decVar vz vz = yes (refl , transport-refl)
decVar vz (vs y) = no λ { (p , q) → {!!} }
decVar (vs x) vz = no λ { (p , q) → {!!} }
decVar (vs x) (vs y) with decVar x y
decVar {Γ = (Γ ,c B)} (vs x) (vs y) | yes (p , q) = yes (ap (λ ty → ty [ wk ]T) p , subst-fun (Var Γ) (λ ty → Var (Γ ,c B) (ty [ wk ]T)) (λ A → vs {A = A}) ∙ ap vs q)
decVar (vs x₀) (vs x₁) | no ¬d = no {!!}

decNe : ∀ {Γ A₀ A₁} → (n₀ : Ne Γ A₀) → (n₁ : Ne Γ A₁)
  → Dec (Σ (A₀ ≡ A₁) λ q → n₀ ≡[ ap (Ne Γ) q ]≡ n₁)
decNf : ∀ {Γ A} → (v₀ v₁ : Nf Γ A) → Dec (v₀ ≡ v₁)

decNe (neVar x) (neVar y) with decVar x y
decNe {Γ = Γ} (neVar x) (neVar y) | yes (p , q) = yes (p , subst-fun (Var Γ) (Ne Γ) (λ A → neVar {A = A}) ∙ ap neVar q)
decNe (neVar x) (neVar y) | no ¬d = no λ { (p , q) → ¬d (p , {!!}) }
decNe (neVar x) (neApp f a) = no {!!}
decNe (neApp f a) (neVar x) = no {!!}
decNe (neApp f₀ a₀) (neApp f₁ a₁) with decNe f₀ f₁
decNe (neApp f₀ a₀) (neApp f₁ a₁) | yes (p , q) = {!!}
decNe (neApp f₀ a₀) (neApp f₁ a₁) | no ¬d = no {!!}
