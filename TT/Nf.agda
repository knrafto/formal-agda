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
  vs : ∀ {Γ A B} → Var Γ B → Var (Γ ,c A) (B [ wk ]T)

varTerm : ∀ {Γ A} → Var Γ A → Tm Γ A
varTerm vz     = π₂ id
varTerm (vs v) = varTerm v [ wk ]t

¬vz≡vs : ∀ {Γ A₀ A₁ B} (p : A₀ [ wk ]T ≡ B) (q : A₁ [ wk ]T ≡ B) (x : Var Γ A₁)
  → subst (Var (Γ ,c A₀)) p vz ≡ subst (Var (Γ ,c A₀)) q (vs x) → ⊥
¬vz≡vs {Γ = Γ} {A₀ = A₀} p q x r =
    transport (sym (Code-subst-vz p) ∙ ap Code r ∙ Code-subst-vs x q) tt
  where
    Code : ∀ {B} → Var (Γ ,c A₀) B → Type₀
    Code vz = ⊤
    Code (vs x) = ⊥

    Code-subst-vz : ∀ {B} (p : A₀ [ wk ]T ≡ B) → Code (subst (Var (Γ ,c A₀)) p vz) ≡ ⊤
    Code-subst-vz =
      pathInd (λ _ p → Code (subst (Var (Γ ,c A₀)) p vz) ≡ ⊤)
        (ap Code transport-refl)

    Code-subst-vs : ∀ {A₁ B} (x : Var Γ A₁) (q : A₁ [ wk ]T ≡ B)
      → Code (subst (Var (Γ ,c A₀)) q (vs x)) ≡ ⊥
    Code-subst-vs x =
      pathInd (λ _ q → Code (subst (Var (Γ ,c A₀)) q (vs x)) ≡ ⊥)
        (ap Code transport-refl)

vs-IsInjective : ∀ {Γ A B₀ B₁} (p : B₀ [ wk ]T ≡ B₁ [ wk ]T)
  → (x : Var Γ B₀) (y : Var Γ B₁)
  → vs x ≡[ ap (Var (Γ ,c A)) p ]≡ vs y
  → Σ (B₀ ≡ B₁) λ q → x ≡[ ap (Var Γ) q ]≡ y
vs-IsInjective {Γ = Γ} {A = A} {B₀ = B₀} p x y q = transport (sym (Code-subst-l p) ∙ ap Code q) (refl , transport-refl)
  where
    Code : ∀ {B} → Var (Γ ,c A) B → Type₀
    Code vz = ⊥
    Code (vs y) = Σ (B₀ ≡ _) λ q → x ≡[ ap (Var Γ) q ]≡ y

    Code-subst-l : ∀ {B} (p : B₀ [ wk ]T ≡ B)
      → Code (subst (Var (Γ ,c A)) p (vs x)) ≡ Σ (B₀ ≡ _) λ q → x ≡[ ap (Var Γ) q ]≡ x
    Code-subst-l =
      pathInd
        (λ _ p → Code (subst (Var (Γ ,c A)) p (vs x)) ≡ Σ (B₀ ≡ _) λ q → x ≡[ ap (Var Γ) q ]≡ x)
        (ap Code transport-refl)

decVar : ∀ {Γ A₀ A₁} → (x₀ : Var Γ A₀) → (x₁ : Var Γ A₁)
  → Dec (Σ (A₀ ≡ A₁) λ p → x₀ ≡[ ap (Var Γ) p ]≡ x₁)
decVar vz vz = yes (refl , transport-refl)
decVar vz (vs y) = no λ { (p , q) → ¬vz≡vs p refl y (q ∙ sym transport-refl) }
decVar (vs x) vz = no λ { (p , q) → ¬vz≡vs refl p x (transport-refl ∙ sym q) }
decVar (vs x) (vs y) with decVar x y
decVar {Γ = (Γ ,c B)} (vs x) (vs y) | yes (p , q) = yes (ap (λ ty → ty [ wk ]T) p , subst-fun (Var Γ) (λ ty → Var (Γ ,c B) (ty [ wk ]T)) (λ B → vs {B = B}) ∙ ap vs q)
decVar (vs x) (vs y) | no ¬d = no λ { (p , q) → ¬d (vs-IsInjective p x y q) }

data Ne : (Γ : Con) → Ty Γ → Type₀
data Nf : (Γ : Con) → Ty Γ → Type₀

neTerm : ∀ {Γ A} → Ne Γ A → Tm Γ A
nfTerm : ∀ {Γ A} → Nf Γ A → Tm Γ A

data Ne where
  neVar : ∀ {Γ A} → Var Γ A → Ne Γ A
  neApp : ∀ {Γ A B} → Ne Γ (Π A B) → (a : Nf Γ A) → Ne Γ (B [ ⟨ nfTerm a ⟩ ]T)

neApp-neVar-disjoint : ∀ {Γ A₀ A₁ B} (f : Ne Γ (Π A₀ B)) (a : Nf Γ A₀) (x : Var Γ A₁)
  → (p : B [ ⟨ nfTerm a ⟩ ]T ≡ A₁) → neApp f a ≡[ ap (Ne Γ) p ]≡ neVar x → ⊥
neApp-neVar-disjoint {Γ = Γ} {B = B} f a x p q = transport (sym (Code-subst-neApp p) ∙ ap Code q) tt
  where
    Code : ∀ {A} → Ne Γ A → Type₀
    Code (neVar x) = ⊥
    Code (neApp f a) = ⊤

    Code-subst-neApp : ∀ {A} → (p : B [ ⟨ nfTerm a ⟩ ]T ≡ A) → Code (subst (Ne Γ) p (neApp f a)) ≡ ⊤
    Code-subst-neApp = pathInd (λ _ p → Code (subst (Ne Γ) p (neApp f a)) ≡ ⊤) (ap Code transport-refl)

neVar-IsInjective : ∀ {Γ A₀ A₁} (p : A₀ ≡ A₁) (x : Var Γ A₀) (y : Var Γ A₁) → neVar x ≡[ ap (Ne Γ) p ]≡ neVar y → x ≡[ ap (Var Γ) p ]≡ y
neVar-IsInjective {Γ = Γ} {A₀ = A₀} =
  pathInd
    (λ A₁ p → (x : Var Γ A₀) (y : Var Γ A₁) → neVar x ≡[ ap (Ne Γ) p ]≡ neVar y → x ≡[ ap (Var Γ) p ]≡ y)
    λ x y q → transport-refl ∙ neVar-IsInjective' x y (sym transport-refl ∙ q)
  where
    neVar-IsInjective' : (x : Var Γ A₀) (y : Var Γ A₀) → neVar x ≡ neVar y → x ≡ y
    neVar-IsInjective' x y p = subst Code p refl
      where
        Code : Ne Γ A₀ → Type₀
        Code (neVar y) = x ≡ y
        Code (neApp c a) = ⊥

data Nf where
  nfU : ∀ {Γ} → Ne Γ U → Nf Γ U
  nfEl : ∀ {Γ t} → Ne Γ (El t) → Nf Γ (El t)
  nfLam : ∀ {Γ A B} → Nf (Γ ,c A) B → Nf Γ (Π A B)

neTerm (neVar v) = varTerm v
neTerm (neApp f a) = app (neTerm f) [ ⟨ nfTerm a ⟩ ]t

nfTerm (nfU t) = neTerm t
nfTerm (nfEl t) = neTerm t
nfTerm (nfLam t) = lam (nfTerm t)

decNe : ∀ {Γ A₀ A₁} → (n₀ : Ne Γ A₀) → (n₁ : Ne Γ A₁)
  → Dec (Σ (A₀ ≡ A₁) λ q → n₀ ≡[ ap (Ne Γ) q ]≡ n₁)
decNf : ∀ {Γ A} → (v₀ v₁ : Nf Γ A) → Dec (v₀ ≡ v₁)

decNe (neVar x) (neVar y) with decVar x y
decNe {Γ = Γ} (neVar x) (neVar y) | yes (p , q) = yes (p , subst-fun (Var Γ) (Ne Γ) (λ A → neVar {A = A}) ∙ ap neVar q)
decNe (neVar x) (neVar y) | no ¬d = no λ { (p , q) → ¬d (p , neVar-IsInjective p x y q) }
decNe {Γ = Γ} (neVar x) (neApp f a) = no λ { (p , q) → neApp-neVar-disjoint f a x (sym p) (sym-≡[]≡ (ap (Ne Γ) p) q) }
decNe (neApp f a) (neVar x) = no λ { (p , q) → neApp-neVar-disjoint f a x p q }
decNe (neApp f₀ a₀) (neApp f₁ a₁) with decNe f₀ f₁
decNe {Γ = Γ} (neApp f₀ a₀) (neApp f₁ a₁) | yes (p , q) with decNf (subst (Nf Γ) {!!} a₀) a₁
decNe (neApp f₀ a₀) (neApp f₁ a₁) | yes (p , q) | yes r = yes {!!}
decNe (neApp f₀ a₀) (neApp f₁ a₁) | yes (p , q) | no ¬r = no {!!}
decNe (neApp f₀ a₀) (neApp f₁ a₁) | no ¬d = no {!!}
