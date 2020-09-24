{-# OPTIONS --cubical #-}
module Experimental.TT where

open import Math.Fin
open import Math.Nat
open import Math.Type hiding (Π; _∙_)

-- Σ is the signature of metavariables
module _ (Σ : Type₀) where
  infixl 7 _▹_
  infixr 8 _*T_
  infixr 8 _*t_

  data Ctx   : Type₀
  data Ty    : Ctx → Type₀
  data Subst : Ctx → Ctx → Type₀
  data Tm    : (Γ : Ctx) → Ty Γ → Type₀

  data Ctx where
    ε   : Ctx
    _▹_ : (Γ : Ctx) → Ty Γ → Ctx

  data Ty where
    metaTy : Σ → Ty ε

    -- Substitution of types
    _*T_ : ∀ {Δ Γ} → Subst Δ Γ → Ty Γ → Ty Δ

    -- Universes as object classifiers. Type : Type for now
    U  : ∀ {Γ} → Ty Γ
    El : ∀ {Γ} → Tm Γ U → Ty Γ

    -- Pi-types
    Π : ∀ {Γ} (A : Ty Γ) (B : Ty (Γ ▹ A)) → Ty Γ

  data Subst where
    -- category structure
    id   : ∀ {Γ} → Subst Γ Γ
    _∙_  : ∀ {Θ Δ Γ} → Subst Θ Δ → Subst Δ Γ → Subst Θ Γ
    -- terminal (empty) substitution
    !    : ∀ {Γ} → Subst Γ ε
    -- weakening (parent) substitution
    wk   : ∀ {Γ A} → Subst (Γ ▹ A) Γ
    -- extend substitution by pullback
    lift : ∀ {Δ Γ A} (σ : Subst Δ Γ) → Subst (Δ ▹ σ *T A) (Γ ▹ A)
    -- term substitution
    ⟨_⟩  : ∀ {Γ A} → Tm Γ A → Subst Γ (Γ ▹ A)

  data Tm where
    metaTm : (α : Σ) → Tm ε (metaTy α)

    -- substitution of terms
    _*t_ : ∀ {Δ Γ A} (σ : Subst Δ Γ) → Tm Γ A → Tm Δ (σ *T A )
    -- variable
    v₀   : ∀ {Γ A} → Tm (Γ ▹ A) (wk *T A)

    -- Inverse of El ("name")
    ⌜_⌝ : ∀ {Γ} → Ty Γ → Tm Γ U

    -- Π-types
    app : ∀ {Γ A B} → Tm Γ (Π A B) → Tm (Γ ▹ A) B
    lam : ∀ {Γ A B} → Tm (Γ ▹ A) B → Tm Γ (Π A B)

  postulate
    -- TODO: identities and associativity
    id-∙  : ∀ {Γ Δ} (σ : Subst Γ Δ) → id ∙ σ ≡ σ

    -- Initial context
    !-∙ : ∀ {Γ Δ} (σ : Subst Γ Δ) → σ ∙ ! ≡ !

    -- Types: slice category C/Γ. A type A consists of a context Γ ▹ A and a morphism wk : Γ ▹ A → Γ


    -- Terms: element 1 → A of a type A as a morphism in C/Γ. Consists of a morphism Γ → Γ ▹ A such that composing with wk is the identity.
    -- ⟨⟩-∘-wk : ∀ {Γ A} (t : Tm Γ A) → ⟨ t ⟩ ∙ wk ≡ id

    -- Metavariables from the signature.

    -- Π types.
    -- TODO: app and lam are inverses
    -- TODO: relation to substitution

    *T-U : ∀ {Γ Δ} (σ : Subst Δ Γ) → σ *T U ≡ U
    -- TODO: other substitution properties

  instantiate : ∀ {Γ A} → Ty (Γ ▹ A) → Tm Γ A → Ty Γ
  instantiate B a = ⟨ a ⟩ *T B

  apply : ∀ {Γ A B} (f : Tm Γ (Π A B)) (a : Tm Γ A) → Tm Γ (instantiate B a)
  apply f a = ⟨ a ⟩ *t app f

  -- de Bruijn variables
  data Var : (Γ : Ctx) → Ty Γ → Type₀ where
    vzero : ∀ {Γ A} → Var (Γ ▹ A) (wk *T A)
    vsuc  : ∀ {Γ A B} (v : Var Γ B) → Var (Γ ▹ A) (wk *T B)

  var : ∀ {Γ A} → Var Γ A → Tm Γ A
  var vzero    = v₀
  var (vsuc v) = wk *t var v

  length : Ctx → ℕ
  length ε       = zero
  length (Γ ▹ _) = suc (length Γ)

  lookup : (Γ : Ctx) → Fin (length Γ) → Σ[ A ∈ Ty Γ ] Var Γ A
  lookup ε       (_     , i<n  ) = ⊥-rec (¬-<-zero i<n)
  lookup (Γ ▹ A) (zero  , _    ) = wk *T A  , vzero
  lookup (Γ ▹ A) (suc i , si<sn) = let (B , v) = lookup Γ (i , suc-reflects-< si<sn) in wk *T B , vsuc v

  lookupTy : (Γ : Ctx) → Fin (length Γ) → Ty Γ
  lookupTy Γ i = fst (lookup Γ i)

  lookupTm : (Γ : Ctx) (i : Fin (length Γ)) → Tm Γ (lookupTy Γ i)
  lookupTm Γ i = var (snd (lookup Γ i))

-- Metavariable substitutions

{-
  data Expr : ℕ → Type₀ where
    evar : ∀ {n} → Fin n → Expr n
    eapp : ∀ {n} → Expr n → Expr n → Expr n
    elam : ∀ {n} → Expr (suc n) → Expr n

  -- Typing rules for expressions Γ ⊢ e :: A ⇝ t
  data _⊢_::_⇝_ : (Γ : Ctx) → Expr (length Γ) → (A : Ty Γ) → Tm Γ A → Type₀ where
    ⊢var : ∀ {Γ i} →
      Γ ⊢ evar i :: lookupTy Γ i ⇝ lookupTm Γ i
    ⊢app : ∀ {Γ A B f f' a a'} →
      Γ ⊢ f :: Π A B ⇝ f' →
      Γ ⊢ a :: A ⇝ a' →
      Γ ⊢ eapp f a :: ⟨ a' ⟩ *T B ⇝ apply f' a'
    ⊢lam : ∀ {Γ A B e e'} →
      (Γ ▹ A) ⊢ e :: B ⇝ e' →
      Γ ⊢ elam e :: Π A B ⇝ lam e'

  ⊢subst : ∀ {Γ e A₁ t₁ A₂ t₂} → (A₁ , t₁) ≡ (A₂ , t₂) → Γ ⊢ e :: A₁ ⇝ t₁ → Γ ⊢ e :: A₂ ⇝ t₂
  ⊢subst {Γ = Γ} {e = e} p = transport λ i → Γ ⊢ e :: fst (p i) ⇝ snd (p i)

  -- Monadic type-checking
  postulate
    M      : Type₀ → Type₀
    return : ∀ {A : Type₀} → A → M A
    _>>=_  : ∀ {A B : Type₀} → M A → (A → M B) → M B
    genTy  : (Γ : Ctx) → M (Ty Γ)
    genTm  : (Γ : Ctx) (A : Ty Γ) → M (Tm Γ A)
    genEq  : ∀ {Γ} (u₁ u₂ : Σ[ A ∈ Ty Γ ] Tm Γ A) → M (u₁ ≡ u₂)

  expect : ∀ {Γ A C e} → Σ[ t ∈ Tm Γ A ] Γ ⊢ e :: A ⇝ t → M (Σ[ t ∈ Tm Γ C ] Γ ⊢ e :: C ⇝ t)
  expect {Γ = Γ} {A = A} {C = C} (e' , ⊢e) = do
    t ← genTm Γ C
    p ← genEq (A , e') (C , t)
    return (t , ⊢subst p ⊢e)

  elaborate : (Γ : Ctx) (e : Expr (length Γ)) (A : Ty Γ) → M (Σ[ t ∈ Tm Γ A ] Γ ⊢ e :: A ⇝ t)
  elaborate Γ (evar i) C = expect (lookupTm Γ i , ⊢var)
  elaborate Γ (eapp f a) C = do
    A ← genTy Γ
    B ← genTy (Γ ▹ A)
    f' , ⊢f ← elaborate Γ f (Π A B)
    a' , ⊢a ← elaborate Γ a A
    expect (apply f' a' , ⊢app ⊢f ⊢a)
  elaborate Γ (elam e) C = do
    A ← genTy Γ
    B ← genTy (Γ ▹ A)
    e' , ⊢e ← elaborate (Γ ▹ A) e B
    expect (lam e' , ⊢lam ⊢e)

data CheckedExpr : (Γ : Ctx) → Ty Γ → Type₀
exprTm : ∀ {Γ A} → CheckedExpr Γ A → Tm Γ A

data CheckedExpr where
  evar : ∀ {Γ A} (v : Var Γ A) → CheckedExpr Γ A
  eapp : ∀ {Γ A B} (f : CheckedExpr Γ (Pi A B)) (a : CheckedExpr Γ A) → CheckedExpr Γ (⟨ exprTm a ⟩ *T[ B ])
  elam : ∀ {Γ A B} (e : CheckedExpr (Γ ▹ A) B) → CheckedExpr Γ (Pi A B)

exprTm (evar v)   = varTm v
exprTm (eapp f a) = ⟨ exprTm a ⟩ *t[ app (exprTm f) ]
exprTm (elam e)   = lam (exprTm e)

unchecked : ∀ {Γ A} → CheckedExpr Γ A → UncheckedExpr (length Γ)
unchecked (evar v)   = evar (varIndex v)
unchecked (eapp f a) = eapp (unchecked f) (unchecked a)
unchecked (elam e)   = elam (unchecked e)

Term : Ctx → Type₀
Term Γ = Σ[ A ∈ Ty Γ ] Tm Γ A

MetaSubst : Type₀ → Type₀
MetaSubst M = M → Term ε

MetaTerm : Type₀ → Ctx → Type₀
MetaTerm M Γ = MetaSubst M → Term Γ

Constraint : Type₀ → Type₀
Constraint M = Σ[ Γ ∈ Ctx ] MetaTerm M Γ × MetaTerm M Γ

IsSatisified : ∀ {M} → Constraint M → MetaSubst M → Type₀
IsSatisified (Γ , t₁ , t₂) θ = t₁ θ ≡ t₂ θ

-- A unification problem is:
--   A set of metavariables
--   A set of constraints
Problem : Type₁
Problem = Σ[ M ∈ Type₀ ] Σ[ C ∈ Type₀ ] (C → Constraint M)

emptyProblem : Problem
emptyProblem = (⊥ , ⊥ , ⊥-rec)

-- A solution to a unification problem is an assignment of metavars such that all constraints are satisfied.
Solution : Problem → Type₀
Solution (M , C , constraint) = Σ[ θ ∈ MetaSubst M ] ((c : C) → IsSatisified (constraint c) θ)

checked : ∀ {Γ A} → UncheckedExpr (length Γ) → Σ[ M ∈ Problem ] (Solution M → CheckedExpr Γ A)
checked {Γ = Γ} (evar i)   = let (A , v) = lookup Γ i in
                             emptyProblem , λ _ → evar v
checked {Γ = Γ} (eapp f a) = {!!}
checked {Γ = Γ} (elam e)   = {!!}
  -- add metas α : Γ → A, β : Γ → Set, γ : Γ → β Γ → Set

data Expr : Ctx → Type₀
exprTy : ∀ {Γ} → Expr Γ → Ty Γ
exprTm : ∀ {Γ} (e : Expr Γ) → Tm Γ (exprTy e)

data Expr where
  evar : ∀ {Γ} → Var Γ → Expr Γ
  eu   : ∀ {Γ} → Expr Γ
  epi  : ∀ {Γ}
    (e₁ : Expr Γ)
    (p₁ : exprTy e₁ ≡ U)
    (e₂ : Expr (Γ ▹ El (subst (Tm _) p₁ (exprTm e₁))))
    (p₂ : exprTy e₂ ≡ U) →
    Expr Γ
  eapp : ∀ {Γ}
    (f a : Expr Γ)
    (B : Ty (Γ ▹ exprTy a))
    (p : exprTy f ≡ Pi (exprTy a) B) →
    Expr Γ
  elam : ∀ {Γ} (A : Ty Γ) → Expr (Γ ▹ A) → Expr Γ

exprTy (evar v) = varTy v
exprTy eu = U
exprTy (epi e₁ p₁ e₂ p₂) = U
exprTy (eapp f a B p) = instantiateTy (exprTm a) B
exprTy (elam A e) = Pi _ (exprTy e)

exprTm (evar v) = varTm v
exprTm eu = name U
exprTm (epi e₁ p₁ e₂ p₂) = name (Pi (El (subst (Tm _) p₁ (exprTm e₁))) (El (subst (Tm _) p₂ (exprTm e₂))))
exprTm (eapp f a B p) = instantiateTm (exprTm a) (app (subst (Tm _) p (exprTm f)))
exprTm (elam A e) = lam (exprTm e)
-}
