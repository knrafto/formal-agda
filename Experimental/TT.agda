module Experimental.TT where

open import Math.Fin
open import Math.Function hiding (id)
open import Math.Nat
open import Math.Type hiding (Π; _∙_)

infixl 7 _▹_
infixr 8 _*T_
infixr 8 _*t_

data Sig   : Type₀
data Ctx   : Sig → Type₀
data Ty    : ∀ {Σ} → Ctx Σ → Type₀
data Subst : ∀ {Σ} → Ctx Σ → Ctx Σ → Type₀
data Tm    : ∀ {Σ} → (Γ : Ctx Σ) → Ty Γ → Type₀

data MetaSubst : Sig → Sig → Type₀

data Ctx where
  ε   : ∀ {Σ} → Ctx Σ
  _▹_ : ∀ {Σ} → (Γ : Ctx Σ) → Ty Γ → Ctx Σ

data Sig where
  ε   : Sig
  _▹_ : (Σ : Sig) → Ty {Σ} ε → Sig

_$C_ : ∀ {Σ Σ'} → MetaSubst Σ Σ' → Ctx Σ → Ctx Σ'

data Ty where
  -- Meta substitution
  _$T_ : ∀ {Σ Σ'} {Γ : Ctx Σ} (θ : MetaSubst Σ Σ') → Ty Γ → Ty (θ $C Γ)
  -- Context substitution
  _*T_ : ∀ {Σ} {Δ Γ : Ctx Σ} → Subst Δ Γ → Ty Γ → Ty Δ

  -- Universes as object classifiers. Type : Type for now
  U  : ∀ {Σ} {Γ : Ctx Σ} → Ty Γ
  El : ∀ {Σ} {Γ : Ctx Σ} → Tm Γ U → Ty Γ

  -- Pi-types
  Π : ∀ {Σ} {Γ : Ctx Σ} (A : Ty Γ) (B : Ty (Γ ▹ A)) → Ty Γ

θ $C ε       = ε
θ $C (Γ ▹ A) = θ $C Γ ▹ θ $T A

-- Metavariable substitutions
data MetaSubst where
  -- new metavariable
  wk   : ∀ {Σ A} → MetaSubst Σ (Σ ▹ A)
  -- extend substitution
  lift : ∀ {Σ Σ' A} (θ : MetaSubst Σ Σ') → MetaSubst (Σ ▹ A) (Σ' ▹ θ $T A)
  -- term substitution
  ⟨_⟩  : ∀ {Σ A} → Tm {Σ} ε A → MetaSubst (Σ ▹ A) Σ

data Subst where
  -- category structure
  id   : ∀ {Σ} {Γ : Ctx Σ} → Subst Γ Γ
  _∙_  : ∀ {Σ} {Θ Δ Γ : Ctx Σ} → Subst Θ Δ → Subst Δ Γ → Subst Θ Γ
  -- terminal (empty) substitution
  !    : ∀ {Σ} {Γ : Ctx Σ} → Subst Γ ε
  -- weakening (parent) substitution
  wk   : ∀ {Σ} {Γ : Ctx Σ} {A} → Subst (Γ ▹ A) Γ
  -- extend substitution by pullback
  lift : ∀ {Σ} {Δ Γ : Ctx Σ} {A} (σ : Subst Δ Γ) → Subst (Δ ▹ σ *T A) (Γ ▹ A)
  -- term substitution
  ⟨_⟩  : ∀ {Σ} {Γ : Ctx Σ} {A} → Tm Γ A → Subst Γ (Γ ▹ A)

data Tm where
  -- Meta substitution
  _$t_ : ∀ {Σ Σ'} {Γ : Ctx Σ} {A} (θ : MetaSubst Σ Σ') → Tm Γ A → Tm (θ $C Γ) (θ $T A)
  -- Context substitution
  _*t_ : ∀ {Σ} {Δ Γ : Ctx Σ} {A} (σ : Subst Δ Γ) → Tm Γ A → Tm Δ (σ *T A )

  -- metavariable
  m₀ : ∀ {Σ A} → Tm {Σ = Σ ▹ A} ε (wk $T A)

  -- variable
  v₀ : ∀ {Σ} {Γ : Ctx Σ} {A} → Tm (Γ ▹ A) (wk *T A)

  -- Inverse of El ("name")
  ⌜_⌝ : ∀ {Σ} {Γ : Ctx Σ} → Ty Γ → Tm Γ U

  -- Π-types
  app : ∀ {Σ} {Γ : Ctx Σ} {A B} → Tm Γ (Π A B) → Tm (Γ ▹ A) B
  lam : ∀ {Σ} {Γ : Ctx Σ} {A B} → Tm (Γ ▹ A) B → Tm Γ (Π A B)

-- postulate
  -- TODO: identities and associativity
  -- id-∙  : ∀ {Γ Δ} (σ : Subst Γ Δ) → id ∙ σ ≡ σ

  -- Initial context
  -- !-∙ : ∀ {Γ Δ} (σ : Subst Γ Δ) → σ ∙ ! ≡ !

  -- Types: slice category C/Γ. A type A consists of a context Γ ▹ A and a morphism wk : Γ ▹ A → Γ


  -- Terms: element 1 → A of a type A as a morphism in C/Γ. Consists of a morphism Γ → Γ ▹ A such that composing with wk is the identity.
  -- ⟨⟩-∘-wk : ∀ {Γ A} (t : Tm Γ A) → ⟨ t ⟩ ∙ wk ≡ id

  -- Metavariables from the signature.

  -- Π types.
  -- TODO: app and lam are inverses
  -- TODO: relation to substitution

  -- *T-U : ∀ {Γ Δ} (σ : Subst Δ Γ) → σ *T U ≡ U
  -- TODO: other substitution properties

instantiate : ∀ {Σ} {Γ : Ctx Σ} {A} → Ty (Γ ▹ A) → Tm Γ A → Ty Γ
instantiate B a = ⟨ a ⟩ *T B

apply : ∀ {Σ} {Γ : Ctx Σ} {A B} (f : Tm Γ (Π A B)) (a : Tm Γ A) → Tm Γ (instantiate B a)
apply f a = ⟨ a ⟩ *t app f

-- de Bruijn variables
data Var : ∀ {Σ} (Γ : Ctx Σ) → Ty Γ → Type₀ where
  vzero : ∀ {Σ} {Γ : Ctx Σ} {A} → Var (Γ ▹ A) (wk *T A)
  vsuc  : ∀ {Σ} {Γ : Ctx Σ} {A B} (v : Var Γ B) → Var (Γ ▹ A) (wk *T B)

var : ∀ {Σ} {Γ : Ctx Σ} {A} → Var Γ A → Tm Γ A
var vzero    = v₀
var (vsuc v) = wk *t var v

ctxLen : ∀ {Σ} → Ctx Σ → ℕ
ctxLen ε       = zero
ctxLen (Γ ▹ _) = suc (ctxLen Γ)

{-
lookupVar : ∀ {Σ} (Γ : Ctx Σ) → Fin (ctxLen Γ) → Σ[ A ∈ Ty Γ ] Var Γ A
lookupVar ε       (_     , i<n  ) = ⊥-rec (¬-<-zero i<n)
lookupVar (Γ ▹ A) (zero  , _    ) = wk *T A  , vzero
lookupVar (Γ ▹ A) (suc i , si<sn) = let (B , v) = lookupVar Γ (i , suc-reflects-< si<sn) in wk *T B , vsuc v
-}

lookupVar : ∀ {Σ} (Γ : Ctx Σ) → Fin (ctxLen Γ) → Σ[ A ∈ Ty Γ ] Tm Γ A
lookupVar ε       (_     , i<n  ) = ⊥-rec (¬-<-zero i<n)
lookupVar (Γ ▹ A) (zero  , _    ) = wk *T A  , v₀
lookupVar (Γ ▹ A) (suc i , si<sn) = let (B , v) = lookupVar Γ (i , suc-reflects-< si<sn) in wk *T B , wk *t v

-- metavariables
data Meta : ∀ {Σ} → Ty {Σ} ε → Type₀ where
  mzero : ∀ {Σ A} → Meta {Σ ▹ A} (wk $T A)
  msuc  : ∀ {Σ B A} → Meta {Σ} B → Meta {Σ ▹ A} (wk $T B)

meta : ∀ {Σ A} → Meta {Σ} A → Tm ε A
meta mzero    = m₀
meta (msuc m) = wk $t meta m

sigLen : Sig → ℕ
sigLen ε       = zero
sigLen (Σ ▹ _) = suc (sigLen Σ)

metaIndex : ∀ {Σ A} → Meta {Σ} A → Fin (sigLen Σ)
metaIndex mzero    = fzero
metaIndex (msuc m) = fsuc (metaIndex m)

lookupMeta : (Σ : Sig) → Fin (sigLen Σ) → Σ[ A ∈ Ty {Σ} ε ] Meta A
lookupMeta ε       (_     , i<n  ) = ⊥-rec (¬-<-zero i<n)
lookupMeta (Σ ▹ A) (zero  , _    ) = wk $T A , mzero
lookupMeta (Σ ▹ A) (suc i , si<sn) = let (B , m) = lookupMeta Σ (i , suc-reflects-< si<sn) in wk $T B , msuc m

-- Unification
-- The elaborator produces a signature Σ and constraint K
-- The goal is to produce a "smaller" signature Σ' and subst θ : Σ → Σ' such that
--   K is satisfied (over Σ) iff θK is satisfied (over Σ')
--   TODO: hmm that's not right, if K is trivially true then it can make any substitution?
--   TODO: "most general unifier
-- We say the problem "typechecks" if Σ' is empty (no remaining metas) and θK is "trivially" satisfied (no remaining constraints)

-- Heterogeneous constraints
data Constraint : Sig → Type₀ where
  true  : ∀ {Σ} → Constraint Σ
  _⊢_≡_ : ∀ {Σ} → (Γ : Ctx Σ) → Σ[ A ∈ Ty Γ ] Tm Γ A → Σ[ B ∈ Ty Γ ] Tm Γ B → Constraint Σ
  _∧_   : ∀ {Σ} → Constraint Σ → Constraint Σ → Constraint Σ

IsSatisfied : ∀ {Σ} → Constraint Σ → Type₀
IsSatisfied true        = ⊤
IsSatisfied (Γ ⊢ A ≡ B) = A ≡ B
IsSatisfied (k₁ ∧ k₂)   = IsSatisfied k₁ × IsSatisfied k₂

_$K_ : ∀ {Σ Σ'} → MetaSubst Σ Σ' → Constraint Σ → Constraint Σ'
θ $K true                    = true
θ $K (Γ ⊢ (A , a) ≡ (B , b)) = (θ $C Γ) ⊢ (θ $T A , θ $t a) ≡ (θ $T B , θ $t b)
θ $K (k₁ ∧ k₂)               = (θ $K k₁) ∧ (θ $K k₂)

data Expr : ℕ → Type₀ where
  hole : ∀ {n} → Expr n
  evar : ∀ {n} → Fin n → Expr n
  eapp : ∀ {n} → Expr n → Expr n → Expr n
  elam : ∀ {n} → Expr (suc n) → Expr n
  type : ∀ {n} → Expr n
  pi   : ∀ {n} → Expr n → Expr (suc n) → Expr n
  arr  : ∀ {n} → Expr n → Expr n → Expr n
  ann  : ∀ {n} → Expr n → Expr n → Expr n

data CheckedExpr : ∀ {Σ} → Ctx Σ → Type₀
⟦_⟧ : ∀ {Σ} {Γ : Ctx Σ} → CheckedExpr Γ → Σ[ A ∈ Ty Γ ] Tm Γ A

data CheckedExpr where
  hole : ∀ {Σ} {Γ : Ctx Σ} (A : Ty Γ) (a : Tm Γ A) → CheckedExpr Γ
  evar : ∀ {Σ} {Γ : Ctx Σ} → Fin (ctxLen Γ) → CheckedExpr Γ
  eapp : ∀ {Σ} {Γ : Ctx Σ} →
    (A : Ty Γ) (B : Ty (Γ ▹ A)) (f : Tm Γ (Π A B)) (a : Tm Γ A)
    (e₁ : CheckedExpr Γ) (e₂ : CheckedExpr Γ) →
    ⟦ e₁ ⟧ ≡ (Π A B , f) →
    ⟦ e₂ ⟧ ≡ (A , a) →
    CheckedExpr Γ
  elam : ∀ {Σ} {Γ : Ctx Σ} →
    (A : Ty Γ) (B : Ty (Γ ▹ A)) (b : Tm (Γ ▹ A) B)
    (e : CheckedExpr (Γ ▹ A)) →
    ⟦ e ⟧ ≡ (B , b) →
    CheckedExpr Γ
  type : ∀ {Σ} {Γ : Ctx Σ} → CheckedExpr Γ
  pi   : ∀ {Σ} {Γ : Ctx Σ} →
    (A : Ty Γ) (B : Ty (Γ ▹ A))
    (e₁ : CheckedExpr Γ) (e₂ : CheckedExpr (Γ ▹ A)) →
    ⟦ e₁ ⟧ ≡ (U , ⌜ A ⌝) →
    ⟦ e₂ ⟧ ≡ (U , ⌜ B ⌝) →
    CheckedExpr Γ
  arr  : ∀ {Σ} {Γ : Ctx Σ} →
    (A : Ty Γ) (B : Ty Γ)
    (e₁ : CheckedExpr Γ) (e₂ : CheckedExpr Γ) →
    ⟦ e₁ ⟧ ≡ (U , ⌜ A ⌝) →
    ⟦ e₂ ⟧ ≡ (U , ⌜ B ⌝) →
    CheckedExpr Γ
  ann  : ∀ {Σ} {Γ : Ctx Σ} →
    (A : Ty Γ) (a : Tm Γ A)
    (e₁ : CheckedExpr Γ) (e₂ : CheckedExpr Γ) →
    ⟦ e₁ ⟧ ≡ (A , a) →
    ⟦ e₂ ⟧ ≡ (U , ⌜ A ⌝) →
    CheckedExpr Γ

⟦ hole A a ⟧ = (A , a)
⟦ evar i ⟧ = lookupVar _ i
⟦ eapp A B f a _ _ _ _ ⟧ = instantiate B a , apply f a
⟦ elam A B b _ _ ⟧ = (Π A B , lam b)
⟦ type ⟧ = U , ⌜ U ⌝
⟦ pi A B e₁ e₂ _ _ ⟧ = U , ⌜ Π A B ⌝
⟦ arr A B _ _ _ _ ⟧ = U , ⌜ Π A (wk *T B) ⌝
⟦ ann A a _ _ _ _ ⟧ = A , a

forget : ∀ {Σ} {Γ : Ctx Σ} → CheckedExpr Γ → Expr (ctxLen Γ)
forget (hole _ _) = hole
forget (evar i) = evar i
forget (eapp _ _ _ _ e₁ e₂ _ _) = eapp (forget e₁) (forget e₂)
forget (elam _ _ _ e _) = elam (forget e)
forget type = type
forget (pi _ _ e₁ e₂ _ _) = pi (forget e₁) (forget e₂)
forget (arr _ _ e₁ e₂ _ _) = arr (forget e₁) (forget e₂)
forget (ann _ _ e₁ e₂ _ _) = ann (forget e₁) (forget e₂)
