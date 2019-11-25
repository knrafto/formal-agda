{-# OPTIONS --cubical #-}
module TT.Nf where

open import Math.Type hiding (Π)
open import TT.Term

-- Agda's internal representation:
-- https://github.com/agda/agda/blob/4ed20e8548f5ce88b5f68d0b284002cd8a5bd1d4/src/full/Agda/Syntax/Internal.hs#L188
-- See also nbe-for-tt-in-tt: https://arxiv.org/pdf/1612.02462.pdf

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
