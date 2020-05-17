{-# OPTIONS --cubical #-}
module Experimental.Paxos where

open import Experimental.Tree
open import Math.Dec
open import Math.Nat
open import Math.Type

private
  variable
    ℓ ℓ' : Level

infix 6 _∈_

-- Paxos proposals must have a unique id. For simplicity, we'll let them be the
-- naturals as in most presentations.
Proposal : Type₀
Proposal = ℕ

postulate
  -- Paxos requires a set of acceptors with stable storage.
  Acceptor : Type₀

  -- Quorums, which are subsets of the acceptors.
  -- TODO: need finiteness
  Quorum : Type₀
  _∈_ : Acceptor → Quorum → Type₀
  ∈-IsProp : ∀ a q → IsProp (a ∈ q)

  -- Any two quorums overlap.
  quorumOverlap : (q₁ q₂ : Quorum) → ∥ Σ[ a ∈ Acceptor ] a ∈ q₁ × a ∈ q₂ ∥

  -- Acceptors may accept proposals. This is independent of time, so it means
  -- "was or will be accepted" rather than "is known to be accepted as of now".
  IsAccepted : Acceptor → Proposal → Type₀
  IsAccepted-IsProp : ∀ a p → IsProp (IsAccepted a p)

-- A promise not to accept a proposal in the future means its acceptance is now
-- decidable.
Promise : Acceptor → Proposal → Type₀
Promise a p = ∀ i → i < p → Dec (IsAccepted a i)

postulate
  -- Every proposal must have some quorum of acceptors that responded in the prepare phase with a promise
  prepareQuorum : Proposal → Quorum
  preparePromise : (p : Proposal) (a : Acceptor) → a ∈ prepareQuorum p → Promise a p

-- A proposal is visible to another proposal if at least one acceptor
-- in the later proposal's prepare quorum has accepted it.
IsVisible : Proposal → Proposal → Type₀
IsVisible p q = (p < q) × ∥ Σ[ a ∈ Acceptor ] a ∈ prepareQuorum q × IsAccepted a p ∥

IsVisible-IsProp : ∀ p q → IsProp (IsVisible p q)
IsVisible-IsProp p q = ×-IsProp <-IsProp ∥∥-IsProp

-- TODO: we need finite quorums for this
IsVisible-Dec : ∀ p q → Dec (IsVisible p q)
IsVisible-Dec = {!!}

-- max seen proposal (decidable)
-- TODO: make it a max
MaxVisibleProposal : Proposal → Type₀
MaxVisibleProposal p = Σ[ i ∈ Proposal ] IsVisible i p

MaxVisibleProposal-IsProp : ∀ p → IsProp (MaxVisibleProposal p)
MaxVisibleProposal-IsProp = {!!}

MaxVisibleProposal-Dec : ∀ p → Dec (MaxVisibleProposal p)
MaxVisibleProposal-Dec = {!!}

-- The tree of proposals
depth-step : (n : Proposal) → (∀ i → i < n → ℕ) → ℕ
depth-step n rec with MaxVisibleProposal-Dec n
... | yes (i , i<p , _) = suc (rec i i<p)
... | no _              = zero

depth : Proposal → ℕ
depth = <-ind depth-step

parent : ∀ {n} → (Σ[ p ∈ Proposal ] depth p ≡ suc n) → (Σ[ p ∈ Proposal ] depth p ≡ n)
parent (p , dp≡sucn) with MaxVisibleProposal-Dec p
parent (p , dp≡sucn) | yes mvp = fst mvp , suc-IsInjective (sym (lemma₁ p mvp) ∙ sym (<-ind-step depth-step p) ∙ dp≡sucn)
  where
  lemma₁ : ∀ p → (mvp : MaxVisibleProposal p) → depth-step p (λ i _ → depth i) ≡ suc (depth (fst mvp))
  lemma₁ p mvp with MaxVisibleProposal-Dec p
  ... | yes mvp' = ap (λ mvp → suc (depth (fst mvp))) (MaxVisibleProposal-IsProp p mvp' mvp)
  ... | no ¬mvp  = ⊥-elim (¬mvp mvp)

parent (p , dp≡sucn) | no ¬mvp = ⊥-elim (¬zero≡suc (sym (lemma₂ p ¬mvp) ∙ dp≡sucn))
  where
  lemma₁ : ∀ p → ¬ (MaxVisibleProposal p) → depth-step p (λ i _ → depth i) ≡ zero
  lemma₁ p ¬mvp with MaxVisibleProposal-Dec p
  ... | yes mvp = ⊥-elim (¬mvp mvp)
  ... | no _    = refl

  lemma₂ : ∀ p → ¬ (MaxVisibleProposal p) → depth p ≡ zero
  lemma₂ p ¬mvp = <-ind-step depth-step p ∙ lemma₁ p ¬mvp

-- For ≤T and friends
open Tree Proposal ℕ-IsSet depth parent

-- We say a proposal is "acked" if it is accepted by a quorum of acceptors. This
-- is independent of time, so it means "was or will be acked" rather than
-- "is known to be acked as of now".
IsAcked : Proposal → Type₀
IsAcked p = ∥ Σ[ q ∈ Quorum ] ((a : Acceptor) → a ∈ q → IsAccepted a p) ∥

IsAcked-IsProp : ∀ p → IsProp (IsAcked p)
IsAcked-IsProp p = ∥∥-IsProp

-- Acked proposals are always visible to later proposals, because the quorum that acked this
-- proposal overlaps the prepare quorum for the later proposal.
IsAcked-IsVisible : ∀ p q → p < q → IsAcked p → IsVisible p q
IsAcked-IsVisible p q p<q =
   ∥∥-rec (IsVisible-IsProp p q) λ { (Qp , Qp-IsAccepted) →
   with-∥∥ (quorumOverlap Qp (prepareQuorum q)) (IsVisible-IsProp p q) λ { (a , a∈Qp , a∈Qq) →
   p<q , ∣ a , a∈Qq , Qp-IsAccepted a a∈Qp ∣ } }

-- Thus, acked proposals are always ancestors to later proposals.
IsAcked-≤T : ∀ p q → IsAcked p → p < q → p ≤T q
IsAcked-≤T p = <-ind λ q rec p-IsAcked p<q →
  let mvp = {!!}
      i = fst mvp
  in
  case p ≟ i return p ≤T q of λ
    { (lt p<i) → ≤T-trans p i q (rec i {!!} p-IsAcked p<i) {!!}
    ; (eq p≡i) → {!!}
    ; (gt i<p) → {!!}
    } 

-- We say a proposal is "committed" if it is the ancestor of an acked proposal.
IsCommitted : Proposal → Type₀
IsCommitted p = ∥ Σ[ q ∈ Proposal ] IsAcked q × p ≤T q ∥

IsCommitted-IsProp : ∀ p → IsProp (IsCommitted p)
IsCommitted-IsProp p = ∥∥-IsProp

-- The ancestor of committed proposal is committed
ancestor-IsCommitted : ∀ p₁ p₂ → p₁ ≤T p₂ → IsCommitted p₂ → IsCommitted p₁
ancestor-IsCommitted p₁ p₂ p₁≤Tp₂ =
  ∥∥-rec (IsCommitted-IsProp p₁) λ { (q , q-IsAcked , p₂≤Tq) →
    ∣ q , q-IsAcked , ≤T-trans p₁ p₂ q p₁≤Tp₂ p₂≤Tq ∣ }

-- There is at most one committed proposal at each depth
committed-unique : ∀ p₁ p₂ → depth p₁ ≡ depth p₂
  → IsCommitted p₁ → IsCommitted p₂ → p₁ ≡ p₂
committed-unique p₁ p₂ dp₁≡dp₂ =
  ∥∥-rec (Π-IsProp λ _ → ℕ-IsSet p₁ p₂) λ { (q₁ , q₁-IsAcked , p₁≤Tq₁) →
  ∥∥-rec (ℕ-IsSet p₁ p₂) λ { (q₂ , q₂-IsAcked , p₂≤Tq₂) →
  case q₁ ≟ q₂ return p₁ ≡ p₂ of λ
    { (lt q₁<q₂) → ≤T-unique p₁ p₂ q₂
      (≤T-trans p₁ q₁ q₂ p₁≤Tq₁ (IsAcked-≤T q₁ q₂ q₁-IsAcked q₁<q₂))
      p₂≤Tq₂
      dp₁≡dp₂
    ; (eq q₁≡q₂) → ≤T-unique p₁ p₂ q₂ (subst (p₁ ≤T_) q₁≡q₂ p₁≤Tq₁) p₂≤Tq₂ dp₁≡dp₂
    ; (gt q₂<q₁) → ≤T-unique p₁ p₂ q₁
      p₁≤Tq₁
      (≤T-trans p₂ q₂ q₁ p₂≤Tq₂ (IsAcked-≤T q₂ q₁ q₂-IsAcked q₂<q₁))
      dp₁≡dp₂
    } } }
