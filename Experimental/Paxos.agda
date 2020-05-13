{-# OPTIONS --cubical #-}
module Experimental.Paxos where

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
  Quorum : Type₀
  _∈_ : Acceptor → Quorum → Type₀
  ∈-IsProp : ∀ a q → IsProp (a ∈ q)

  -- Any two quorums overlap.
  quorumOverlap : (q₁ q₂ : Quorum) → ∥ Σ[ a ∈ Acceptor ] a ∈ q₁ × a ∈ q₂ ∥

  -- Acceptors may accept proposals.
  IsAccepted : Acceptor → Proposal → Type₀
  IsAccepted-IsProp : ∀ a p → IsProp (IsAccepted a p)

-- A promise not to accept a proposal in the future means its acceptance is now
-- decidable.
Promise : Acceptor → Proposal → Type₀
Promise a p = ∀ i → i < p → Dec (IsAccepted a i)

postulate
  -- Every proposal must have some quorum of acceptors that responded to the
  -- prepare phase
  prepareQuorum : Proposal → Quorum
  preparePromise : (p : Proposal) (a : Acceptor) → a ∈ prepareQuorum p → Promise a p

-- We say a proposal is chosen if it is accepted by a quorum of acceptors. This
-- is independent of time, so it means "was or will be chosen" rather than
-- "is known to be chosen as of now".
IsChosen : Proposal → Type₀
IsChosen p = ∥ Σ[ q ∈ Quorum ] ((a : Acceptor) → a ∈ q → IsAccepted a p) ∥

-- Acceptors may accept proposals.
IsChosen-IsProp : ∀ p → IsProp (IsChosen p)
IsChosen-IsProp _ = ∥∥-IsProp

IsSeen : Proposal → Proposal → Type₀
IsSeen p q = ∥ Σ[ a ∈ Acceptor ] (a ∈ prepareQuorum q → p < q → IsAccepted a p) ∥

IsSeen-IsProp : ∀ p q → IsProp (IsSeen p q)
IsSeen-IsProp _ _ = ∥∥-IsProp

-- TODO: we need finite quorums for this
IsSeen-Dec : ∀ p q → Dec (IsSeen p q)
IsSeen-Dec = {!!}

-- max seen proposal (decidable)
MaxSeenProposal : Proposal → Type₀
MaxSeenProposal p = Σ[ i ∈ Proposal ] {!!}

MaxSeenProposal-IsProp : ∀ p → IsProp (MaxSeenProposal p)
MaxSeenProposal-IsProp = {!!}

MaxSeenProposal-Dec : ∀ p → Dec (MaxSeenProposal p)
MaxSeenProposal-Dec = {!!}

-- depth and parent of proposals
depth : Proposal → ℕ
depth p with MaxSeenProposal-Dec p
depth p | yes (i , _) = {!!}
depth p | no  _       = 0

-- ancestor relation
-- chosen proposals are always ancestors
-- committed proposal
-- parent of committed proposal is committed
-- at most one committed proposal at each depth
