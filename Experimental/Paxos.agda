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

-- depth of proposals
depth : Proposal → ℕ
depth p with MaxSeenProposal-Dec p
depth p | yes (i , _) = {!!}
depth p | no  _       = 0

-- parent of proposals
parent : ∀ n → (Σ[ p ∈ Proposal ] depth p ≡ suc n) → (Σ[ p ∈ Proposal ] depth p ≡ n)
parent = {!!}

-- ancestor relation
_≤T_ : Proposal → Proposal → Type₀
_≤T_ = {!!}

≤T-IsProp : ∀ p q → IsProp (p ≤T q)
≤T-IsProp = {!!}

≤T-Dec : ∀ p q → Dec (p ≤T q)
≤T-Dec = {!!}

≤T-trans : ∀ p q r → p ≤T q → q ≤T r → p ≤T r
≤T-trans = {!!}

-- only one ancestor at each depth
ancestor-unique : ∀ p₁ p₂ q → depth p₁ ≡ depth p₂ → p₁ ≤T q → p₂ ≤T q → p₁ ≡ p₂
ancestor-unique = {!!}

-- chosen proposals are always ancestors
chosen-≤T : ∀ p q → p < q → IsChosen p → p ≤T q
chosen-≤T = {!!}

IsCommitted : Proposal → Type₀
IsCommitted p = ∥ Σ[ q ∈ Proposal ] IsChosen q × p ≤T q ∥

IsCommitted-IsProp : ∀ p → IsProp (IsCommitted p)
IsCommitted-IsProp p = ∥∥-IsProp

-- ancestor of committed proposal is committed
ancestor-IsCommitted : ∀ p₁ p₂ → p₁ ≤T p₂ → IsCommitted p₂ → IsCommitted p₁
ancestor-IsCommitted p₁ p₂ p₁≤Tp₂ =
  ∥∥-rec (IsCommitted-IsProp p₁) λ { (q , q-IsChosen , p₂≤Tq) →
    ∣ q , q-IsChosen , ≤T-trans p₁ p₂ q p₁≤Tp₂ p₂≤Tq ∣ }

-- at most one committed proposal at each depth
committed-unique : ∀ p₁ p₂ → depth p₁ ≡ depth p₂
  → IsCommitted p₁ → IsCommitted p₂ → p₁ ≡ p₂
committed-unique p₁ p₂ dp₁≡dp₂ =
  ∥∥-rec (Π-IsProp λ _ → ℕ-IsSet p₁ p₂) λ { (q₁ , q₁-IsChosen , p₁≤Tq₁) →
  ∥∥-rec (ℕ-IsSet p₁ p₂) λ { (q₂ , q₂-IsChosen , p₂≤Tq₂) →
  case q₁ ≟ q₂ return p₁ ≡ p₂ of λ {
    (lt q₁<q₂) → ancestor-unique p₁ p₂ q₂ dp₁≡dp₂
      (≤T-trans p₁ q₁ q₂ p₁≤Tq₁ (chosen-≤T q₁ q₂ q₁<q₂ q₁-IsChosen))
      p₂≤Tq₂ ;
    (eq q₁≡q₂) → ancestor-unique p₁ p₂ q₂ dp₁≡dp₂ (subst (p₁ ≤T_) q₁≡q₂ p₁≤Tq₁) p₂≤Tq₂ ;
    (gt q₂<q₁) → ancestor-unique p₁ p₂ q₁ dp₁≡dp₂
      p₁≤Tq₁
      (≤T-trans p₂ q₂ q₁ p₂≤Tq₂ (chosen-≤T q₂ q₁ q₂<q₁ q₂-IsChosen)) } } }
    
