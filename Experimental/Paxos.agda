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

-- The proposal's parent is the maximum visible proposal.
HasParent : Proposal → Type₀
HasParent p = Σ[ i ∈ Proposal ] IsVisible i p × (∀ i' → IsVisible i' p → i' ≤ i)

HasParent-IsProp : ∀ p → IsProp (HasParent p)
HasParent-IsProp p (i₁ , i₁-IsVisible , i₁-max) (i₂ , i₂-IsVisible , i₂-max)
  = ΣProp≡ (λ i → ×-IsProp (IsVisible-IsProp i p) (Π-IsProp λ _ → Π-IsProp λ _ → ≤-IsProp))
      (≤-antisym (i₂-max i₁ i₁-IsVisible) (i₁-max i₂ i₂-IsVisible))

HasParent-Dec : ∀ p → Dec (HasParent p)
HasParent-Dec = {!!}

¬HasParent-¬IsVisible : ∀ i p → ¬ (HasParent p) → ¬ (IsVisible i p)
¬HasParent-¬IsVisible = {!!}

parent : ∀ {p} → HasParent p → Proposal
parent = fst

parent-< : ∀ {p} (h : HasParent p) → parent h < p
parent-< (i , (i<p , _) , _) = i<p

depth-step : (n : Proposal) → (∀ i → i < n → ℕ) → ℕ
depth-step n rec with HasParent-Dec n
... | yes h = suc (rec (parent h) (parent-< h))
... | no  _ = zero

depth : Proposal → ℕ
depth = <-ind depth-step

depth-zero : ∀ p → ¬ HasParent p → depth p ≡ zero
depth-zero p ¬h = <-ind-step depth-step p ∙ lemma
  where
  lemma : depth-step p (λ i _ → depth i) ≡ zero
  lemma with HasParent-Dec p
  ... | yes h = ⊥-elim (¬h h)
  ... | no  _ = refl

depth-suc : ∀ p (h : HasParent p) → depth p ≡ suc (depth (parent h))
depth-suc p h = <-ind-step depth-step p ∙ lemma
  where
  lemma : depth-step p (λ i _ → depth i) ≡ suc (depth (parent h))
  lemma with HasParent-Dec p
  ... | yes h' = ap (λ h → suc (depth (parent h))) (HasParent-IsProp p h' h)
  ... | no ¬h  = ⊥-elim (¬h h)

tree-parent : ∀ {n} → (Σ[ p ∈ Proposal ] depth p ≡ suc n) → (Σ[ p ∈ Proposal ] depth p ≡ n)
tree-parent (p , dp≡sucn) with HasParent-Dec p
... | yes h = parent h , suc-IsInjective (sym (depth-suc p h) ∙ dp≡sucn)
... | no ¬h = ⊥-elim (¬zero≡suc (sym (depth-zero p ¬h) ∙ dp≡sucn))

-- For ≤T and friends
open Tree Proposal ℕ-IsSet depth tree-parent

HasParent-≤T : ∀ p → (h : HasParent p) → parent h ≤T p
HasParent-≤T p h = subst (λ i → i ≤T p) (lemma (depth-suc p h)) (parent-≤T (p , depth-suc p h))
  where
  lemma : ∀ {n} (x : depth p ≡ suc n) → fst (tree-parent (p , x)) ≡ parent h
  lemma x with HasParent-Dec p
  ... | yes h' = ap parent (HasParent-IsProp p h' h)
  ... | no ¬h  = ⊥-elim (¬h h)

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
IsAcked-≤T : ∀ p → IsAcked p → ∀ q → p < q → p ≤T q
IsAcked-≤T p p-IsAcked = <-ind IsAcked-≤T-step
  where
  IsAcked-≤T-step : ∀ q → (∀ i → i < q → p < i → p ≤T i) → p < q → p ≤T q
  IsAcked-≤T-step q rec p<q with HasParent-Dec q
  ... | no ¬h = ⊥-elim (¬HasParent-¬IsVisible p q ¬h (IsAcked-IsVisible p q p<q p-IsAcked))
  ... | yes h@(i , i-IsVisible , i-max) with p ≟ i
  ...   | lt p<i = ≤T-trans p i q (rec i (fst i-IsVisible) p<i) (HasParent-≤T q h)
  ...   | eq p≡i = subst (λ p → p ≤T q) (sym p≡i) (HasParent-≤T q h)
  ...   | gt p>i = ⊥-elim (<-asym p>i (i-max p (IsAcked-IsVisible p q p<q p-IsAcked)))

-- We say a proposal is "committed" if it is the ancestor of an acked proposal.
IsCommitted : Proposal → Type₀
IsCommitted p = ∥ Σ[ q ∈ Proposal ] IsAcked q × p ≤T q ∥

IsCommitted-IsProp : ∀ p → IsProp (IsCommitted p)
IsCommitted-IsProp p = ∥∥-IsProp

-- TODO: what properties do we need for linearizability?

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
      (≤T-trans p₁ q₁ q₂ p₁≤Tq₁ (IsAcked-≤T q₁ q₁-IsAcked q₂ q₁<q₂))
      p₂≤Tq₂
      dp₁≡dp₂
    ; (eq q₁≡q₂) → ≤T-unique p₁ p₂ q₂ (subst (p₁ ≤T_) q₁≡q₂ p₁≤Tq₁) p₂≤Tq₂ dp₁≡dp₂
    ; (gt q₂<q₁) → ≤T-unique p₁ p₂ q₁
      p₁≤Tq₁
      (≤T-trans p₂ q₂ q₁ p₂≤Tq₂ (IsAcked-≤T q₂ q₂-IsAcked q₁ q₂<q₁))
      dp₁≡dp₂
    } } }
