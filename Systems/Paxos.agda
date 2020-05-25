{-# OPTIONS --cubical #-}
module Systems.Paxos where

open import Math.Dec
open import Math.Finite
open import Math.Nat
open import Math.Type
open import Systems.Forest
open import Systems.Log

private
  variable
    ℓ ℓ' : Level

-- For simplicity, we'll let the set of proposals be the naturals as in most presentations.
Proposal : Type₀
Proposal = ℕ

Proposal-IsSet : IsSet Proposal
Proposal-IsSet = ℕ-IsSet

-- First, we posulate some basic facts which will be provided by the implementation.
postulate
  -- Paxos requires a set of acceptors with stable storage.
  Acceptor : Type₀

  -- Quorums, which are special finite subsets of the acceptors.
  -- Each quorum consists of a finite set of members, each of which corresponds to an acceptor.
  Quorum : Type₀
  Member : Quorum → Type₀
  Member-IsFinite : ∀ {q} → IsFinite (Member q)
  acceptor : ∀ {q} → Member q → Acceptor

  -- The critical property of quorums: any two quorums have a member in common.
  quorumOverlap : (q₁ q₂ : Quorum) → ∥ Σ[ m₁ ∈ Member q₁ ] Σ[ m₂ ∈ Member q₂ ] acceptor m₁ ≡ acceptor m₂ ∥

  -- Acceptors may accept proposals. This is independent of time, so this means
  -- "was or will ever be accepted" rather than "is known to be accepted as of now".
  IsAccepted : Acceptor → Proposal → Type₀
  IsAccepted-IsProp : ∀ a p → IsProp (IsAccepted a p)

  -- Every proposal p must have some quorum of acceptors that responded in the prepare phase with a "promise".
  -- The promise means that each acceptor will no longer accept proposals less than p, which means it is now
  -- decided whether each acceptor in the quorum has accepted proposals less than p.
  prepareQuorum : Proposal → Quorum
  preparePromise : ∀ i p → i < p → (m : Member (prepareQuorum p)) → Dec (IsAccepted (acceptor m) i)

-- Next, we define a forest of proposals, where each proposal is either a root or attached
-- to some other proposal (its "parent"). A proposal's p parent will be the maximum proposal that is accepted
-- by any member the prepare quorum for p, if it exists. If no member in the prepare quorum accepted any proposal,
-- then p is a root.

-- We say a proposal "is visible" to another proposal if at least one acceptor
-- in the later proposal's prepare quorum has accepted it.
IsVisible : Proposal → Proposal → Type₀
IsVisible i p = (i < p) × ∥ Σ[ m ∈ Member (prepareQuorum p) ] IsAccepted (acceptor m) i ∥

IsVisible-IsProp : ∀ p q → IsProp (IsVisible p q)
IsVisible-IsProp p q = ×-IsProp <-IsProp ∥∥-IsProp

-- Visibility is decidable thanks to the promise property.
IsVisible-Dec : ∀ p q → Dec (IsVisible p q)
IsVisible-Dec p q = case (<-Dec p q) return Dec (IsVisible p q) of λ
  { (yes p<q) → case IsFinite-∃-Dec Member-IsFinite (preparePromise p q p<q) return Dec (IsVisible p q) of λ
    { (yes m) → yes (p<q , m)
    ; (no ¬m) → no λ { (_ , m) → ¬m m }
    }
  ; (no ¬p<q) → no λ { (p<q , _) → ¬p<q p<q }
  }

-- A proposal has a parent if there exists a maximum visible proposal.
HasParent : Proposal → Type₀
HasParent p = Σ[ i ∈ Proposal ] IsVisible i p × (∀ i' → IsVisible i' p → i' ≤ i)

-- There is at most one possible parent.
HasParent-IsProp : ∀ p → IsProp (HasParent p)
HasParent-IsProp p (i₁ , i₁-IsVisible , i₁-max) (i₂ , i₂-IsVisible , i₂-max)
  = ΣProp≡ (λ i → ×-IsProp (IsVisible-IsProp i p) (Π-IsProp λ _ → Π-IsProp λ _ → ≤-IsProp))
      (≤-antisym (i₂-max i₁ i₁-IsVisible) (i₁-max i₂ i₂-IsVisible))

-- The parent, if a proposal has one.
parent : ∀ {p} → HasParent p → Proposal
parent = fst

parent-< : ∀ {p} (h : HasParent p) → parent h < p
parent-< (i , (i<p , _) , _) = i<p

-- (A lemma to help with the proofs below).
HasParent-or-¬IsVisible : ∀ p → HasParent p ⊎ (∀ i → ¬ IsVisible i p)
HasParent-or-¬IsVisible p = case lemma p return HasParent p ⊎ (∀ i → ¬ IsVisible i p) of λ
  { (inl (i , (i<n , i-IsVisible) , i-max)) → inl (i , i-IsVisible , λ i' i'-IsVisible → i-max i' (fst i'-IsVisible , i'-IsVisible))
  ; (inr ¬-IsVisible<) → inr λ i i-IsVisible → ¬-IsVisible< i (fst i-IsVisible , i-IsVisible)
  }
  where
  IsVisible< : ℕ → ℕ → Type₀
  IsVisible< i n = (i < n) × IsVisible i p

  P : ℕ → Type₀
  P n = (Σ[ i ∈ Proposal ] IsVisible< i n × (∀ i' → IsVisible< i' n → i' ≤ i)) ⊎ (∀ i → ¬ IsVisible< i n)

  lemma : ∀ n → P n
  lemma zero      = inr λ i i-IsVisible< → ¬-<-zero (fst i-IsVisible<)
  lemma n@(suc j) = case IsVisible-Dec j p return P n of λ
    { (yes j-IsVisible) → inl (j , (≤-refl , j-IsVisible) , λ { i (i<sucj , i-IsVisible) → suc-reflects-≤ i<sucj })
    ; (no ¬j-IsVisible) → case lemma j return P n of λ
      { (inl (i , (i<j , i-IsVisible) , i-max)) → inl (i , (≤-suc i<j , i-IsVisible) , λ {
        i' (i'<sucj , i'-IsVisible) → case <-split i'<sucj of λ
          { (inl i'<j) → i-max i' (i'<j , i'-IsVisible)
          ; (inr i'≡j) → ⊥-elim (¬j-IsVisible (subst (λ i → IsVisible i p) i'≡j i'-IsVisible))
          }
        })
      ; (inr ¬IsVisible<) → inr λ {
        i (i<sucj , i-IsVisible) → case <-split i<sucj of λ
          { (inl i<j) → ¬IsVisible< i (i<j , i-IsVisible)
          ; (inr i≡j) → ¬j-IsVisible (subst (λ i → IsVisible i p) i≡j i-IsVisible)
          }
        }
      }
    }

-- It is decidable whether a proposal has a parent. This is necessary to define the forest
-- of proposals, because otherwise we couldn't trace the path from a proposal to a root.
HasParent-Dec : ∀ p → Dec (HasParent p)
HasParent-Dec p = case HasParent-or-¬IsVisible p return Dec (HasParent p) of λ
  { (inl h) → yes h
  ; (inr ¬IsVisible) → no λ { (i , i-IsVisible , _) → ¬IsVisible i i-IsVisible }
  }

-- If any proposal is visible to p, then p has a parent.
IsVisible→HasParent : ∀ {i p} → IsVisible i p → HasParent p
IsVisible→HasParent {i} {p} i-IsVisible = case HasParent-or-¬IsVisible p return HasParent p of λ
  { (inl h) → h
  ; (inr ¬IsVisible) → ⊥-elim (¬IsVisible i i-IsVisible)
  }

-- (A helper function to make proofs about the depth function easier.)
depth-step : (n : Proposal) → (∀ i → i < n → ℕ) → ℕ
depth-step n rec with HasParent-Dec n
... | yes h = suc (rec (parent h) (parent-< h))
... | no  _ = zero

-- The depth of a proposal as a node in the proposal forest.
depth : Proposal → ℕ
depth = <-ind depth-step

-- Roots have depth zero.
depth-zero : ∀ p → ¬ HasParent p → depth p ≡ zero
depth-zero p ¬h = <-ind-step depth-step p ∙ lemma
  where
  lemma : depth-step p (λ i _ → depth i) ≡ zero
  lemma with HasParent-Dec p
  ... | yes h = ⊥-elim (¬h h)
  ... | no  _ = refl

-- The depth of a non-root proposal is one more than the depth of its parent.
depth-suc : ∀ p (h : HasParent p) → depth p ≡ suc (depth (parent h))
depth-suc p h = <-ind-step depth-step p ∙ lemma
  where
  lemma : depth-step p (λ i _ → depth i) ≡ suc (depth (parent h))
  lemma with HasParent-Dec p
  ... | yes h' = ap (λ h → suc (depth (parent h))) (HasParent-IsProp p h' h)
  ... | no ¬h  = ⊥-elim (¬h h)

-- The "parent" function of the forest, which takes a node at depth n + 1 to its parent node at depth n.
tree-parent : ∀ {n} → (Σ[ p ∈ Proposal ] depth p ≡ suc n) → (Σ[ p ∈ Proposal ] depth p ≡ n)
tree-parent (p , dp≡sucn) with HasParent-Dec p
... | yes h = parent h , suc-IsInjective (sym (depth-suc p h) ∙ dp≡sucn)
... | no ¬h = ⊥-elim (¬zero≡suc (sym (depth-zero p ¬h) ∙ dp≡sucn))

-- This completes the description of the forest of proposals. The "Tree" module contains some
-- generic definitions about forest that we now bring into scope. Particularly important is
-- the "ancestor" relation: for two proposals p and q, p ≤T q means that p is an ancestor of q
-- in the forest.
open Forest Proposal Proposal-IsSet depth tree-parent

-- Now, we'll pick out a single "branch" of the proposal forest, which will be our consensus log.
-- We'll define what it means for a proposal to be "committed", and show that committed proposals
-- form a log.

-- First, we say a proposal is "acked" if it is accepted by some quorum of acceptors.
-- In "Paxos Made Simple", this property is called "chosen" rather than "acked".
IsAcked : Proposal → Type₀
IsAcked p = ∥ Σ[ q ∈ Quorum ] ((m : Member q) → IsAccepted (acceptor m) p) ∥

IsAcked-IsProp : ∀ p → IsProp (IsAcked p)
IsAcked-IsProp p = ∥∥-IsProp

-- Acked proposals are always visible to later proposals, because the quorum that acked this
-- proposal overlaps the prepare quorum for the later proposal.
IsAcked→IsVisible : ∀ {p q} → p < q → IsAcked p → IsVisible p q
IsAcked→IsVisible {p} {q} p<q =
   ∥∥-rec (IsVisible-IsProp p q) λ { (Qp , Qp-IsAccepted) →
   with-∥∥ (quorumOverlap Qp (prepareQuorum q)) (IsVisible-IsProp p q) λ { (m₁ , m₂ , am₁≡am₂) →
   p<q , ∣ m₂ , subst (λ a → IsAccepted a p) am₁≡am₂ (Qp-IsAccepted m₁) ∣ } }

-- (Another lemma.)
HasParent-≤T : ∀ p → (h : HasParent p) → parent h ≤T p
HasParent-≤T p h = subst (λ i → i ≤T p) (lemma (depth-suc p h)) parent-≤T
  where
  lemma : ∀ {n} (x : depth p ≡ suc n) → fst (tree-parent (p , x)) ≡ parent h
  lemma x with HasParent-Dec p
  ... | yes h' = ap parent (HasParent-IsProp p h' h)
  ... | no ¬h  = ⊥-elim (¬h h)

-- Acked proposals are always ancestors to later proposals.
IsAcked-≤T : ∀ p → IsAcked p → ∀ q → p < q → p ≤T q
IsAcked-≤T p p-IsAcked = <-ind IsAcked-≤T-step
  where
  IsAcked-≤T-step : ∀ q → (∀ i → i < q → p < i → p ≤T i) → p < q → p ≤T q
  IsAcked-≤T-step q rec p<q with HasParent-Dec q
  ... | no ¬h = ⊥-elim (¬h (IsVisible→HasParent (IsAcked→IsVisible p<q p-IsAcked)))
  ... | yes h@(i , i-IsVisible , i-max) with p ≟ i
  ...   | lt p<i = ≤T-trans (rec i (fst i-IsVisible) p<i) (HasParent-≤T q h)
  ...   | eq p≡i = subst (λ p → p ≤T q) (sym p≡i) (HasParent-≤T q h)
  ...   | gt p>i = ⊥-elim (<-asym p>i (i-max p (IsAcked→IsVisible p<q p-IsAcked)))

-- We say a proposal is "committed" if it is the ancestor of some acked proposal.
IsCommitted : Proposal → Type₀
IsCommitted p = ∥ Σ[ q ∈ Proposal ] IsAcked q × p ≤T q ∥

IsCommitted-IsProp : ∀ {p} → IsProp (IsCommitted p)
IsCommitted-IsProp = ∥∥-IsProp

-- Acked proposals are committed.
IsAcked→IsCommitted : ∀ {p} → IsAcked p → IsCommitted p
IsAcked→IsCommitted {p} p-IsAcked = ∣ p , p-IsAcked , ≤T-refl ∣

-- The ancestor of committed proposal is committed.
ancestor-IsCommitted : ∀ p₁ p₂ → p₁ ≤T p₂ → IsCommitted p₂ → IsCommitted p₁
ancestor-IsCommitted p₁ p₂ p₁≤Tp₂ =
  ∥∥-rec IsCommitted-IsProp λ { (q , q-IsAcked , p₂≤Tq) →
    ∣ q , q-IsAcked , ≤T-trans p₁≤Tp₂ p₂≤Tq ∣ }

-- The crucial property: there is at most one committed proposal at each depth.
-- Together with the above property, this implies that committed proposals lie
-- on a single branch of the proposal forest.
committed-unique : ∀ p₁ p₂ → depth p₁ ≡ depth p₂
  → IsCommitted p₁ → IsCommitted p₂ → p₁ ≡ p₂
committed-unique p₁ p₂ dp₁≡dp₂ =
  ∥∥-rec (Π-IsProp λ _ → Proposal-IsSet p₁ p₂) λ { (q₁ , q₁-IsAcked , p₁≤Tq₁) →
  ∥∥-rec (Proposal-IsSet p₁ p₂) λ { (q₂ , q₂-IsAcked , p₂≤Tq₂) →
  case q₁ ≟ q₂ return p₁ ≡ p₂ of λ
    { (lt q₁<q₂) → ≤T-unique p₁ p₂ q₂
      (≤T-trans p₁≤Tq₁ (IsAcked-≤T q₁ q₁-IsAcked q₂ q₁<q₂))
      p₂≤Tq₂
      dp₁≡dp₂
    ; (eq q₁≡q₂) → ≤T-unique p₁ p₂ q₂ (subst (p₁ ≤T_) q₁≡q₂ p₁≤Tq₁) p₂≤Tq₂ dp₁≡dp₂
    ; (gt q₂<q₁) → ≤T-unique p₁ p₂ q₁
      p₁≤Tq₁
      (≤T-trans p₂≤Tq₂ (IsAcked-≤T q₂ q₂-IsAcked q₁ q₂<q₁))
      dp₁≡dp₂
    } } }

-- Finally, we can define our log of committed proposals by combining all of the above.
CommittedProposal : Type₀
CommittedProposal = Σ[ p ∈ Proposal ] IsCommitted p

CommittedProposal-IsSet : IsSet CommittedProposal
CommittedProposal-IsSet = Σ-IsSet Proposal-IsSet (λ _ → IsProp→IsSet IsCommitted-IsProp)

committedDepth : CommittedProposal → ℕ
committedDepth (p , _) = depth p

committedDepth-IsInjective : ∀ {p₁ p₂ : CommittedProposal} → committedDepth p₁ ≡ committedDepth p₂ → p₁ ≡ p₂
committedDepth-IsInjective {p₁ , p₁-IsCommitted} {p₂ , p₂-IsCommitted} dp₁≡dp₂ =
  ΣProp≡ (λ _ → IsCommitted-IsProp) (committed-unique p₁ p₂ dp₁≡dp₂ p₁-IsCommitted p₂-IsCommitted)

committedParent : ∀ {n} → (Σ[ p ∈ CommittedProposal ] committedDepth p ≡ suc n) → (Σ[ p ∈ CommittedProposal ] committedDepth p ≡ n)
committedParent {n} ((p , p-IsCommitted) , dp≡sucn) =
    (p' , ancestor-IsCommitted p' p parent-≤T p-IsCommitted) , dp'≡n
  where
  p' : Proposal
  p' = fst (tree-parent (p , dp≡sucn))

  dp'≡n : depth p' ≡ n
  dp'≡n = snd (tree-parent (p , dp≡sucn))

open Log CommittedProposal CommittedProposal-IsSet committedDepth committedDepth-IsInjective committedParent
