{-# OPTIONS --cubical #-}
-- Overview: we posulate acceptors and the prepare phase, which come from the implementation.
-- From this, we can define what a "committed" proposal is, and show that committed proposals are serializable.
module Experimental.Paxos where

open import Experimental.Log
open import Experimental.Tree
open import Math.Dec
open import Math.Finite
open import Math.Nat
open import Math.Type

private
  variable
    ℓ ℓ' : Level

-- Paxos proposals must have a unique id. For simplicity, we'll let them be the
-- naturals as in most presentations.
Proposal : Type₀
Proposal = ℕ

postulate
  -- Paxos requires a set of acceptors with stable storage.
  Acceptor : Type₀

  -- Quorums, which are finite subsets of the acceptors.
  Quorum : Type₀
  Member : Quorum → Type₀
  Member-IsFinite : ∀ {q} → IsFinite (Member q)
  acceptor : ∀ {q} → Member q → Acceptor

  -- Any two quorums overlap.
  quorumOverlap : (q₁ q₂ : Quorum) → ∥ Σ[ m₁ ∈ Member q₁ ] Σ[ m₂ ∈ Member q₂ ] acceptor m₁ ≡ acceptor m₂ ∥

  -- Acceptors may accept proposals. This is independent of time, so it means
  -- "was or will be accepted" rather than "is known to be accepted as of now".
  IsAccepted : Acceptor → Proposal → Type₀
  IsAccepted-IsProp : ∀ a p → IsProp (IsAccepted a p)

  -- Every proposal must have some quorum of acceptors that responded in the prepare phase with a promise
  prepareQuorum : Proposal → Quorum

  -- A promise not to accept a proposal in the future means its acceptance is now
  -- decidable.
  preparePromise : ∀ p q → p < q → (m : Member (prepareQuorum q)) → Dec (IsAccepted (acceptor m) p)

-- A proposal is visible to another proposal if at least one acceptor
-- in the later proposal's prepare quorum has accepted it.
IsVisible : Proposal → Proposal → Type₀
IsVisible p q = (p < q) × ∥ Σ[ m ∈ Member (prepareQuorum q) ] IsAccepted (acceptor m) p ∥

IsVisible-IsProp : ∀ p q → IsProp (IsVisible p q)
IsVisible-IsProp p q = ×-IsProp <-IsProp ∥∥-IsProp

IsVisible-Dec : ∀ p q → Dec (IsVisible p q)
IsVisible-Dec p q = case (<-Dec p q) return Dec (IsVisible p q) of λ
  { (yes p<q) → case IsFinite-∃-Dec Member-IsFinite (preparePromise p q p<q) return Dec (IsVisible p q) of λ
    { (yes m) → yes (p<q , m)
    ; (no ¬m) → no λ { (_ , m) → ¬m m }
    }
  ; (no ¬p<q) → no λ { (p<q , _) → ¬p<q p<q }
  }

-- The proposal's parent is the maximum visible proposal.
HasParent : Proposal → Type₀
HasParent p = Σ[ i ∈ Proposal ] IsVisible i p × (∀ i' → IsVisible i' p → i' ≤ i)

-- There is at most one possible parent.
HasParent-IsProp : ∀ p → IsProp (HasParent p)
HasParent-IsProp p (i₁ , i₁-IsVisible , i₁-max) (i₂ , i₂-IsVisible , i₂-max)
  = ΣProp≡ (λ i → ×-IsProp (IsVisible-IsProp i p) (Π-IsProp λ _ → Π-IsProp λ _ → ≤-IsProp))
      (≤-antisym (i₂-max i₁ i₁-IsVisible) (i₁-max i₂ i₂-IsVisible))

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
  lemma n@(suc k) = case IsVisible-Dec k p return P n of λ
    { (yes k-IsVisible) → inl (k , (≤-refl , k-IsVisible) , λ { i (i<suck , i-IsVisible) → suc-reflects-≤ i<suck })
    ; (no ¬k-IsVisible) → case lemma k return P n of λ
      { (inl (i , (i<k , i-IsVisible) , i-max)) → inl (i , (≤-suc i<k , i-IsVisible) , λ {
        i' (i'<suck , i'-IsVisible) → case <-split i'<suck of λ
          { (inl i'<k) → i-max i' (i'<k , i'-IsVisible)
          ; (inr i'≡k) → ⊥-elim (¬k-IsVisible (subst (λ i → IsVisible i p) i'≡k i'-IsVisible))
          }
        })
      ; (inr ¬-IsVisible<) → inr λ {
        i (i<suck , i-IsVisible) → case <-split i<suck of λ
          { (inl i<k) → ¬-IsVisible< i (i<k , i-IsVisible)
          ; (inr i≡k) → ¬k-IsVisible (subst (λ i → IsVisible i p) i≡k i-IsVisible)
          }
        }
      }
    }

HasParent-Dec : ∀ p → Dec (HasParent p)
HasParent-Dec p = case HasParent-or-¬IsVisible p return Dec (HasParent p) of λ
  { (inl h) → yes h
  ; (inr ¬IsVisible) → no λ { (i , i-isVisible , _) → ¬IsVisible i i-isVisible }
  }

IsVisible→HasParent : ∀ {i p} → IsVisible i p → HasParent p
IsVisible→HasParent {i} {p} i-IsVisible = case HasParent-or-¬IsVisible p return HasParent p of λ
  { (inl h) → h
  ; (inr ¬IsVisible) → ⊥-elim (¬IsVisible i i-IsVisible)
  }

parent : ∀ {p} → HasParent p → Proposal
parent = fst

parent-< : ∀ {p} (h : HasParent p) → parent h < p
parent-< (i , (i<p , _) , _) = i<p

-- TODO: are all these withs to get this to compute necessary?
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
HasParent-≤T p h = subst (λ i → i ≤T p) (lemma (depth-suc p h)) parent-≤T
  where
  lemma : ∀ {n} (x : depth p ≡ suc n) → fst (tree-parent (p , x)) ≡ parent h
  lemma x with HasParent-Dec p
  ... | yes h' = ap parent (HasParent-IsProp p h' h)
  ... | no ¬h  = ⊥-elim (¬h h)

-- We say a proposal is "acked" if it is accepted by a quorum of acceptors. This
-- is independent of time, so it means "was or will be acked" rather than
-- "is known to be acked as of now".
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

-- Thus, acked proposals are always ancestors to later proposals.
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

-- We say a proposal is "committed" if it is the ancestor of an acked proposal.
IsCommitted : Proposal → Type₀
IsCommitted p = ∥ Σ[ q ∈ Proposal ] IsAcked q × p ≤T q ∥

IsCommitted-IsProp : ∀ {p} → IsProp (IsCommitted p)
IsCommitted-IsProp = ∥∥-IsProp

IsAcked→IsCommitted : ∀ {p} → IsAcked p → IsCommitted p
IsAcked→IsCommitted {p} p-IsAcked = ∣ p , p-IsAcked , ≤T-refl ∣

-- The ancestor of committed proposal is committed
ancestor-IsCommitted : ∀ p₁ p₂ → p₁ ≤T p₂ → IsCommitted p₂ → IsCommitted p₁
ancestor-IsCommitted p₁ p₂ p₁≤Tp₂ =
  ∥∥-rec IsCommitted-IsProp λ { (q , q-IsAcked , p₂≤Tq) →
    ∣ q , q-IsAcked , ≤T-trans p₁≤Tp₂ p₂≤Tq ∣ }

-- There is at most one committed proposal at each depth
committed-unique : ∀ p₁ p₂ → depth p₁ ≡ depth p₂
  → IsCommitted p₁ → IsCommitted p₂ → p₁ ≡ p₂
committed-unique p₁ p₂ dp₁≡dp₂ =
  ∥∥-rec (Π-IsProp λ _ → ℕ-IsSet p₁ p₂) λ { (q₁ , q₁-IsAcked , p₁≤Tq₁) →
  ∥∥-rec (ℕ-IsSet p₁ p₂) λ { (q₂ , q₂-IsAcked , p₂≤Tq₂) →
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

CommittedProposal : Type₀
CommittedProposal = Σ[ p ∈ Proposal ] IsCommitted p

CommittedProposal-IsSet : IsSet CommittedProposal
CommittedProposal-IsSet = Σ-IsSet ℕ-IsSet (λ _ → IsProp→IsSet IsCommitted-IsProp)

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
