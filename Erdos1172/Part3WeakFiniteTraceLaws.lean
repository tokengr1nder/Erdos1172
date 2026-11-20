/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3WeakPositiveProductExtraction

@[expose] public section

/-!
# Finite loss deletion for the weak omega-product trace

Finite joins are proved directly. Unlike countable joins, their natural
level cutoffs have a finite maximum. Positivity consequently survives
deleting finitely many small losses. No countable-union law is asserted.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3WeakFiniteTraceLaws

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3NamedCenteredLoss (MonotoneSmallness)
open Erdos1172Part3ProductTraceIdeal (CoreTrace rowCore)
open Erdos1172Part3WeakProductTrace (WeakCoreTrace productTrace)
open Erdos1172Part3FiniteTraceSchemes (scheme)
open Erdos1172Part3OmegaPowerIndex (OmegaIndex)
open Erdos1172Part3OmegaLevelTrace (levelCore omegaTrace omegaWeakTrace omegaProductTrace)

variable {P : Type} [Preorder P]

def unite (U V : RegularName P W2) : RegularName P W2 :=
  regularize (fun p x => U.holds p x ∨ V.holds p x)

theorem unite_left (U V : RegularName P W2) {p : P} {x : W2} (hx : U.holds p x) :
    (unite U V).holds p x := fun q hqp => ⟨q, le_rfl, Or.inl (U.persistent hqp hx)⟩

theorem unite_right (U V : RegularName P W2) {p : P} {x : W2} (hx : V.holds p x) :
    (unite U V).holds p x := fun q hqp => ⟨q, le_rfl, Or.inr (V.persistent hqp hx)⟩

def BinaryClosed (J : RegularName P (RegularName P W2)) : Prop :=
  ∀ p U V, J.holds p U → J.holds p V → J.holds p (unite U V)

theorem coreTrace_binary_closed {I : Type} [LinearOrder I] {G : SimpleGraph W2}
    (T : CoreTrace P I G) (hclosed : CountablyClosed P) (core : CliqueDecisions P I W2 G) :
    BinaryClosed (T.trace core) := by
  classical
  intro p U V hU hV
  let seq : ℕ → RegularName P W2 := fun n => if n = 0 then U else V
  have hseq : (T.trace core).holds p (join seq) := T.countable_join hclosed core p seq (by
    intro n
    by_cases hn : n = 0
    · simpa only [seq, if_pos hn] using hU
    · simpa only [seq, if_neg hn] using hV)
  apply T.mono core p (unite U V) (join seq) _ hseq
  intro x q hqp hx s hsq
  obtain ⟨t, hts, ht | ht⟩ := hx s hsq
  · exact ⟨t, hts, 0, by simpa only [seq, if_pos rfl] using ht⟩
  · exact ⟨t, hts, 1, by simpa only [seq, Nat.one_ne_zero, if_false] using ht⟩

theorem omegaTrace_binary_closed {G : SimpleGraph W2} (hclosed : CountablyClosed P)
    (core : CliqueDecisions P OmegaIndex W2 G) : BinaryClosed (omegaTrace core) := by
  intro p U V hU hV q hqp
  obtain ⟨s, hsq, ub, hu⟩ := hU q hqp
  obtain ⟨t, hts, vb, hv⟩ := hV s (hsq.trans hqp)
  refine ⟨t, hts.trans hsq, max ub vb, fun n hn => ?_⟩
  exact coreTrace_binary_closed ((scheme G n).forOrder P) hclosed (levelCore core n) t U V
    ((((scheme G n).forOrder P).trace (levelCore core n)).persistent hts
      (hu n ((le_max_left _ _).trans_lt hn))) (hv n ((le_max_right _ _).trans_lt hn))

theorem productTrace_binary_closed {I : Type} [LinearOrder I] {G : SimpleGraph W2}
    (T : WeakCoreTrace P I G) (hT : ∀ core, BinaryClosed (T.trace core))
    (core : CliqueDecisions P (W1 ×ₗ I) W2 G) : BinaryClosed (productTrace T core) := by
  intro p U V hU hV q hqp
  obtain ⟨s, hsq, ub, hu⟩ := hU q hqp
  obtain ⟨t, hts, vb, hv⟩ := hV s (hsq.trans hqp)
  refine ⟨t, hts.trans hsq, max ub vb, fun i hi => ?_⟩
  exact hT (rowCore core i) t U V
    ((T.trace (rowCore core i)).persistent hts (hu i ((le_max_left _ _).trans_lt hi)))
    (hv i ((le_max_right _ _).trans_lt hi))

theorem omega_product_binary_closed {G : SimpleGraph W2} (hclosed : CountablyClosed P)
    (core : CliqueDecisions P (W1 ×ₗ OmegaIndex) W2 G) :
    BinaryClosed (omegaProductTrace.trace core) :=
  productTrace_binary_closed omegaWeakTrace (omegaTrace_binary_closed hclosed) core

theorem positive_remove_small (J : RegularName P (RegularName P W2))
    (hmono : MonotoneSmallness J) (hbinary : BinaryClosed J)
    (p : P) (X V : RegularName P W2) (hX : (neg J).holds p X) (hV : J.holds p V) :
    (neg J).holds p (meet X (neg V)) := by
  intro q hqp hsmall
  apply hX q hqp
  apply hmono q X (unite (meet X (neg V)) V) _ (hbinary q _ _ hsmall (J.persistent hqp hV))
  intro x s hsq hXs t hts
  obtain ⟨v, hvt, hv | hv⟩ := exists_deciding_refinement V t x
  · exact ⟨v, hvt, Or.inr hv⟩
  · exact ⟨v, hvt, Or.inl ⟨X.persistent (hvt.trans hts) hXs, hv⟩⟩

noncomputable def finiteUnion {A : Type} (t : Finset A) (F : A → RegularName P W2) : RegularName P W2 :=
  regularize (fun p x => ∃ i ∈ t, (F i).holds p x)

theorem finiteUnion_of_holds {A : Type} (t : Finset A) (F : A → RegularName P W2)
    {i : A} (hi : i ∈ t) {p : P} {x : W2} (hx : (F i).holds p x) :
    (finiteUnion t F).holds p x := fun q hqp => ⟨q, le_rfl, i, hi, (F i).persistent hqp hx⟩

theorem finiteUnion_empty {A : Type} (F : A → RegularName P W2) :
    finiteUnion ∅ F = ground ∅ := by
  apply RegularName.ext
  intro p x
  constructor
  · intro h
    obtain ⟨q, _, i, hi, _⟩ := h p le_rfl
    exact (Finset.notMem_empty i hi).elim
  · intro h
    exact h.elim

theorem finiteUnion_insert {A : Type} [DecidableEq A] (i : A) (t : Finset A)
    (F : A → RegularName P W2) : finiteUnion (insert i t) F = unite (F i) (finiteUnion t F) := by
  apply RegularName.ext
  intro p x
  constructor
  · intro h q hqp
    obtain ⟨s, hsq, j, hj, hx⟩ := h q hqp
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ⟨s, hsq, Or.inl hx⟩
    · exact ⟨s, hsq, Or.inr (finiteUnion_of_holds t F hj hx)⟩
  · intro h q hqp
    obtain ⟨s, hsq, hx | hx⟩ := h q hqp
    · exact ⟨s, hsq, i, Finset.mem_insert_self _ _, hx⟩
    · obtain ⟨v, hvs, j, hj, hxj⟩ := hx s le_rfl
      exact ⟨v, hvs.trans hsq, j, Finset.mem_insert_of_mem hj, hxj⟩

theorem finiteUnion_small {A : Type} (J : RegularName P (RegularName P W2))
    (hempty : ∀ p, J.holds p (ground ∅)) (hbinary : BinaryClosed J)
    (t : Finset A) (F : A → RegularName P W2) (p : P) (hF : ∀ i ∈ t, J.holds p (F i)) :
    J.holds p (finiteUnion t F) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa only [finiteUnion_empty] using hempty p
  | @insert i t hi ih =>
    rw [finiteUnion_insert]
    exact hbinary p _ _ (hF i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

end Erdos1172Part3WeakFiniteTraceLaws
