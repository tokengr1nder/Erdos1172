/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3FunctionDecisions

@[expose] public section

/-!
# Small names for functions on omegaOne

Each coordinate is represented by at most alephOne many compatible-value
decisions forming a predense family. The omegaTwo chain condition supplies
such a representation for every total persistent function-decision system.
GCH bounds the type of these names by alephTwo when the earlier order has
that size. No extra global domination principle is assumed.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3NiceFunctionNames

open ErdosRadoCHAsym (W1)
open Erdos1172Part3ClosedDecisionSystem (DenseBelow)
open Erdos1172Part3StationaryDecisions
open Erdos1172Part3FunctionDecisions

structure NiceFunctionName (P I V : Type) [Preorder P] where
  graph : I → Set (P × V)
  small : ∀ i, #(graph i) ≤ ℵ_ 1
  consistent : ∀ i p v q w, (p, v) ∈ graph i → (q, w) ∈ graph i →
    Compatible p q → v = w
  predense : ∀ p i, ∃ q v, (q, v) ∈ graph i ∧ Compatible p q

variable {P I V : Type} [Preorder P]

def NiceFunctionName.toDecisions (N : NiceFunctionName P I V) : FunctionDecisions P I V where
  decides p i v := ∃ q : P, (q, v) ∈ N.graph i ∧ p ≤ q
  dense := by
    intro p i
    obtain ⟨q, v, hq, r, hrp, hrq⟩ := N.predense p i
    exact ⟨r, hrp, v, q, hq, hrq⟩
  persistent := by
    rintro p q i v hqp ⟨r, hr, hpr⟩
    exact ⟨r, hr, hqp.trans hpr⟩
  unique := by
    rintro p i v w ⟨q, hq, hpq⟩ ⟨r, hr, hpr⟩
    exact N.consistent i q v r w hq hr ⟨p, hpq, hpr⟩

/-- Choose one small predense antichain for each coordinate. All
decisions made by the resulting name are decisions of the original
function system, so normalization does not invent any value. -/
theorem exists_nice_name (hcc : OmegaTwoCC P) (F : FunctionDecisions P I V) :
    ∃ N : NiceFunctionName P I V,
      ∀ p i v, N.toDecisions.decides p i v → F.decides p i v := by
  classical
  let D (i : I) : Set P := {p | ∃ v, F.decides p i v}
  have hD : ∀ i, DenseBelow (D i) := by
    intro i p
    obtain ⟨q, hqp, v, hv⟩ := F.dense p i
    exact ⟨q, ⟨v, hv⟩, hqp⟩
  choose A hAD hAA hAP using fun i => exists_predense_antichain (D i) (hD i)
  let graph (i : I) : Set (P × V) := {pv | pv.1 ∈ A i ∧ F.decides pv.1 i pv.2}
  have hsmall : ∀ i, #(graph i) ≤ ℵ_ 1 := by
    intro i
    let code (pv : graph i) : A i := ⟨pv.val.1, pv.property.1⟩
    have hinj : Injective code := by
      intro pv qw h
      have heq : pv.val.1 = qw.val.1 := congrArg Subtype.val h
      apply Subtype.ext
      refine Prod.ext heq ?_
      have hv := pv.property.2
      have hw := qw.property.2
      rw [heq] at hv
      exact F.unique hv hw
    apply (Cardinal.mk_le_of_injective hinj).trans
    have h := hcc (A i) (hAA i)
    have hsucc : (ℵ_ 2 : Cardinal.{0}) = Order.succ (ℵ_ 1) := by
      rw [Cardinal.succ_aleph, show (1 : Ordinal.{0}) + 1 = 2 by norm_num]
    rwa [hsucc, Order.lt_succ_iff] at h
  let N : NiceFunctionName P I V :=
    { graph := graph
      small := hsmall
      consistent := by
        intro i p v q w hp hq hcompat
        have heq : p = q := by
          by_contra hne
          exact hAA i p hp.1 q hq.1 hne hcompat
        exact F.unique (heq ▸ hp.2) hq.2
      predense := by
        intro p i
        obtain ⟨q, hq, hcompat⟩ := hAP i p
        obtain ⟨v, hv⟩ := hAD i hq
        exact ⟨q, v, ⟨hq, hv⟩, hcompat⟩ }
  refine ⟨N, ?_⟩
  rintro p i v ⟨q, hq, hpq⟩
  exact F.persistent hpq hq.2

/-- Dense refinement preserves every forced strict bound. Thus a later
stage dominating a nice representative also dominates the original
earlier-stage function decisions. -/
theorem boundedAt_iff_of_refines {F K : FunctionDecisions P W1 W1}
    (href : ∀ p i v, K.decides p i v → F.decides p i v) (p : P) (i bound : W1) :
    BoundedAt K p i bound ↔ BoundedAt F p i bound := by
  constructor
  · intro h q hqp v hv
    obtain ⟨r, hrq, w, hw⟩ := K.dense q i
    have heq : v = w := F.unique (F.persistent hrq hv) (href r i w hw)
    exact heq.trans_lt (h r (hrq.trans hqp) w hw)
  · intro h q hqp v hv
    exact h q hqp v (href q i v hv)

theorem NiceFunctionName.ext {N M : NiceFunctionName P I V} (h : N.graph = M.graph) :
    N = M := by
  cases N
  cases M
  cases h
  rfl

/-- This cardinality bound is on the explicitly constructed small name
type, not on the much larger type of arbitrary decision predicates. -/
theorem mk_nice_function_name_le (hGCH : GCH) (hP : #P ≤ ℵ_ 2) :
    #(NiceFunctionName P W1 W1) ≤ ℵ_ 2 := by
  let Code := {s : Set (P × W1) // #s ≤ ℵ_ 1}
  have hprod : #(P × W1) ≤ ℵ_ 2 := by
    rw [Cardinal.mk_prod]
    simp only [Cardinal.lift_id, W1, Cardinal.mk_toType, Ordinal.card_omega]
    exact (mul_le_mul' hP (Cardinal.aleph_le_aleph.mpr
      (by norm_num : (1 : Ordinal.{0}) ≤ 2))).trans_eq
        (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 2))
  have hcode : #Code ≤ ℵ_ 2 := by
    apply (Cardinal.mk_bounded_set_le (P × W1) (ℵ_ 1)).trans
    exact (Cardinal.power_le_power_right (max_le hprod (Cardinal.aleph0_le_aleph 2))).trans_eq
        hGCH.aleph_two_power_aleph_one
  let encode (N : NiceFunctionName P W1 W1) : W1 → Code :=
    fun i => ⟨N.graph i, N.small i⟩
  have hinj : Injective encode := by
    intro N M h
    apply NiceFunctionName.ext
    funext i
    exact congrArg (fun code : W1 → Code => (code i).val) h
  apply (Cardinal.mk_le_of_injective hinj).trans
  rw [Cardinal.mk_arrow]
  simp only [Cardinal.lift_id, W1, Cardinal.mk_toType, Ordinal.card_omega]
  exact (Cardinal.power_le_power_right hcode).trans_eq hGCH.aleph_two_power_aleph_one

end Erdos1172Part3NiceFunctionNames
