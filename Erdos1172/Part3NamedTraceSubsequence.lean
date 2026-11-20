/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedTraceExtraction
public import Erdos1172.Part3RegularConeRestriction

@[expose] public section

/-!
# Trace-positive subsequences with index provenance

The original-core index of each extracted point is greater than its new
index. Consequently an old tail-avoidance bound is also a bound for the
new core. Restriction to the starting cone preserves actual membership
and stationary possibilities.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedTraceSubsequence

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularConeRestriction (onCone)
open Erdos1172Part3NamedTraceIdeal
open Erdos1172Part3NamedTraceExtraction (exists_unbounded_trace_cone)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3ConstrainedDecisionFusion (ControlledExtension exists_controlled_clique)
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)

variable {P : Type} [Preorder P] {G : SimpleGraph W2}

theorem exists_cone_subsequence (hclosed : CountablyClosed P)
    (core : CliqueDecisions P W1 W2 G) (p0 : P) (U : RegularName P W2)
    (hU : ¬(traceName core).holds p0 U) :
    ∃ q : P, q ≤ p0 ∧ ∃ out : CliqueDecisions (Set.Iic q) W1 W2 G,
      ∀ p i x, out.decides p i x → U.holds p.val x ∧
        ∃ j : W1, i < j ∧ core.decides p.val j x := by
  classical
  obtain ⟨q, hqp0, hq⟩ := exists_unbounded_trace_cone core p0 U hU
  let R (p : Set.Iic q) (x : W2) : Prop := U.holds p.val x ∧ ∃ j, core.decides p.val j x
  let K (i : W1) (p : Set.Iic q) (x : W2) : Prop :=
    ∃ j : W1, i < j ∧ core.decides p.val j x
  have hR : ∀ {p s : Set.Iic q} {x}, s ≤ p → R p x → R s x := by
    rintro p s x hsp ⟨hU, j, hj⟩
    exact ⟨U.persistent hsp hU, j, core.persistent hsp hj⟩
  have hK : ∀ {i} {p s : Set.Iic q} {x}, s ≤ p → K i p x → K i s x := by
    rintro i p s x hsp ⟨j, hij, hj⟩
    exact ⟨j, hij, core.persistent hsp hj⟩
  have hextend : ControlledExtension G R K := by
    intro i p selected hcount hselected
    let index (x : selected) : W1 := (hselected x.val x.property).2.choose
    have hindex (x : selected) : core.decides p.val (index x) x.val :=
      (hselected x.val x.property).2.choose_spec
    have hindexCount : (Set.range index).Countable :=
      Cardinal.le_aleph0_iff_set_countable.mp (Cardinal.mk_range_le.trans
        (Cardinal.le_aleph0_iff_set_countable.mpr hcount))
    obtain ⟨bound, hbound⟩ := exists_bound_of_countable
      (insert i (Set.range index)) (hindexCount.insert i)
    obtain ⟨s, hsp, j, hbj, y, hcore, hUy⟩ := hq p.val p.property bound
    refine ⟨⟨s, hsp.trans p.property⟩, hsp, y, ⟨hUy, j, hcore⟩,
      ⟨j, (hbound i (Set.mem_insert _ _)).trans hbj, hcore⟩, ?_⟩
    intro x hx
    have hij : index ⟨x, hx⟩ < j :=
      (hbound _ (Set.mem_insert_of_mem _ ⟨⟨x, hx⟩, rfl⟩)).trans hbj
    have hxc := core.persistent hsp (hindex ⟨x, hx⟩)
    exact ⟨core.ordered hij hxc hcore, core.adjacent hij.ne hxc hcore⟩
  obtain ⟨out, hout⟩ := exists_controlled_clique
    (Erdos1172Part3ClosedDenseRequirements.countablyClosed_Iic hclosed q) G R K
    (fun hsp h => hR hsp h) (fun hsp h => hK hsp h) hextend
  exact ⟨q, hqp0, out, fun p i x hx => ⟨(hout p i x hx).1.1, (hout p i x hx).2⟩⟩

theorem tailAvoid_transfer (core : CliqueDecisions P W1 W2 G) (p0 : P)
    (out : CliqueDecisions (Set.Iic p0) W1 W2 G)
    (hindex : ∀ p i x, out.decides p i x → ∃ j : W1, i < j ∧ core.decides p.val j x)
    (p : Set.Iic p0) (U : RegularName P W2) (bound : W1)
    (hbound : TailAvoid core p.val U bound) :
    TailAvoid out p (onCone p0 U) bound := by
  intro q hqp i hi x hx hUx
  obtain ⟨j, hij, hj⟩ := hindex q i x hx
  exact hbound q.val hqp j (hi.trans hij) x hj hUx

theorem traceName_transfer (core : CliqueDecisions P W1 W2 G) (p0 : P)
    (out : CliqueDecisions (Set.Iic p0) W1 W2 G)
    (hindex : ∀ p i x, out.decides p i x → ∃ j : W1, i < j ∧ core.decides p.val j x)
    (p : Set.Iic p0) (U : RegularName P W2) (hsmall : (traceName core).holds p.val U) :
    (traceName out).holds p (onCone p0 U) := by
  intro q hqp
  obtain ⟨s, hsq, bound, hs⟩ := hsmall q.val hqp
  exact ⟨⟨s, hsq.trans q.property⟩, hsq, bound,
    tailAvoid_transfer core p0 out hindex ⟨s, hsq.trans q.property⟩ U bound hs⟩

theorem named_cover_not_small (core : CliqueDecisions P W1 W2 G)
    (p0 : P) (U : RegularName P W2)
    (hcover : ∀ p : P, p ≤ p0 → ∀ i x, core.decides p i x → U.holds p x) :
    (neg (traceName core)).holds p0 U := by
  intro p hpp0 hsmall
  obtain ⟨q, hqp, bound, hbound⟩ := hsmall p le_rfl
  obtain ⟨i, hi⟩ := exists_bound_of_countable ({bound} : Set W1) (by simp)
  have hbi : bound < i := hi bound (by simp)
  obtain ⟨s, hsq, x, hx⟩ := core.dense q i
  exact hbound s hsq i hbi x hx (hcover s ((hsq.trans hqp).trans hpp0) i x hx)

/-- Trace inclusion needs to hold only at actual point decisions. -/
theorem traceName_mono_on_decisions (core : CliqueDecisions P W1 W2 G) (p : P)
    (U V : RegularName P W2)
    (hsub : ∀ q : P, q ≤ p → ∀ i x, core.decides q i x → U.holds q x → V.holds q x)
    (hV : (traceName core).holds p V) : (traceName core).holds p U := by
  intro q hqp
  obtain ⟨s, hsq, bound, hs⟩ := hV q hqp
  refine ⟨s, hsq, bound, ?_⟩
  intro t hts i hi x hx hUx
  exact hs t hts i hi x hx (hsub t ((hts.trans hsq).trans hqp) i x hx hUx)

end Erdos1172Part3NamedTraceSubsequence
