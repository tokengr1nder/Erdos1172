/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedTraceIdeal

@[expose] public section

/-!
# Clique extraction from positive traces

Failure of dense boundedness gives a cone with unbounded possible indices
below every strengthening. Countable extension then constructs a clique
whose points satisfy the named trace at the deciding condition. Ground
extraction retains an original-core decision for every selected vertex.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedTraceExtraction

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3NamedTraceIdeal
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3CountableDecisionFusion (CountableExtension)
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)

variable {P : Type} [Preorder P] {G : SimpleGraph W2}

theorem exists_unbounded_trace_cone (core : CliqueDecisions P W1 W2 G)
    (p0 : P) (U : RegularName P W2) (hU : ¬(traceName core).holds p0 U) :
    ∃ q : P, q ≤ p0 ∧ ∀ p : P, p ≤ q → ∀ bound : W1,
      ∃ s : P, s ≤ p ∧ ∃ i : W1, bound < i ∧
        ∃ x : W2, core.decides s i x ∧ U.holds s x := by
  classical
  change ¬∀ q : P, q ≤ p0 → ∃ s : P, s ≤ q ∧ ∃ bound, TailAvoid core s U bound at hU
  push Not at hU
  obtain ⟨q, hqp0, hq⟩ := hU
  refine ⟨q, hqp0, ?_⟩
  intro p hpq bound
  have h := hq p hpq bound
  unfold TailAvoid at h
  push Not at h
  exact h

theorem exists_cone_clique_in_positive_trace (hclosed : CountablyClosed P)
    (core : CliqueDecisions P W1 W2 G) (p0 : P) (U : RegularName P W2)
    (hU : ¬(traceName core).holds p0 U) :
    ∃ q : P, q ≤ p0 ∧ ∃ out : CliqueDecisions (Set.Iic q) W1 W2 G,
      ∀ p i x, out.decides p i x → U.holds p.val x ∧ ∃ j : W1, core.decides p.val j x := by
  classical
  obtain ⟨q, hqp0, hq⟩ := exists_unbounded_trace_cone core p0 U hU
  let R (p : Set.Iic q) (x : W2) : Prop := U.holds p.val x ∧ ∃ j, core.decides p.val j x
  have hR : ∀ {p s : Set.Iic q} {x}, s ≤ p → R p x → R s x := by
    rintro p s x hsp ⟨hU, j, hj⟩
    exact ⟨U.persistent hsp hU, j, core.persistent hsp hj⟩
  have hextend : CountableExtension G R := by
    intro p selected hcount hselected
    let index (x : selected) : W1 := (hselected x.val x.property).2.choose
    have hindex (x : selected) : core.decides p.val (index x) x.val :=
      (hselected x.val x.property).2.choose_spec
    have hindexCount : (Set.range index).Countable :=
      Cardinal.le_aleph0_iff_set_countable.mp (Cardinal.mk_range_le.trans
        (Cardinal.le_aleph0_iff_set_countable.mpr hcount))
    obtain ⟨bound, hbound⟩ := exists_bound_of_countable (Set.range index) hindexCount
    obtain ⟨s, hsp, j, hbj, y, hcore, hUy⟩ := hq p.val p.property bound
    refine ⟨⟨s, hsp.trans p.property⟩, hsp, y, ⟨hUy, j, hcore⟩, ?_⟩
    intro x hx
    have hij : index ⟨x, hx⟩ < j := (hbound _ ⟨⟨x, hx⟩, rfl⟩).trans hbj
    have hxc := core.persistent hsp (hindex ⟨x, hx⟩)
    exact ⟨core.ordered hij hxc hcore, core.adjacent hij.ne hxc hcore⟩
  obtain ⟨out, hout⟩ :=
    Erdos1172Part3CountableDecisionFusion.exists_clique_decisions_of_countable_extension
      (Erdos1172Part3ClosedDenseRequirements.countablyClosed_Iic hclosed q) G R
      (fun hsp h => hR hsp h) hextend
  exact ⟨q, hqp0, out, hout⟩

/-- This is an actual ground clique of exact type omegaOne. Source
membership has a condition witness for each point, not one common
condition for the completed uncountable clique. -/
theorem exists_ground_clique_in_positive_trace (hclosed : CountablyClosed P)
    (core : CliqueDecisions P W1 W2 G) (p0 : P) (U : RegularName P W2)
    (hU : ¬(traceName core).holds p0 U) :
    ∃ s : Set W2, G.IsClique s ∧ typeLT s = ω_ 1 ∧
      ∀ x ∈ s, ∃ q : P, q ≤ p0 ∧ U.holds q x ∧ ∃ j : W1, core.decides q j x := by
  obtain ⟨q, hqp0, out, hout⟩ := exists_cone_clique_in_positive_trace hclosed core p0 U hU
  obtain ⟨f, hf, hclique, horigin⟩ :=
    Erdos1172Part3CliqueConeExtension.exists_clique_map_with_origins out
      (Erdos1172Part3ClosedDenseRequirements.countablyClosed_Iic hclosed q)
      ⟨q, le_rfl⟩ (by simp only [W1, Cardinal.mk_toType, Ordinal.card_omega, le_refl])
  refine ⟨Set.range f, hclique, ?_, ?_⟩
  · simpa only [W1, Ordinal.type_toType] using Ordinal.typeLT_range_of_strictMono f hf
  · rintro x ⟨i, rfl⟩
    obtain ⟨p, _, hp⟩ := horigin i
    exact ⟨p.val, p.property.trans hqp0, hout p i (f i) hp⟩

theorem exists_ground_clique_in_positive_set (hclosed : CountablyClosed P)
    (core : CliqueDecisions P W1 W2 G) (p0 : P) (X : Set W2)
    (hX : ¬(traceName core).holds p0 (ground X)) :
    ∃ s : Set W2, s ⊆ X ∧ G.IsClique s ∧ typeLT s = ω_ 1 ∧
      ∀ x ∈ s, ∃ q : P, q ≤ p0 ∧ ∃ j : W1, core.decides q j x := by
  obtain ⟨s, hs, ht, horigin⟩ := exists_ground_clique_in_positive_trace hclosed core p0 (ground X) hX
  exact ⟨s, fun x hx => (horigin x hx).choose_spec.2.1, hs, ht,
    fun x hx => by
      obtain ⟨q, hqp0, _, j, hj⟩ := horigin x hx
      exact ⟨q, hqp0, j, hj⟩⟩

end Erdos1172Part3NamedTraceExtraction
