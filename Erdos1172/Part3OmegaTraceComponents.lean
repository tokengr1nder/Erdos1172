/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3WeakStationaryProductLoss

@[expose] public section

/-!
# Positive finite components and the exact union boundary

Every positive omega-product trace has arbitrarily late rows containing
arbitrarily high positive finite levels. The proved finite extraction
theorem gives actual component names and transfers their finite losses.
The omega-level trace is explicitly not countably complete: finite
prefix covers are small, but their countable union covers the whole core.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3OmegaTraceComponents

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularConeRestriction (onCone)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3FiniteTraceSchemes (Index scheme scheme_extracts)
open Erdos1172Part3ProductTraceIdeal (rowCore)
open Erdos1172Part3OmegaPowerIndex (OmegaIndex)
open Erdos1172Part3OmegaLevelTrace

variable {P : Type} [Preorder P] {G : SimpleGraph W2}

theorem exists_late_positive_component (core : CliqueDecisions P (W1 ×ₗ OmegaIndex) W2 G)
    (p : P) (U : RegularName P W2) (hU : (neg (omegaProductTrace.trace core)).holds p U)
    (q : P) (hqp : q ≤ p) (rowBound : W1) (levelBound : ℕ) :
    ∃ s : P, s ≤ q ∧ ∃ row : W1, rowBound < row ∧ ∃ n : ℕ, levelBound < n ∧
      (neg (((scheme G n).forOrder P).trace (levelCore (rowCore core row) n))).holds s U := by
  obtain ⟨s, hsq, row, hrow, hs⟩ := Erdos1172Part3WeakProductTrace.exists_positive_row
    omegaWeakTrace core p U hU q hqp rowBound
  obtain ⟨t, hts, n, hn, ht⟩ := exists_positive_level (rowCore core row) s U hs s le_rfl levelBound
  exact ⟨t, hts.trans hsq, row, hrow, n, hn, ht⟩

theorem exists_late_component_subcore (hclosed : CountablyClosed P)
    (core : CliqueDecisions P (W1 ×ₗ OmegaIndex) W2 G) (p : P) (U : RegularName P W2)
    (hU : (neg (omegaProductTrace.trace core)).holds p U)
    (q : P) (hqp : q ≤ p) (rowBound : W1) (levelBound : ℕ) :
    ∃ s : P, s ≤ q ∧ ∃ row : W1, rowBound < row ∧ ∃ n : ℕ, levelBound < n ∧
      ∃ sub : CliqueDecisions (Set.Iic s) (Index n) W2 G,
        (∀ t i x, sub.decides t i x → U.holds t.val x ∧
          ∃ j : Index n, core.decides t.val (toLex (row, toLex ⟨n, j⟩)) x) ∧
        ∀ t : Set.Iic s, ∀ V : RegularName P W2,
          (((scheme G n).forOrder P).trace (levelCore (rowCore core row) n)).holds t.val V →
            (((scheme G n).forOrder (Set.Iic s)).trace sub).holds t (onCone s V) := by
  obtain ⟨s, hsq, row, hrow, n, hn, hs⟩ :=
    exists_late_positive_component core p U hU q hqp rowBound levelBound
  obtain ⟨t, hts, sub, hsub, htransfer⟩ := scheme_extracts G n hclosed
    (levelCore (rowCore core row) n) s U (fun h => hs s le_rfl h)
  exact ⟨t, hts.trans hsq, row, hrow, n, hn, sub, hsub, htransfer⟩

noncomputable def levelPrefix (core : CliqueDecisions P OmegaIndex W2 G) (n : ℕ) : RegularName P W2 :=
  regularize (fun p x => ∃ z : OmegaIndex, (ofLex z).1 ≤ n ∧ core.decides p z x)

theorem levelPrefix_of_decision (core : CliqueDecisions P OmegaIndex W2 G) (n : ℕ)
    {p : P} {z : OmegaIndex} {x : W2} (hn : (ofLex z).1 ≤ n) (hx : core.decides p z x) :
    (levelPrefix core n).holds p x :=
  fun q hqp => ⟨q, le_rfl, z, hn, core.persistent hqp hx⟩

theorem not_prefix_of_late_decision (core : CliqueDecisions P OmegaIndex W2 G) (bound n : ℕ)
    (hn : bound < n) {p : P} {i : Index n} {x : W2}
    (hx : (levelCore core n).decides p i x) : ¬(levelPrefix core bound).holds p x := by
  intro hprefix
  obtain ⟨q, hqp, z, hz, hxz⟩ := hprefix p le_rfl
  have hne : (toLex ⟨n, i⟩ : OmegaIndex) ≠ z := by
    intro heq
    have hlevel : n = (ofLex z).1 := congrArg (fun z : OmegaIndex => (ofLex z).1) heq
    exact hn.not_ge (hlevel.symm ▸ hz)
  exact G.irrefl (core.adjacent hne (core.persistent hqp hx) hxz)

theorem levelPrefix_small (core : CliqueDecisions P OmegaIndex W2 G) (p : P) (bound : ℕ) :
    (omegaTrace core).holds p (levelPrefix core bound) := by
  apply omegaTrace_of_witness core p (levelPrefix core bound)
  refine ⟨bound, fun n hn => ((scheme G n).forOrder P).of_avoids (levelCore core n) p _ ?_⟩
  intro q hqp i x hx
  exact not_prefix_of_late_decision core bound n hn hx

theorem prefix_join_positive (core : CliqueDecisions P OmegaIndex W2 G) (p : P) :
    (neg (omegaTrace core)).holds p (join (levelPrefix core)) := by
  apply omegaTrace_not_small_of_cover core p (join (levelPrefix core))
  intro q hqp z x hx
  exact join_of_holds (levelPrefix core) (ofLex z).1 (levelPrefix_of_decision core _ le_rfl hx)

theorem omegaTrace_countable_join_failure (core : CliqueDecisions P OmegaIndex W2 G) (p : P) :
    ∃ U : ℕ → RegularName P W2, (∀ n, (omegaTrace core).holds p (U n)) ∧
      ¬(omegaTrace core).holds p (join U) :=
  ⟨levelPrefix core, levelPrefix_small core p, prefix_join_positive core p p le_rfl⟩

end Erdos1172Part3OmegaTraceComponents
