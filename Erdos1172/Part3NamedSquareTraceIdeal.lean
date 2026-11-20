/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedTraceSubsequence
public import Erdos1172.Part3ControlledSourceSquare

@[expose] public section

/-!
# The regular row trace ideal on a named square

Smallness means that, densely, every sufficiently late row has small
trace. Inner bounds remain regular, condition-dependent witnesses; no
simultaneous decision of omegaOne many bounds is assumed.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedSquareTraceIdeal

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularNamedIdeal
open Erdos1172Part3NamedTraceIdeal
open Erdos1172Part3NamedTraceSubsequence (named_cover_not_small traceName_mono_on_decisions)
open Erdos1172Part3ControlledSourceSquare (SquareConvergesBelow)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3StationarySquareDecisions (Square)
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)

variable {P : Type} [Preorder P] {G H : SimpleGraph W2}

def rowCore (core : CliqueDecisions P Square W2 G) (i : W1) :
    CliqueDecisions P W1 W2 G where
  decides p j x := core.decides p (toLex (i, j)) x
  dense p j := core.dense p (toLex (i, j))
  persistent := core.persistent
  unique := core.unique
  ordered hij hx hy := core.ordered (by
    rw [Prod.Lex.lt_iff]
    exact Or.inr ⟨rfl, hij⟩) hx hy
  adjacent hij hx hy := core.adjacent (by
    intro h
    exact hij (congrArg (fun z : Square => (ofLex z).2) h)) hx hy

def WitnessSquareSmall (core : CliqueDecisions P Square W2 G) (p : P)
    (U : RegularName P W2) : Prop :=
  ∃ bound : W1, ∀ i : W1, bound < i → (traceName (rowCore core i)).holds p U

theorem witnessSquareSmall_persistent {core : CliqueDecisions P Square W2 G} {p q : P}
    {U : RegularName P W2} (hqp : q ≤ p) (h : WitnessSquareSmall core p U) :
    WitnessSquareSmall core q U := by
  obtain ⟨bound, hb⟩ := h
  exact ⟨bound, fun i hi => (traceName (rowCore core i)).persistent hqp (hb i hi)⟩

def squareTraceName (core : CliqueDecisions P Square W2 G) :
    RegularName P (RegularName P W2) := regularize (WitnessSquareSmall core)

theorem squareTraceName_of_witness (core : CliqueDecisions P Square W2 G) (p : P)
    (U : RegularName P W2) (h : WitnessSquareSmall core p U) :
    (squareTraceName core).holds p U :=
  fun q hqp => ⟨q, le_rfl, witnessSquareSmall_persistent hqp h⟩

theorem squareTraceName_empty (core : CliqueDecisions P Square W2 G) (p : P) :
    (squareTraceName core).holds p (ground ∅) := by
  obtain ⟨bound, _⟩ := exists_bound_of_countable (∅ : Set W1) Set.countable_empty
  exact squareTraceName_of_witness core p (ground ∅)
    ⟨bound, fun i _ => traceName_empty (rowCore core i) p⟩

theorem squareTraceName_mono (core : CliqueDecisions P Square W2 G) (p : P)
    (U V : RegularName P W2) (hsub : ∀ x, (implication U V).holds p x)
    (hV : (squareTraceName core).holds p V) : (squareTraceName core).holds p U := by
  intro q hqp
  obtain ⟨s, hsq, bound, hs⟩ := hV q hqp
  exact ⟨s, hsq, bound, fun i hi => traceName_mono (rowCore core i) s U V
    (fun x => (implication U V).persistent (hsq.trans hqp) (hsub x)) (hs i hi)⟩

theorem squareTraceName_countable_join (hclosed : CountablyClosed P)
    (core : CliqueDecisions P Square W2 G) (p : P) (U : ℕ → RegularName P W2)
    (hU : ∀ n, (squareTraceName core).holds p (U n)) :
    (squareTraceName core).holds p (join U) := by
  intro q hqp
  obtain ⟨s, hsq, hs⟩ := exists_common_countable_witnesses hclosed q
    (fun t n => WitnessSquareSmall core t (U n))
    (fun hvt h => witnessSquareSmall_persistent hvt h)
    (fun t htq n => hU n t (htq.trans hqp)) Cardinal.mk_nat.le
  choose bounds hbounds using hs
  obtain ⟨bound, hbound⟩ := exists_bound_of_countable (Set.range bounds) (Set.countable_range _)
  refine ⟨s, hsq, bound, ?_⟩
  intro i hi
  exact traceName_countable_join hclosed (rowCore core i) s U
    (fun n => hbounds n i ((hbound (bounds n) ⟨n, rfl⟩).trans hi))

theorem named_cover_not_square_small (core : CliqueDecisions P Square W2 G)
    (p0 : P) (U : RegularName P W2)
    (hcover : ∀ p : P, p ≤ p0 → ∀ z x, core.decides p z x → U.holds p x) :
    (neg (squareTraceName core)).holds p0 U := by
  intro p hpp0 hsmall
  obtain ⟨q, hqp, bound, hbound⟩ := hsmall p le_rfl
  obtain ⟨i, hi⟩ := exists_bound_of_countable ({bound} : Set W1) (by simp)
  exact named_cover_not_small (rowCore core i) q U
    (fun s hsq j x hx => hcover s ((hsq.trans hqp).trans hpp0) (toLex (i, j)) x hx)
    q le_rfl (hbound i (hi bound (by simp)))

theorem squareTraceName_mono_on_decisions (core : CliqueDecisions P Square W2 G) (p : P)
    (U V : RegularName P W2)
    (hsub : ∀ q : P, q ≤ p → ∀ z x, core.decides q z x → U.holds q x → V.holds q x)
    (hV : (squareTraceName core).holds p V) : (squareTraceName core).holds p U := by
  intro q hqp
  obtain ⟨s, hsq, bound, hs⟩ := hV q hqp
  refine ⟨s, hsq, bound, fun i hi => traceName_mono_on_decisions (rowCore core i) s U V ?_
    (hs i hi)⟩
  intro t hts j x hx hUx
  exact hsub t ((hts.trans hsq).trans hqp) (toLex (i, j)) x hx hUx

/-- A positive square has positive rows arbitrarily far out below every
condition. Only one row is selected at each refinement. -/
theorem exists_positive_row (core : CliqueDecisions P Square W2 G) (p : P)
    (U : RegularName P W2) (hU : (neg (squareTraceName core)).holds p U)
    (q : P) (hqp : q ≤ p) (bound : W1) :
    ∃ s : P, s ≤ q ∧ ∃ i : W1, bound < i ∧
      (neg (traceName (rowCore core i))).holds s U := by
  classical
  by_contra h
  have hrows : ∀ i : W1, bound < i → (traceName (rowCore core i)).holds q U := by
    intro i hi
    by_contra hrow
    obtain ⟨s, hsq, hs⟩ := (not_holds_iff_exists_neg (traceName (rowCore core i)) q U).mp hrow
    exact h ⟨s, hsq, i, hi, hs⟩
  exact hU q hqp (squareTraceName_of_witness core q U ⟨bound, hrows⟩)

variable {r : Code P W1 G ↪ W2} {σ : NiceCliqueName P W1 W2 G ↪ W2}
variable {source : RegularName P W2} {a : W2}

theorem square_witness_of_base_witness (ha : GoodCut r σ H source a)
    (core : CliqueDecisions P Square W2 G) (p0 : P)
    (hbelow : ∀ p z x, core.decides p z x → x < a)
    (hconv : SquareConvergesBelow r H a p0 core)
    (p : P) (hpp0 : p ≤ p0) (U : RegularName P W2)
    (hU : WitnessSmall r H a p U) : WitnessSquareSmall core p U := by
  obtain ⟨c, hc, hn, hcover⟩ := hU
  obtain ⟨bound, hbound⟩ := hconv (SmallUnionCode.compl c) (ha.compl_lt c hc)
  obtain ⟨innerBound, _⟩ := exists_bound_of_countable (∅ : Set W1) Set.countable_empty
  refine ⟨bound, fun i hi => traceName_of_bound (rowCore core i) p U innerBound ?_⟩
  intro q hqp j _ x hx hUx
  have hca : (eval G H (SmallUnionCode.compl c)).holds q a := by
    rw [eval_compl]
    exact (neg (eval G H c)).persistent hqp hn
  have hcx := hbound q (hqp.trans hpp0) hca (toLex (i, j)) hi x hx
  rw [eval_compl] at hcx
  exact hcx q le_rfl (hcover x (hbelow q (toLex (i, j)) x hx) q hqp hUx)

theorem squareTraceName_of_base_small (ha : GoodCut r σ H source a)
    (core : CliqueDecisions P Square W2 G) (p0 : P)
    (hbelow : ∀ p z x, core.decides p z x → x < a)
    (hconv : SquareConvergesBelow r H a p0 core)
    (p : P) (hpp0 : p ≤ p0) (U : RegularName P W2)
    (hU : (smallName r H a).holds p U) : (squareTraceName core).holds p U := by
  intro q hqp
  obtain ⟨s, hsq, hs⟩ := hU q hqp
  exact ⟨s, hsq, square_witness_of_base_witness ha core p0 hbelow hconv s
    ((hsq.trans hqp).trans hpp0) U hs⟩

end Erdos1172Part3NamedSquareTraceIdeal
