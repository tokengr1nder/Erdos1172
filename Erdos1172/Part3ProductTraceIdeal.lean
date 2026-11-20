/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3ControlledCoreProducts

@[expose] public section

/-!
# Iterating regular trace ideals on whole-block products

The trace ideal of an inner core induces a trace ideal on omegaOne many
rows: densely, every sufficiently late row has small inner trace. The
construction preserves countable unions and positivity of a source
cover. It can be iterated; in particular it supplies a cubic trace ideal.
No stationary completely red future is asserted by this construction.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3ProductTraceIdeal

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3RegularNamedIdeal (exists_common_countable_witnesses smallName)
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)
open Erdos1172Part3RegularNeighborhoodCode (Code GoodCut eval)
open Erdos1172Part3ControlledCoreProducts (ProductData)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3StationarySquareDecisions (Square)
open Erdos1172Part3FullSourceCubes (Cube)

structure CoreTrace (P I : Type) [Preorder P] [LinearOrder I] (G : SimpleGraph W2) where
  trace : CliqueDecisions P I W2 G → RegularName P (RegularName P W2)
  empty : ∀ core p, (trace core).holds p (ground ∅)
  mono : ∀ core p U V, (∀ x, (implication U V).holds p x) →
    (trace core).holds p V → (trace core).holds p U
  on_decisions : ∀ core p U V,
    (∀ q : P, q ≤ p → ∀ i x, core.decides q i x → U.holds q x → V.holds q x) →
    (trace core).holds p V → (trace core).holds p U
  countable_join : CountablyClosed P → ∀ core p (U : ℕ → RegularName P W2),
    (∀ n, (trace core).holds p (U n)) → (trace core).holds p (join U)
  of_avoids : ∀ core p U,
    (∀ q : P, q ≤ p → ∀ i x, core.decides q i x → ¬U.holds q x) → (trace core).holds p U
  not_small_of_cover : ∀ core p U,
    (∀ q : P, q ≤ p → ∀ i x, core.decides q i x → U.holds q x) → (neg (trace core)).holds p U

variable {P I : Type} [Preorder P] [LinearOrder I] {G : SimpleGraph W2}

def rowCore (core : CliqueDecisions P (W1 ×ₗ I) W2 G) (i : W1) :
    CliqueDecisions P I W2 G where
  decides p j x := core.decides p (toLex (i, j)) x
  dense p j := core.dense p (toLex (i, j))
  persistent := core.persistent
  unique := core.unique
  ordered hij hx hy := core.ordered (by
    rw [Prod.Lex.lt_iff]
    exact Or.inr ⟨rfl, hij⟩) hx hy
  adjacent hij hx hy := core.adjacent (by
    intro h
    exact hij (congrArg (fun z : W1 ×ₗ I => (ofLex z).2) h)) hx hy

def WitnessProductSmall (T : CoreTrace P I G) (core : CliqueDecisions P (W1 ×ₗ I) W2 G)
    (p : P) (U : RegularName P W2) : Prop :=
  ∃ bound : W1, ∀ i : W1, bound < i → (T.trace (rowCore core i)).holds p U

theorem witnessProductSmall_persistent {T : CoreTrace P I G}
    {core : CliqueDecisions P (W1 ×ₗ I) W2 G} {p q : P} {U : RegularName P W2}
    (hqp : q ≤ p) (h : WitnessProductSmall T core p U) : WitnessProductSmall T core q U := by
  obtain ⟨bound, hb⟩ := h
  exact ⟨bound, fun i hi => (T.trace (rowCore core i)).persistent hqp (hb i hi)⟩

def productTrace (T : CoreTrace P I G) (core : CliqueDecisions P (W1 ×ₗ I) W2 G) :
    RegularName P (RegularName P W2) := regularize (WitnessProductSmall T core)

theorem productTrace_of_witness (T : CoreTrace P I G) (core : CliqueDecisions P (W1 ×ₗ I) W2 G)
    (p : P) (U : RegularName P W2) (h : WitnessProductSmall T core p U) :
    (productTrace T core).holds p U :=
  fun q hqp => ⟨q, le_rfl, witnessProductSmall_persistent hqp h⟩

theorem productTrace_empty (T : CoreTrace P I G) (core : CliqueDecisions P (W1 ×ₗ I) W2 G)
    (p : P) : (productTrace T core).holds p (ground ∅) := by
  obtain ⟨bound, _⟩ := exists_bound_of_countable (∅ : Set W1) Set.countable_empty
  exact productTrace_of_witness T core p (ground ∅) ⟨bound, fun i _ => T.empty (rowCore core i) p⟩

theorem productTrace_mono (T : CoreTrace P I G) (core : CliqueDecisions P (W1 ×ₗ I) W2 G)
    (p : P) (U V : RegularName P W2) (hsub : ∀ x, (implication U V).holds p x)
    (hV : (productTrace T core).holds p V) : (productTrace T core).holds p U := by
  intro q hqp
  obtain ⟨s, hsq, bound, hs⟩ := hV q hqp
  exact ⟨s, hsq, bound, fun i hi => T.mono (rowCore core i) s U V
    (fun x => (implication U V).persistent (hsq.trans hqp) (hsub x)) (hs i hi)⟩

theorem productTrace_on_decisions (T : CoreTrace P I G)
    (core : CliqueDecisions P (W1 ×ₗ I) W2 G) (p : P) (U V : RegularName P W2)
    (hsub : ∀ q : P, q ≤ p → ∀ z x, core.decides q z x → U.holds q x → V.holds q x)
    (hV : (productTrace T core).holds p V) : (productTrace T core).holds p U := by
  intro q hqp
  obtain ⟨s, hsq, bound, hs⟩ := hV q hqp
  refine ⟨s, hsq, bound, fun i hi => T.on_decisions (rowCore core i) s U V ?_ (hs i hi)⟩
  intro t hts j x hx hUx
  exact hsub t ((hts.trans hsq).trans hqp) (toLex (i, j)) x hx hUx

theorem productTrace_countable_join (T : CoreTrace P I G) (hclosed : CountablyClosed P)
    (core : CliqueDecisions P (W1 ×ₗ I) W2 G) (p : P) (U : ℕ → RegularName P W2)
    (hU : ∀ n, (productTrace T core).holds p (U n)) : (productTrace T core).holds p (join U) := by
  intro q hqp
  obtain ⟨s, hsq, hs⟩ := exists_common_countable_witnesses hclosed q
    (fun t n => WitnessProductSmall T core t (U n))
    (fun hvt h => witnessProductSmall_persistent hvt h)
    (fun t htq n => hU n t (htq.trans hqp)) Cardinal.mk_nat.le
  choose bounds hbounds using hs
  obtain ⟨bound, hbound⟩ := exists_bound_of_countable (Set.range bounds) (Set.countable_range _)
  exact ⟨s, hsq, bound, fun i hi => T.countable_join hclosed (rowCore core i) s U
    (fun n => hbounds n i ((hbound (bounds n) ⟨n, rfl⟩).trans hi))⟩

theorem productTrace_of_avoids (T : CoreTrace P I G) (core : CliqueDecisions P (W1 ×ₗ I) W2 G)
    (p : P) (U : RegularName P W2)
    (h : ∀ q : P, q ≤ p → ∀ z x, core.decides q z x → ¬U.holds q x) :
    (productTrace T core).holds p U := by
  obtain ⟨bound, _⟩ := exists_bound_of_countable (∅ : Set W1) Set.countable_empty
  exact productTrace_of_witness T core p U ⟨bound, fun i _ => T.of_avoids (rowCore core i) p U
    (fun q hqp j x hx => h q hqp (toLex (i, j)) x hx)⟩

theorem productTrace_not_small_of_cover (T : CoreTrace P I G)
    (core : CliqueDecisions P (W1 ×ₗ I) W2 G) (p : P) (U : RegularName P W2)
    (h : ∀ q : P, q ≤ p → ∀ z x, core.decides q z x → U.holds q x) :
    (neg (productTrace T core)).holds p U := by
  intro q hqp hsmall
  obtain ⟨s, hsq, bound, hs⟩ := hsmall q le_rfl
  obtain ⟨i, hi⟩ := exists_bound_of_countable ({bound} : Set W1) (by simp)
  exact T.not_small_of_cover (rowCore core i) s U
    (fun t hts j x hx => h t ((hts.trans hsq).trans hqp) (toLex (i, j)) x hx)
    s le_rfl (hs i (hi bound (by simp)))

def CoreTrace.product (T : CoreTrace P I G) : CoreTrace P (W1 ×ₗ I) G where
  trace := productTrace T
  empty := productTrace_empty T
  mono := productTrace_mono T
  on_decisions := productTrace_on_decisions T
  countable_join := productTrace_countable_join T
  of_avoids := productTrace_of_avoids T
  not_small_of_cover := productTrace_not_small_of_cover T

theorem exists_positive_row (T : CoreTrace P I G) (core : CliqueDecisions P (W1 ×ₗ I) W2 G)
    (p : P) (U : RegularName P W2) (hU : (neg (productTrace T core)).holds p U)
    (q : P) (hqp : q ≤ p) (bound : W1) :
    ∃ s : P, s ≤ q ∧ ∃ i : W1, bound < i ∧ (neg (T.trace (rowCore core i))).holds s U := by
  classical
  by_contra h
  have hrows : ∀ i : W1, bound < i → (T.trace (rowCore core i)).holds q U := by
    intro i hi
    by_contra hrow
    obtain ⟨s, hsq, hs⟩ := (not_holds_iff_exists_neg (T.trace (rowCore core i)) q U).mp hrow
    exact h ⟨s, hsq, i, hi, hs⟩
  exact hU q hqp (productTrace_of_witness T core q U ⟨bound, hrows⟩)

noncomputable def lineTrace : CoreTrace P W1 G where
  trace := Erdos1172Part3NamedTraceIdeal.traceName
  empty := Erdos1172Part3NamedTraceIdeal.traceName_empty
  mono := Erdos1172Part3NamedTraceIdeal.traceName_mono
  on_decisions := Erdos1172Part3NamedTraceSubsequence.traceName_mono_on_decisions
  countable_join := Erdos1172Part3NamedTraceIdeal.traceName_countable_join
  of_avoids := by
    intro core p U h
    obtain ⟨bound, _⟩ := exists_bound_of_countable (∅ : Set W1) Set.countable_empty
    exact Erdos1172Part3NamedTraceIdeal.traceName_of_bound core p U bound
      (fun q hqp i _ x hx => h q hqp i x hx)
  not_small_of_cover := Erdos1172Part3NamedTraceSubsequence.named_cover_not_small

noncomputable def squareTrace : CoreTrace P Square G := (lineTrace (P := P) (G := G)).product

theorem squareTrace_eq (core : CliqueDecisions P Square W2 G) :
    squareTrace.trace core = Erdos1172Part3NamedSquareTraceIdeal.squareTraceName core := by
  apply RegularName.ext
  intro p U
  exact Iff.rfl

noncomputable def cubeTrace : CoreTrace P Cube G := (squareTrace (P := P) (G := G)).product

variable {H : SimpleGraph W2} {r : Code P I G ↪ W2}
variable {σ : NiceCliqueName P I W2 G ↪ W2} {source : RegularName P W2} {a : W2}

theorem base_small_to_product_trace (T : CoreTrace P I G) (data : ProductData r H source a)
    (ha : GoodCut r σ H source a) (p : P) (hp : source.holds p a)
    (U : RegularName P W2) (hU : (smallName r H a).holds p U) :
    (productTrace T data.name.toClique).holds p U := by
  intro q hqp
  obtain ⟨s, hsq, c, hc, hn, hcover⟩ := hU q hqp
  have hca : (eval G H (SmallUnionCode.compl c)).holds s a := by
    rw [Erdos1172Part3RegularNeighborhoodCode.eval_compl]
    exact hn
  obtain ⟨t, hts, bound, hbound⟩ := data.converges (SmallUnionCode.compl c)
    (ha.compl_lt c hc) s (source.persistent (hsq.trans hqp) hp) hca s le_rfl
  refine ⟨t, hts.trans hsq, bound, fun i hi => T.of_avoids (rowCore data.name.toClique i) t U ?_⟩
  intro v hvt j x hx hUx
  have hcx := hbound v hvt (toLex (i, j)) hi x hx
  rw [Erdos1172Part3RegularNeighborhoodCode.eval_compl] at hcx
  exact hcx v le_rfl (hcover x (data.geometry v (toLex (i, j)) x hx).1 v (hvt.trans hts) hUx)

theorem prior_source_product_positive (T : CoreTrace P I G) (data : ProductData r H source a)
    (p : P) (hp : source.holds p a) :
    (neg (productTrace T data.name.toClique)).holds p
      (Erdos1172Part3GuardedTraceFamily.priorSource source a) := by
  apply productTrace_not_small_of_cover T data.name.toClique p
    (Erdos1172Part3GuardedTraceFamily.priorSource source a)
  intro q hqp z x hx
  exact ⟨data.actual_source q (source.persistent hqp hp) z x hx, (data.geometry q z x hx).1⟩

end Erdos1172Part3ProductTraceIdeal
