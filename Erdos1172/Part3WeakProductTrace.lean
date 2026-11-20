/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3ProductTraceIdeal

@[expose] public section

/-!
# Product traces without a countable-union premise

The stationary derived-loss argument requires only monotonicity, base
inclusion, and positivity of the source. Countable completeness of the
new trace is not required. This smaller interface keeps precisely the
decision laws needed for product convergence and positive rows.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3WeakProductTrace

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3ClosedDecisionSystem (CliqueDecisions)
open Erdos1172Part3ProductTraceIdeal (CoreTrace rowCore)
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)
open Erdos1172Part3RegularNeighborhoodCode (Code GoodCut eval)
open Erdos1172Part3ControlledCoreProducts (ProductData)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3RegularNamedIdeal (smallName)
open Erdos1172Part3GuardedTraceFamily (priorSource)

structure WeakCoreTrace (P I : Type) [Preorder P] [LinearOrder I] (G : SimpleGraph W2) where
  trace : CliqueDecisions P I W2 G → RegularName P (RegularName P W2)
  empty : ∀ core p, (trace core).holds p (ground ∅)
  mono : ∀ core p U V, (∀ x, (implication U V).holds p x) →
    (trace core).holds p V → (trace core).holds p U
  on_decisions : ∀ core p U V,
    (∀ q : P, q ≤ p → ∀ i x, core.decides q i x → U.holds q x → V.holds q x) →
    (trace core).holds p V → (trace core).holds p U
  of_avoids : ∀ core p U,
    (∀ q : P, q ≤ p → ∀ i x, core.decides q i x → ¬U.holds q x) → (trace core).holds p U
  not_small_of_cover : ∀ core p U,
    (∀ q : P, q ≤ p → ∀ i x, core.decides q i x → U.holds q x) → (neg (trace core)).holds p U

variable {P I : Type} [Preorder P] [LinearOrder I] {G : SimpleGraph W2}

def ofCoreTrace (T : CoreTrace P I G) : WeakCoreTrace P I G :=
  ⟨T.trace, T.empty, T.mono, T.on_decisions, T.of_avoids, T.not_small_of_cover⟩

def ProductSmall (T : WeakCoreTrace P I G) (core : CliqueDecisions P (W1 ×ₗ I) W2 G)
    (p : P) (U : RegularName P W2) : Prop :=
  ∃ bound : W1, ∀ i : W1, bound < i → (T.trace (rowCore core i)).holds p U

theorem productSmall_persistent {T : WeakCoreTrace P I G}
    {core : CliqueDecisions P (W1 ×ₗ I) W2 G} {p q : P} {U : RegularName P W2}
    (hqp : q ≤ p) (h : ProductSmall T core p U) : ProductSmall T core q U := by
  obtain ⟨bound, hb⟩ := h
  exact ⟨bound, fun i hi => (T.trace (rowCore core i)).persistent hqp (hb i hi)⟩

def productTrace (T : WeakCoreTrace P I G) (core : CliqueDecisions P (W1 ×ₗ I) W2 G) :
    RegularName P (RegularName P W2) := regularize (ProductSmall T core)

theorem productTrace_of_witness (T : WeakCoreTrace P I G) (core : CliqueDecisions P (W1 ×ₗ I) W2 G)
    (p : P) (U : RegularName P W2) (h : ProductSmall T core p U) :
    (productTrace T core).holds p U :=
  fun q hqp => ⟨q, le_rfl, productSmall_persistent hqp h⟩

theorem productTrace_empty (T : WeakCoreTrace P I G) (core : CliqueDecisions P (W1 ×ₗ I) W2 G)
    (p : P) : (productTrace T core).holds p (ground ∅) := by
  obtain ⟨bound, _⟩ := exists_bound_of_countable (∅ : Set W1) Set.countable_empty
  exact productTrace_of_witness T core p (ground ∅) ⟨bound, fun i _ => T.empty (rowCore core i) p⟩

theorem productTrace_mono (T : WeakCoreTrace P I G) (core : CliqueDecisions P (W1 ×ₗ I) W2 G)
    (p : P) (U V : RegularName P W2) (hsub : ∀ x, (implication U V).holds p x)
    (hV : (productTrace T core).holds p V) : (productTrace T core).holds p U := by
  intro q hqp
  obtain ⟨s, hsq, bound, hs⟩ := hV q hqp
  exact ⟨s, hsq, bound, fun i hi => T.mono (rowCore core i) s U V
    (fun x => (implication U V).persistent (hsq.trans hqp) (hsub x)) (hs i hi)⟩

theorem productTrace_on_decisions (T : WeakCoreTrace P I G)
    (core : CliqueDecisions P (W1 ×ₗ I) W2 G) (p : P) (U V : RegularName P W2)
    (hsub : ∀ q : P, q ≤ p → ∀ z x, core.decides q z x → U.holds q x → V.holds q x)
    (hV : (productTrace T core).holds p V) : (productTrace T core).holds p U := by
  intro q hqp
  obtain ⟨s, hsq, bound, hs⟩ := hV q hqp
  refine ⟨s, hsq, bound, fun i hi => T.on_decisions (rowCore core i) s U V ?_ (hs i hi)⟩
  intro t hts j x hx hUx
  exact hsub t ((hts.trans hsq).trans hqp) (toLex (i, j)) x hx hUx

theorem productTrace_of_avoids (T : WeakCoreTrace P I G) (core : CliqueDecisions P (W1 ×ₗ I) W2 G)
    (p : P) (U : RegularName P W2)
    (h : ∀ q : P, q ≤ p → ∀ z x, core.decides q z x → ¬U.holds q x) :
    (productTrace T core).holds p U := by
  obtain ⟨bound, _⟩ := exists_bound_of_countable (∅ : Set W1) Set.countable_empty
  exact productTrace_of_witness T core p U ⟨bound, fun i _ => T.of_avoids (rowCore core i) p U
    (fun q hqp j x hx => h q hqp (toLex (i, j)) x hx)⟩

theorem productTrace_not_small_of_cover (T : WeakCoreTrace P I G)
    (core : CliqueDecisions P (W1 ×ₗ I) W2 G) (p : P) (U : RegularName P W2)
    (h : ∀ q : P, q ≤ p → ∀ z x, core.decides q z x → U.holds q x) :
    (neg (productTrace T core)).holds p U := by
  intro q hqp hsmall
  obtain ⟨s, hsq, bound, hs⟩ := hsmall q le_rfl
  obtain ⟨i, hi⟩ := exists_bound_of_countable ({bound} : Set W1) (by simp)
  exact T.not_small_of_cover (rowCore core i) s U
    (fun t hts j x hx => h t ((hts.trans hsq).trans hqp) (toLex (i, j)) x hx)
    s le_rfl (hs i (hi bound (by simp)))

def WeakCoreTrace.product (T : WeakCoreTrace P I G) : WeakCoreTrace P (W1 ×ₗ I) G where
  trace := productTrace T
  empty := productTrace_empty T
  mono := productTrace_mono T
  on_decisions := productTrace_on_decisions T
  of_avoids := productTrace_of_avoids T
  not_small_of_cover := productTrace_not_small_of_cover T

theorem exists_positive_row (T : WeakCoreTrace P I G) (core : CliqueDecisions P (W1 ×ₗ I) W2 G)
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

variable {H : SimpleGraph W2} {r : Code P I G ↪ W2}
variable {σ : NiceCliqueName P I W2 G ↪ W2} {source : RegularName P W2} {a : W2}

theorem base_small_to_product_trace (T : WeakCoreTrace P I G) (data : ProductData r H source a)
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

theorem prior_source_product_positive (T : WeakCoreTrace P I G) (data : ProductData r H source a)
    (p : P) (hp : source.holds p a) :
    (neg (productTrace T data.name.toClique)).holds p (priorSource source a) := by
  apply productTrace_not_small_of_cover T data.name.toClique p (priorSource source a)
  intro q hqp z x hx
  exact ⟨data.actual_source q (source.persistent hqp hp) z x hx, (data.geometry q z x hx).1⟩

end Erdos1172Part3WeakProductTrace
