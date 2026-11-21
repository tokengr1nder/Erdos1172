/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedConvergentCore

@[expose] public section

/-!
# Bounded traces on convergent core names

Trace smallness has dense witnesses for a bound on the core's index.
The bound may depend on the witnessing condition. Countable closure
combines countably many such bounds. Base-ideal smallness implies this
trace smallness for a convergent name, with actual membership retained.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedTraceIdeal

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularNamedIdeal
open Erdos1172Part3NamedConvergentCore (ConvergesBelow)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)

variable {P : Type} [Preorder P] {K : SimpleGraph W2}

def TailAvoid (core : CliqueDecisions P W1 W2 K) (p : P)
    (U : RegularName P W2) (bound : W1) : Prop :=
  ∀ q : P, q ≤ p → ∀ i : W1, bound < i → ∀ x : W2,
    core.decides q i x → ¬U.holds q x

theorem tailAvoid_persistent {core : CliqueDecisions P W1 W2 K} {p q : P}
    {U : RegularName P W2} {bound : W1} (hqp : q ≤ p) (h : TailAvoid core p U bound) :
    TailAvoid core q U bound := fun s hsq => h s (hsq.trans hqp)

def traceName (core : CliqueDecisions P W1 W2 K) : RegularName P (RegularName P W2) :=
  regularize (fun p U => ∃ bound, TailAvoid core p U bound)

theorem traceName_of_bound (core : CliqueDecisions P W1 W2 K) (p : P)
    (U : RegularName P W2) (bound : W1) (h : TailAvoid core p U bound) :
    (traceName core).holds p U :=
  fun q hqp => ⟨q, le_rfl, bound, tailAvoid_persistent hqp h⟩

theorem traceName_empty (core : CliqueDecisions P W1 W2 K) (p : P) :
    (traceName core).holds p (ground ∅) := by
  obtain ⟨bound, _⟩ := exists_bound_of_countable (∅ : Set W1) Set.countable_empty
  exact traceName_of_bound core p (ground ∅) bound (fun _ _ _ _ _ _ h => h)

theorem traceName_mono (core : CliqueDecisions P W1 W2 K) (p : P)
    (U V : RegularName P W2) (hsub : ∀ x, (implication U V).holds p x)
    (hV : (traceName core).holds p V) : (traceName core).holds p U := by
  intro q hqp
  obtain ⟨s, hsq, bound, hs⟩ := hV q hqp
  refine ⟨s, hsq, bound, ?_⟩
  intro t hts i hi x hx hUx
  exact hs t hts i hi x hx (hsub x t ((hts.trans hsq).trans hqp) hUx)

theorem traceName_countable_join (hclosed : CountablyClosed P)
    (core : CliqueDecisions P W1 W2 K) (p : P) (U : ℕ → RegularName P W2)
    (hU : ∀ n, (traceName core).holds p (U n)) :
    (traceName core).holds p (join U) := by
  intro q hqp
  obtain ⟨s, hsq, hs⟩ := exists_common_countable_witnesses hclosed q
    (fun t n => ∃ bound, TailAvoid core t (U n) bound) (by
      rintro t v n hvt ⟨bound, hb⟩
      exact ⟨bound, tailAvoid_persistent hvt hb⟩)
    (fun t htq n => hU n t (htq.trans hqp)) Cardinal.mk_nat.le
  choose bounds hbounds using hs
  obtain ⟨bound, hbound⟩ := exists_bound_of_countable (Set.range bounds) (Set.countable_range _)
  refine ⟨s, hsq, bound, ?_⟩
  intro t hts i hi x hx hjoin
  obtain ⟨v, hvt, n, hn⟩ := hjoin t le_rfl
  exact hbounds n v (hvt.trans hts) i ((hbound (bounds n) ⟨n, rfl⟩).trans hi) x
    (core.persistent hvt hx) hn

variable {I : Type} [LinearOrder I] {G H : SimpleGraph W2}
variable {r : Code P I G ↪ W2} {σ : NiceCliqueName P I W2 G ↪ W2}
variable {source : RegularName P W2} {a : W2}

theorem bound_of_base_witness (ha : GoodCut r σ H source a)
    (core : CliqueDecisions P W1 W2 K) (p0 : P)
    (hbelow : ∀ p i x, core.decides p i x → x < a)
    (hconv : ConvergesBelow r H a p0 core)
    (p : P) (hpp0 : p ≤ p0) (U : RegularName P W2)
    (hU : WitnessSmall r H a p U) : ∃ bound, TailAvoid core p U bound := by
  obtain ⟨c, hc, hn, hcover⟩ := hU
  obtain ⟨bound, hbound⟩ := hconv (SmallUnionCode.compl c) (ha.compl_lt c hc)
  refine ⟨bound, ?_⟩
  intro q hqp i hi x hx hUx
  have hca : (eval G H (SmallUnionCode.compl c)).holds q a := by
    rw [eval_compl]
    exact (neg (eval G H c)).persistent hqp hn
  have hcx := hbound q (hqp.trans hpp0) hca i hi x hx
  rw [eval_compl] at hcx
  exact hcx q le_rfl (hcover x (hbelow q i x hx) q hqp hUx)

theorem traceName_of_base_small (ha : GoodCut r σ H source a)
    (core : CliqueDecisions P W1 W2 K) (p0 : P)
    (hbelow : ∀ p i x, core.decides p i x → x < a)
    (hconv : ConvergesBelow r H a p0 core)
    (p : P) (hpp0 : p ≤ p0) (U : RegularName P W2)
    (hU : (smallName r H a).holds p U) : (traceName core).holds p U := by
  intro q hqp
  obtain ⟨s, hsq, hs⟩ := hU q hqp
  exact ⟨s, hsq, bound_of_base_witness ha core p0 hbelow hconv s ((hsq.trans hqp).trans hpp0) U hs⟩

end Erdos1172Part3NamedTraceIdeal
