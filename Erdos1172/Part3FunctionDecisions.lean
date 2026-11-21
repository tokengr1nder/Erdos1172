/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3StationaryDecisions

@[expose] public section

/-!
# Function decisions and countable simultaneous decisions

These explicit ground-type decision systems are the function names used
by an additional dominating-function stage. Countable closure decides a
countable family at once. It is not used to decide omegaOne many values
under one condition.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3FunctionDecisions

open ErdosRadoCHAsym (W1)
open Erdos1172Part3ClosedDecisionSystem
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)

structure FunctionDecisions (P I V : Type) [Preorder P] where
  decides : P → I → V → Prop
  dense : ∀ p i, ∃ q, q ≤ p ∧ ∃ v, decides q i v
  persistent : ∀ {p q i v}, q ≤ p → decides p i v → decides q i v
  unique : ∀ {p i v w}, decides p i v → decides p i w → v = w

variable {P I V : Type} [Preorder P]

def FunctionDecisions.ofFunction (f : I → V) : FunctionDecisions P I V where
  decides _ i v := f i = v
  dense p i := ⟨p, le_rfl, f i, rfl⟩
  persistent _ h := h
  unique h h' := h.symm.trans h'

/-- The single lower bound is taken at a countable stage beyond the
countably many relevant coordinates of the omegaOne construction. -/
theorem FunctionDecisions.exists_simultaneous (F : FunctionDecisions P I V)
    (hclosed : CountablyClosed P) (p0 : P) (hI : #I ≤ ℵ₀) :
    ∃ q : P, q ≤ p0 ∧ ∀ i : I, ∃ v : V, F.decides q i v := by
  classical
  obtain ⟨index⟩ : Nonempty (I ↪ W1) := (Cardinal.le_def _ _).mp (by
    simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using
      hI.trans (Cardinal.aleph0_le_aleph 1))
  let D (j : W1) : Set P := {p | ∀ i, index i = j → ∃ v, F.decides p i v}
  have hD : ∀ j, DenseBelow (D j) := by
    intro j p
    by_cases h : ∃ i, index i = j
    · obtain ⟨q, hqp, v, hv⟩ := F.dense p h.choose
      refine ⟨q, ?_, hqp⟩
      intro i hi
      have heq : i = h.choose := index.injective (hi.trans h.choose_spec.symm)
      subst i
      exact ⟨v, hv⟩
    · exact ⟨p, fun i hi => (h ⟨i, hi⟩).elim, le_rfl⟩
  obtain ⟨conditions, hanti, hstart, hmeet⟩ := exists_antitone_dense_sequence hclosed p0 D hD
  have hcount : (Set.range index).Countable :=
    Cardinal.le_aleph0_iff_set_countable.mp (Cardinal.mk_range_le.trans hI)
  obtain ⟨bound, hbound⟩ := exists_bound_of_countable (Set.range index) hcount
  refine ⟨conditions bound, hstart bound, ?_⟩
  intro i
  obtain ⟨v, hv⟩ := hmeet (index i) i rfl
  exact ⟨v, F.persistent (hanti (hbound (index i) ⟨i, rfl⟩).le) hv⟩

/-- A condition bounds all later decisions for this function value. -/
def BoundedAt (F : FunctionDecisions P W1 W1) (p : P) (i bound : W1) : Prop :=
  ∀ q : P, q ≤ p → ∀ v : W1, F.decides q i v → v < bound

theorem boundedAt_mono {F : FunctionDecisions P W1 W1} {p q : P} {i bound : W1}
    (h : BoundedAt F p i bound) (hqp : q ≤ p) : BoundedAt F q i bound :=
  fun r hr v hv => h r (hr.trans hqp) v hv

theorem boundedAt_of_decides {F : FunctionDecisions P W1 W1} {p : P} {i v bound : W1}
    (hv : F.decides p i v) (hbound : v < bound) : BoundedAt F p i bound := by
  intro q hqp w hw
  exact (F.unique hw (F.persistent hqp hv)).trans_lt hbound

/-- At a fixed coordinate, one strengthening bounds countably many
function names. These names need not come from ground functions. -/
theorem exists_bound_for_countable_family {J : Type}
    (hclosed : CountablyClosed P) (p0 : P) (F : J → FunctionDecisions P W1 W1)
    (hJ : #J ≤ ℵ₀) (i : W1) :
    ∃ q : P, q ≤ p0 ∧ ∃ bound : W1, ∀ j : J, BoundedAt (F j) q i bound := by
  classical
  let values : FunctionDecisions P J W1 :=
    ⟨fun p j v => (F j).decides p i v,
      fun p j => (F j).dense p i,
      fun {p q j v} hqp hv => (F j).persistent hqp hv,
      fun {p j v w} hv hw => (F j).unique hv hw⟩
  obtain ⟨q, hqp, hvalues⟩ := values.exists_simultaneous hclosed p0 hJ
  let chosen (j : J) : W1 := (hvalues j).choose
  have hcount : (Set.range chosen).Countable :=
    Cardinal.le_aleph0_iff_set_countable.mp (Cardinal.mk_range_le.trans hJ)
  obtain ⟨bound, hb⟩ := exists_bound_of_countable (Set.range chosen) hcount
  exact ⟨q, hqp, bound, fun j => boundedAt_of_decides (hvalues j).choose_spec
    (hb (chosen j) ⟨j, rfl⟩)⟩

end Erdos1172Part3FunctionDecisions
