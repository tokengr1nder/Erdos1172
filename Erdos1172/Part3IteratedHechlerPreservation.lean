/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3FiniteHechlerStages

@[expose] public section

/-!
# Lifting earlier clique and stationary-future decisions

The projection to the earlier condition has exact lifting: any earlier
strengthening lifts without altering the new stem or its side names.
Consequently earlier persistent stationary possibilities are preserved
and reflected, while earlier clique decisions lift unchanged.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3IteratedHechlerPreservation

open ErdosRadoCHAsym (W2)
open Erdos1172Part3ClosedDecisionSystem (CliqueDecisions)
open Erdos1172Part3StationaryDecisions
open Erdos1172Part3IteratedHechlerOrder

variable {P : Type} [Preorder P]

def liftPredicate (U : P → W2 → Prop) : Condition P → W2 → Prop :=
  fun p a => U p.base a

theorem liftPredicate_persistent {U : P → W2 → Prop} (hU : Persistent U) :
    Persistent (liftPredicate U) := fun hqp ha => hU (base_le hqp) ha

theorem possible_liftPredicate (U : P → W2 → Prop) (p : Condition P) :
    possible (liftPredicate U) p = possible U p.base := by
  ext a
  constructor
  · rintro ⟨q, hqp, hqa⟩
    exact ⟨q.base, base_le hqp, hqa⟩
  · rintro ⟨q, hqp, hqa⟩
    exact ⟨liftBase p q, liftBase_le p hqp, hqa⟩

/-- All earlier strengthenings are still accessible in the new order,
so stationarity of possible membership is preserved and reflected. -/
theorem stationaryAt_liftPredicate_iff (U : P → W2 → Prop) (p : Condition P) :
    StationaryAt (liftPredicate U) p ↔ StationaryAt U p.base := by
  constructor
  · intro h q hqp
    have hstat := h (liftBase p q) (liftBase_le p hqp)
    simpa only [possible_liftPredicate, liftBase] using hstat
  · intro h q hqp
    rw [possible_liftPredicate]
    exact h q.base (base_le hqp)

def liftClique {I V : Type} [LinearOrder I] [LinearOrder V] {G : SimpleGraph V}
    (sys : CliqueDecisions P I V G) : CliqueDecisions (Condition P) I V G where
  decides p i v := sys.decides p.base i v
  dense := by
    intro p i
    obtain ⟨q, hqp, v, hv⟩ := sys.dense p.base i
    exact ⟨liftBase p q, liftBase_le p hqp, v, hv⟩
  persistent hqp hv := sys.persistent (base_le hqp) hv
  unique hv hw := sys.unique hv hw
  ordered hij hv hw := sys.ordered hij hv hw
  adjacent hij hv hw := sys.adjacent hij hv hw

theorem lift_cross {I : Type} [LinearOrder I] {G : SimpleGraph W2}
    (sys : CliqueDecisions P I W2 G) (U : P → W2 → Prop)
    (hcross : ∀ p a, U p a → ∀ i x, sys.decides p i x → x < a ∧ G.Adj x a) :
    ∀ p a, liftPredicate U p a → ∀ i x, (liftClique sys).decides p i x →
      x < a ∧ G.Adj x a := by
  intro p a ha i x hx
  exact hcross p.base a ha i x hx

end Erdos1172Part3IteratedHechlerPreservation
