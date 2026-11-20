/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3IteratedHechlerPreservation

@[expose] public section

/-!
# Stationary uniform domination of earlier-stage function decisions

Both source membership and the functions to bound may depend on earlier
conditions. Small-name normalization and stationary refinement give one
tail bound below which stationary possible membership persists.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedStationaryTail

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3StationaryDecisions
open Erdos1172Part3FunctionDecisions
open Erdos1172Part3NiceFunctionNames
open Erdos1172Part3IteratedHechlerOrder
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)

variable {P : Type} [Preorder P]

def DominatesAfter (p : Condition P) (F : FunctionDecisions P W1 W1) (bound : W1) : Prop :=
  ∀ q : Condition P, q ≤ p → ∀ i : W1, bound < i →
    ∀ v : W1, q.stem i = some v → BoundedAt F q.base i v

theorem dominatesAfter_mono {p q : Condition P} {F : FunctionDecisions P W1 W1}
    {bound : W1} (h : DominatesAfter p F bound) (hqp : q ≤ p) :
    DominatesAfter q F bound := fun r hr i hi v hv => h r (hr.trans hqp) i hi v hv

def TailMembers (U : P → W2 → Prop) (F : W2 → FunctionDecisions P W1 W1)
    (bound : W1) (p : Condition P) (a : W2) : Prop :=
  U p.base a ∧ DominatesAfter p (F a) bound

theorem tailMembers_persistent (U : P → W2 → Prop) (hU : Persistent U)
    (F : W2 → FunctionDecisions P W1 W1) (bound : W1) :
    Persistent (TailMembers U F bound) := by
  intro p q a hqp ha
  exact ⟨hU (base_le hqp) ha.1, dominatesAfter_mono ha.2 hqp⟩

/-- The initial stem supplies a common tail cutoff before any function
is normalized. Each possible source member has an extension tracking its
own nice representative, and the new chain condition yields stationary
possibilities below every stronger condition. -/
theorem exists_stationary_uniform_tail (c : CountablyCenteredCode P) (hCH : CH)
    (p0 : Condition P) (U : P → W2 → Prop) (hU : Persistent U)
    (hs : IsStationary (possible U p0.base)) (F : W2 → FunctionDecisions P W1 W1) :
    ∃ bound : W1, ∃ p : Condition P, p ≤ p0 ∧ StationaryAt (TailMembers U F bound) p := by
  obtain ⟨bound, hb⟩ := Erdos1172Part3HechlerOrder.exists_bound_of_countable _ p0.stem_countable
  have hnone : ∀ i : W1, bound < i → p0.stem i = none := by
    intro i hi
    by_contra h
    exact (hb i h).asymm hi
  have hsub : possible U p0.base ⊆ possible (TailMembers U F bound) p0 := by
    rintro a ⟨base, hbase, ha⟩
    obtain ⟨N, hN⟩ := exists_nice_name c.omegaTwoCC (F a)
    let p := track (liftBase p0 base) N
    have hpp0 : p ≤ p0 := (track_le _ _).trans (liftBase_le p0 hbase)
    refine ⟨p, hpp0, ha, ?_⟩
    intro q hqp i hi v hv
    have hpi : p.stem i = none := hnone i hi
    have hbound := hqp.2.2.2 i hpi v hv N (Set.mem_insert _ _)
    exact (boundedAt_iff_of_refines hN q.base i v).mp hbound
  have hstat : IsStationary (possible (TailMembers U F bound) p0) := hs.mono hsub
  obtain ⟨p, hpp0, hp⟩ := exists_stationary_refinement (c.extend hCH).omegaTwoCC
    (TailMembers U F bound) (tailMembers_persistent U hU F bound) p0 hstat
  exact ⟨bound, p, hpp0, hp⟩

end Erdos1172Part3NamedStationaryTail
