/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedCliqueThinning

@[expose] public section

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedCutoffRefinement

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3StationaryDecisions
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3IteratedHechlerOrder (Condition liftBase liftBase_le)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3NamedCliqueThinning (StationaryCliqueDecisions)
open Erdos1172Part3StationarySquareDecisions (Square)

variable {P : Type} [Preorder P]

/-- A small-valued decision on stationary possible members has a fixed
value with stationary possibilities below one stronger condition. -/
theorem exists_stationary_small_decision_fiber {I : Type} (hI : #I < ℵ_ 2)
    (hcc : OmegaTwoCC P) (p0 : P) (U : P → W2 → Prop) (hU : Persistent U)
    (hs : IsStationary (possible U p0)) (K : FunctionDecisions P W2 I) :
    ∃ value : I, ∃ p : P, p ≤ p0 ∧ StationaryAt (fun q a => U q a ∧ K.decides q a value) p := by
  classical
  let S := possible U p0
  have witness (a : S) : ∃ value : I, ∃ p : P, p ≤ p0 ∧ U p a.val ∧ K.decides p a.val value := by
    obtain ⟨q, hqp, hqa⟩ := a.property
    obtain ⟨p, hpq, value, hvalue⟩ := K.dense q a.val
    exact ⟨value, p, hpq.trans hqp, hU hpq hqa, hvalue⟩
  let chosen (a : S) : I := (witness a).choose
  obtain ⟨value, hfiber⟩ :=
    Erdos1172Part3CenteredStationaryLoss.exists_stationary_fiber_of_small hI hs chosen
  let V : P → W2 → Prop := fun p a => U p a ∧ K.decides p a value
  have hV : Persistent V := by
    intro p q a hqp ha
    exact ⟨hU hqp ha.1, K.persistent hqp ha.2⟩
  have hstat : IsStationary (possible V p0) := by
    apply hfiber.mono
    rintro a ⟨ha, heq⟩
    obtain ⟨p, hpp0, hpa, hpvalue⟩ := (witness ⟨a, ha⟩).choose_spec
    refine ⟨p, hpp0, hpa, ?_⟩
    change chosen ⟨a, ha⟩ = value at heq
    rwa [← heq]
  obtain ⟨p, hpp0, hp⟩ := exists_stationary_refinement hcc V hV p0 hstat
  exact ⟨value, p, hpp0, hp⟩

end Erdos1172Part3NamedCutoffRefinement
