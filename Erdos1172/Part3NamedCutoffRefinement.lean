/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedSquareThinning

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
    ∃ value : I, ∃ p : P, p ≤ p0 ∧
      StationaryAt (fun q a => U q a ∧ K.decides q a value) p := by
  classical
  let S := possible U p0
  have witness (a : S) : ∃ value : I, ∃ p : P,
      p ≤ p0 ∧ U p a.val ∧ K.decides p a.val value := by
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

/-- The cutoff, as well as the column-bound functions and the square,
may depend on earlier conditions. No fixed ground cutoff is required. -/
theorem exists_stationary_square_from_named_cutoffs
    (c : CountablyCenteredCode P) (hclosed : CountablyClosed P) (hCH : CH)
    (p0 : Condition P) (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (core : CliqueDecisions P Square W2 G) (U : P → W2 → Prop) (hU : Persistent U)
    (hs : IsStationary (possible U p0.base))
    (hafter : ∀ p a, U p a → ∀ z x, core.decides p z x → x < a)
    (K : FunctionDecisions P W2 W1) (F : W2 → FunctionDecisions P W1 W1)
    (hloss : ∀ p a, U p a → ∀ cutoff : W1, K.decides p a cutoff →
      ∀ i : W1, cutoff < i → ∀ j : W1, ∀ x : W2,
        core.decides p (toLex (i, j)) x → H.Adj x a →
          ∀ v : W1, (F a).decides p i v → j < v) :
    ∃ sys : StationaryCliqueDecisions (Condition P) Square G,
      sys.start ≤ p0 ∧ (∀ q a, sys.future q a → U q.base a) ∧
        ∀ q i x, sys.clique.decides q i x → ∃ z : Square, core.decides q.base z x := by
  have hsmall : #W1 < ℵ_ 2 := by
    simp only [W1, Cardinal.mk_toType, Ordinal.card_omega]
    exact Cardinal.aleph_lt_aleph.mpr (by norm_num)
  obtain ⟨cutoff, base, hbase, hb⟩ :=
    exists_stationary_small_decision_fiber hsmall c.omegaTwoCC p0.base U hU hs K
  let V : P → W2 → Prop := fun p a => U p a ∧ K.decides p a cutoff
  have hV : Persistent V := by
    intro p q a hqp ha
    exact ⟨hU hqp ha.1, K.persistent hqp ha.2⟩
  obtain ⟨sys, hsys, hfuture, hinside⟩ :=
    Erdos1172Part3NamedSquareThinning.exists_stationary_square_from_named_row_bounds
      c hclosed hCH (liftBase p0 base) G H hcompl core V hV (hb base le_rfl)
      (fun p a ha => hafter p a ha.1) cutoff F
      (fun p a ha => hloss p a ha.1 cutoff ha.2)
  exact ⟨sys, hsys.trans (liftBase_le p0 hbase), fun q a ha => (hfuture q a ha).1, hinside⟩

end Erdos1172Part3NamedCutoffRefinement
