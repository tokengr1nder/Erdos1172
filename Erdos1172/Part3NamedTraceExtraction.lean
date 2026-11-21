/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedTraceIdeal

@[expose] public section

/-!
# Clique extraction from positive traces

Failure of dense boundedness gives a cone with unbounded possible indices
below every strengthening. Countable extension then constructs a clique
whose points satisfy the named trace at the deciding condition. Ground
extraction retains an original-core decision for every selected vertex.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedTraceExtraction

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3NamedTraceIdeal
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3CountableDecisionFusion (CountableExtension)
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)

variable {P : Type} [Preorder P] {G : SimpleGraph W2}

theorem exists_unbounded_trace_cone (core : CliqueDecisions P W1 W2 G)
    (p0 : P) (U : RegularName P W2) (hU : ¬(traceName core).holds p0 U) :
    ∃ q : P, q ≤ p0 ∧ ∀ p : P, p ≤ q → ∀ bound : W1,
      ∃ s : P, s ≤ p ∧ ∃ i : W1, bound < i ∧ ∃ x : W2, core.decides s i x ∧ U.holds s x := by
  classical
  change ¬∀ q : P, q ≤ p0 → ∃ s : P, s ≤ q ∧ ∃ bound, TailAvoid core s U bound at hU
  push Not at hU
  obtain ⟨q, hqp0, hq⟩ := hU
  refine ⟨q, hqp0, ?_⟩
  intro p hpq bound
  have h := hq p hpq bound
  unfold TailAvoid at h
  push Not at h
  exact h

end Erdos1172Part3NamedTraceExtraction
