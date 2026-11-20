/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3ProductTraceIdeal

@[expose] public section

/-!
# Extracting a whole cube while preserving its small traces

Outer fusion chooses increasing old square rows. Each positive old row
supplies a square subsequence together with its trace-transfer theorem.
The chosen old row is fixed by a single outer decision. This retained
row-local law is stronger than coordinatewise vertex provenance alone.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3CubeTraceSubsequence

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularConeRestriction (onCone)
open Erdos1172Part3NamedTraceIdeal (traceName)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)

variable {P : Type} [Preorder P] {G : SimpleGraph W2}

theorem line_trace_to_cone (p0 : P) (core : CliqueDecisions P W1 W2 G)
    (sub : CliqueDecisions (Set.Iic p0) W1 W2 G) (p : Set.Iic p0) (U : RegularName P W2)
    (hdec : ∀ q : Set.Iic p0, q ≤ p → ∀ i x, sub.decides q i x → core.decides q.val i x)
    (hsmall : (traceName core).holds p.val U) : (traceName sub).holds p (onCone p0 U) := by
  intro q hqp
  obtain ⟨s, hsq, bound, hs⟩ := hsmall q.val hqp
  refine ⟨⟨s, hsq.trans q.property⟩, hsq, bound, ?_⟩
  intro t hts i hi x hx hUx
  exact hs t.val hts i hi x (hdec t ((hts.trans hsq).trans hqp) i x hx) hUx

end Erdos1172Part3CubeTraceSubsequence
