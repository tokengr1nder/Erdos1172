/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3SupportedCoverRealization

@[expose] public section

/-!
# One upper decision name for a countable family of cover names

Countable closure bounds countably many function names at each fixed
coordinate. Coherent selection of these dense bounds yields one function
decision name above every member of the family. This is a new decision
name, not a ground function dominating all the original names.

Actual membership in each finitely certified cover transfers to the same
cover evaluated at the common upper name. Neither GCH nor an omegaOne
fusion condition is assumed.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedCoverBounds

open ErdosRadoCHAsym (W1)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3FunctionDecisions
open Erdos1172Part3DecisionSelection (exists_function_decisions_of_dense)
open Erdos1172Part3SupportedCoverRealization

variable {P J X : Type} [Preorder P]

/-- Every decided value of the common name strictly bounds all later
decisions of every original name at that coordinate. -/
theorem exists_common_strict_bound
    (hclosed : CountablyClosed P) (F : J → FunctionDecisions P W1 W1)
    (hJ : #J ≤ ℵ₀) :
    ∃ H : FunctionDecisions P W1 W1,
      ∀ p i bound, H.decides p i bound → ∀ j : J, BoundedAt (F j) p i bound := by
  let R (p : P) (i bound : W1) : Prop := ∀ j : J, BoundedAt (F j) p i bound
  have hpersistent : ∀ {p q i bound}, q ≤ p → R p i bound → R q i bound := by
    intro p q i bound hqp hR j
    exact boundedAt_mono (hR j) hqp
  have hdense : ∀ p i, ∃ q : P, q ≤ p ∧ ∃ bound : W1, R q i bound := by
    intro p i
    exact exists_bound_for_countable_family hclosed p F hJ i
  exact exists_function_decisions_of_dense R hpersistent hdense

/-- The common upper name dominates each member pointwise at every
condition, tested whenever the two values have been jointly decided. -/
theorem exists_pointwise_upper
    (hclosed : CountablyClosed P) (F : J → FunctionDecisions P W1 W1)
    (hJ : #J ≤ ℵ₀) :
    ∃ H : FunctionDecisions P W1 W1, ∀ j p, PointwiseBelow (F j) H p := by
  obtain ⟨H, hH⟩ := exists_common_strict_bound hclosed F hJ
  refine ⟨H, ?_⟩
  intro j p q _ i v bound hv hbound
  exact (hH q i bound hbound j q le_rfl v hv).le

end Erdos1172Part3NamedCoverBounds
