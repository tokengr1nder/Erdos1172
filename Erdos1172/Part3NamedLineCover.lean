/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3SupportedCoverRealization
public import Erdos1172.Part3CofinalLineCover

@[expose] public section

/-!
# Lifting the canonical line cover to an actual function name

An ordered omegaOne enumeration which densely covers a regular source,
and whose range is cofinal, gives dense bounds on every fixed line row.
Choose one enumerated value beyond the row cut and decide all its
countably many predecessors. Every later actual source point in that row
must equal one of these fixed values.

Coherent selection from these dense row bounds gives a function name.
Each actual source point then has a singleton coordinate certificate for
the original canonical line cover. Cofinality in the displayed ambient
order is an explicit hypothesis; a bounded omegaOne subset does not meet it.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3NamedLineCover

open ErdosRadoCHAsym (W1)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName)
open Erdos1172Part3CofinalLineCover (LineCoverData)
open Erdos1172Part3SupportedCoverRealization (coverName)
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)

variable {P V : Type} [Preorder P] [LinearOrder V] [WellFoundedLT V]

/-- A bound valid for every actual row member at every refinement. -/
def RowBound (data : LineCoverData V) (U : RegularName P V)
    (p : P) (i bound : W1) : Prop :=
  ∀ q : P, q ≤ p → ∀ x : V, U.holds q x → data.row x = i → data.code x < bound

theorem rowBound_persistent {data : LineCoverData V} {U : RegularName P V}
    {p q : P} {i bound : W1} (hqp : q ≤ p) (h : RowBound data U p i bound) :
    RowBound data U q i bound :=
  fun r hrq x hx hi => h r (hrq.trans hqp) x hx hi

/-- Dense row bounds alone suffice for coherent function-name selection.
The source of those bounds is kept as an explicit premise here. -/
theorem exists_named_line_cover_of_dense_row_bounds
    (data : LineCoverData V) (U : RegularName P V)
    (hbound : ∀ p : P, ∀ i : W1,
      ∃ q : P, q ≤ p ∧ ∃ bound : W1, RowBound data U q i bound) :
    ∃ F : FunctionDecisions P W1 W1,
      ∀ p : P, ∀ x : V, U.holds p x → (coverName F data.cover).holds p x := by
  classical
  obtain ⟨F, hF⟩ := Erdos1172Part3DecisionSelection.exists_function_decisions_of_dense
    (RowBound data U)
    (fun {_ _ _ _} hqp h => rowBound_persistent hqp h)
    hbound
  refine ⟨F, ?_⟩
  intro p x hx q hqp
  obtain ⟨r, hrq, bound, hdec⟩ := F.dense q (data.row x)
  have hcode : data.code x < bound := hF r (data.row x) bound hdec r le_rfl x
    (U.persistent (hrq.trans hqp) hx) rfl
  refine ⟨r, hrq, (fun _ : W1 => bound), {data.row x}, ?_, ?_⟩
  · intro i hi
    have heq : i = data.row x := Finset.mem_singleton.mp hi
    subst i
    exact hdec
  · intro g hg
    exact Or.inr (hcode.trans_le (hg (data.row x) (Finset.mem_singleton_self _)))

end Erdos1172Part3NamedLineCover
