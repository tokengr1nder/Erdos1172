/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3SupportedCoverTransport
public import Erdos1172.Part3FunctionProfileEncoding

@[expose] public section

/-!
# Joint realization of two actual supported cover names

Encode the two function names on disjoint profile coordinates. A dense
choice between their actual membership predicates then gives actual
membership in one union family. The existing omegaOne realization recovers
two ground functions whose ground covers together contain every requested
point. No fixed condition deciding all the points or coordinates is used.
-/

open Cardinal Set

namespace Erdos1172Part3SupportedCoverUnion

open ErdosRadoCHAsym (W1)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3SupportedCoverRealization
open Erdos1172Part3SupportedCoverTransport
open Erdos1172Part3FunctionProfileEncoding
open Erdos1172Part3CoverProfileTools (head row decode)

variable {P X : Type} [Preorder P]

noncomputable def firstRow : W1 := Ordinal.ToType.mk ⟨0, Ordinal.omega_pos 1⟩

noncomputable def unionFamily (C D : (W1 → W1) → Set X) (f : W1 → W1) : Set X :=
  C (head (decode f)) ∪ D (row (decode f) firstRow)

theorem holds_union_left (F H : FunctionDecisions P W1 W1)
    (C D : (W1 → W1) → Set X) {p : P} {x : X}
    (hx : (coverName F C).holds p x) :
    (coverName (encodedName F (fun _ => H)) (unionFamily C D)).holds p x := by
  have hleft : (coverName (encodedName F (fun _ => H))
      (fun f => C (head (decode f)))).holds p x :=
    holds_precompose headCoordinate (fun _ _ _ _ _ hv hw =>
      (F.unique hv ((encodedName_head_decides_iff F (fun _ => H) _ _ _).mp hw)).le) hx
  exact holds_of_family_subset (fun _ _ h => Or.inl h) hleft

theorem holds_union_right (F H : FunctionDecisions P W1 W1)
    (C D : (W1 → W1) → Set X) {p : P} {x : X}
    (hx : (coverName H D).holds p x) :
    (coverName (encodedName F (fun _ => H)) (unionFamily C D)).holds p x := by
  have hright : (coverName (encodedName F (fun _ => H))
      (fun f => D (row (decode f) firstRow))).holds p x :=
    holds_precompose (rowCoordinate firstRow) (fun _ _ _ _ _ hv hw =>
      (H.unique hv ((encodedName_row_decides_iff F (fun _ => H) _ _ _ _).mp hw)).le) hx
  exact holds_of_family_subset (fun _ _ h => Or.inr h) hright

/-- Dense actual membership in either cover is jointly realizable on
every ground set of cardinality at most alephOne. Both ground functions
come from one coherent sequence of finite certificate decisions. -/
theorem exists_ground_union_of_dense_members
    (F H : FunctionDecisions P W1 W1) (C D : (W1 → W1) → Set X)
    (hclosed : CountablyClosed P) (p0 : P) (A : Set X) (hA : #A ≤ ℵ_ 1)
    (hdense : ∀ p : P, p ≤ p0 → ∀ x ∈ A, ∃ q : P, q ≤ p ∧
      ((coverName F C).holds q x ∨ (coverName H D).holds q x)) :
    ∃ f g : W1 → W1, A ⊆ C f ∪ D g := by
  let M := encodedName F (fun _ => H)
  have hactual : ∀ x ∈ A, (coverName M (unionFamily C D)).holds p0 x := by
    intro x hx
    apply (coverName M (unionFamily C D)).of_dense p0 x
    intro p hpp0
    obtain ⟨q, hqp, hq⟩ := hdense p hpp0 x hx
    refine ⟨q, hqp, ?_⟩
    rcases hq with hq | hq
    · exact holds_union_left F H C D hq
    · exact holds_union_right F H C D hq
  obtain ⟨f, hf⟩ := exists_ground_cover_of_actual_members M (unionFamily C D)
    hclosed p0 A hA hactual
  exact ⟨head (decode f), row (decode f) firstRow, hf⟩

end Erdos1172Part3SupportedCoverUnion
