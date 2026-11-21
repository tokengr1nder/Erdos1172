/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedLineCover
public import Erdos1172.Part3CoverProfileTools

@[expose] public section

/-!
# Actual named endpoint supports have dense line-row bounds

Endpoint indices carry source-row labels with countable bounded prefixes.
A row witness below each decided endpoint forces that endpoint's index
into the corresponding prefix. Decide this countable prefix at one
condition. Uniqueness then identifies every later actual endpoint-row
member with one of those fixed values, giving an actual persistent row
bound. The dense row bounds construct one head function name through the
canonical line-cover family.

No assertion is made about a ground union of all possible members. A
certificate is obtained below the condition of each actual member, and
all comparisons use decisions at one common strengthening.

The set-valued variant permits the countable endpoint family of each row
to vary with the condition. One set-valued name per row replaces a
globally fixed indexing of all local antichain branches.
-/

open Cardinal Set Order

namespace Erdos1172Part3NamedEndpointSupport

open ErdosRadoCHAsym (W1)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName regularize)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3CofinalLineCover (LineCoverData)
open Erdos1172Part3NamedLineCover (RowBound exists_named_line_cover_of_dense_row_bounds)
open Erdos1172Part3SupportedCoverRealization (coverName)
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)

variable {P J V : Type} [Preorder P]

/-- Endpoint rows are themselves decided countable sets; their contents
need not share a fixed index family across different conditions. -/
def setEndpointName (B : FunctionDecisions P W1 (Set V)) : RegularName P V :=
  regularize (fun p y => ∃ i : W1, ∃ S : Set V, B.decides p i S ∧ y ∈ S)

theorem setEndpoint_holds_of_decision (B : FunctionDecisions P W1 (Set V))
    {p : P} {i : W1} {S : Set V} {y : V} (hS : B.decides p i S) (hy : y ∈ S) :
    (setEndpointName B).holds p y :=
  fun q hqp => ⟨q, le_rfl, i, S, B.persistent hqp hS, hy⟩

variable [LinearOrder V] [WellFoundedLT V]

/-- Freeze the countably many set-valued row decisions below a fixed row.
The chosen sets may vary between incompatible conditions; only the sets
decided together at the selected strengthening are united here. -/
theorem exists_set_endpoint_row_bound
    (data : LineCoverData V) (B : FunctionDecisions P W1 (Set V))
    (hsets : ∀ p : P, ∀ i : W1, ∀ S : Set V, B.decides p i S →
      S.Countable ∧ ∀ y ∈ S, ∃ x : V, data.row x = i ∧ x ≤ y)
    (hclosed : CountablyClosed P) (p : P) (j : W1) :
    ∃ q : P, q ≤ p ∧ ∃ bound : W1, RowBound data (setEndpointName B) q j bound := by
  classical
  have hprefix : #(Set.Iic j) ≤ ℵ₀ := Cardinal.lt_aleph_one_iff.mp
    (Erdos1172Part3ConvergentCore.mk_Iic_W1_lt j)
  letI : Countable (Set.Iic j) := Cardinal.mk_le_aleph0_iff.mp hprefix
  let restricted : FunctionDecisions P (Set.Iic j) (Set V) :=
    Erdos1172Part3DecisionSelection.reindex B Subtype.val
  obtain ⟨q, hqp, hvalues⟩ := restricted.exists_simultaneous hclosed p hprefix
  let chosen (i : Set.Iic j) : Set V := (hvalues i).choose
  have hchosen (i : Set.Iic j) : B.decides q i.val (chosen i) := (hvalues i).choose_spec
  have hchosenCount (i : Set.Iic j) : (chosen i).Countable :=
    (hsets q i.val (chosen i) (hchosen i)).1
  have hunion : (⋃ i : Set.Iic j, chosen i).Countable := Set.countable_iUnion hchosenCount
  have hcodes : (data.code '' (⋃ i : Set.Iic j, chosen i)).Countable := hunion.image data.code
  obtain ⟨bound, hbound⟩ :=
    exists_bound_of_countable (data.code '' (⋃ i : Set.Iic j, chosen i)) hcodes
  refine ⟨q, hqp, bound, ?_⟩
  intro r hrq y hy hyrow
  obtain ⟨s, hsr, i, S, hS, hyS⟩ := hy r le_rfl
  obtain ⟨x, hxrow, hxy⟩ := (hsets s i S hS).2 y hyS
  have hij : i ≤ j := by
    have hi : i ≤ data.row y := hxrow ▸ data.row_mono hxy
    simpa only [hyrow] using hi
  let index : Set.Iic j := ⟨i, hij⟩
  have hSeq : S = chosen index := B.unique hS (B.persistent (hsr.trans hrq) (hchosen index))
  have hymem : y ∈ ⋃ i : Set.Iic j, chosen i := Set.mem_iUnion.mpr ⟨index, hSeq ▸ hyS⟩
  exact hbound (data.code y) ⟨y, hymem, rfl⟩

/-- A head name covers the actual endpoint support of condition-dependent
countable row sets. No globally fixed countable row-piece indices are used. -/
theorem exists_named_set_endpoint_head
    (data : LineCoverData V) (B : FunctionDecisions P W1 (Set V))
    (hsets : ∀ p : P, ∀ i : W1, ∀ S : Set V, B.decides p i S →
      S.Countable ∧ ∀ y ∈ S, ∃ x : V, data.row x = i ∧ x ≤ y)
    (hclosed : CountablyClosed P) :
    ∃ F : FunctionDecisions P W1 W1,
      ∀ p : P, ∀ y : V, (setEndpointName B).holds p y → (coverName F data.cover).holds p y :=
  exists_named_line_cover_of_dense_row_bounds data (setEndpointName B)
    (exists_set_endpoint_row_bound data B hsets hclosed)

end Erdos1172Part3NamedEndpointSupport
