/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedLineCover
public import Erdos1172.Part3CoverProfileTools
public import Erdos1172.Part3DecisionSelection

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

def rowPrefix (rowOf : J → W1) (i : W1) : Set J := {a | rowOf a ≤ i}

/-- A countable family at every row has countable bounded row prefixes. -/
theorem sigma_prefix_countable (Fiber : W1 → Type) (hFiber : ∀ i, #(Fiber i) ≤ ℵ₀)
    (j : W1) :
    #(rowPrefix (fun a : (Σ i : W1, Fiber i) => a.1) j) ≤ ℵ₀ := by
  have hrows : (Set.Iic j).Countable := Cardinal.le_aleph0_iff_set_countable.mp
    (Cardinal.lt_aleph_one_iff.mp (Erdos1172Part3ConvergentCore.mk_Iic_W1_lt j))
  have hfiber (i : W1) :
      (Set.range (fun a : Fiber i => (⟨i, a⟩ : Σ k : W1, Fiber k))).Countable :=
    Cardinal.le_aleph0_iff_set_countable.mp (Cardinal.mk_range_le.trans (hFiber i))
  apply Cardinal.le_aleph0_iff_set_countable.mpr
  apply (hrows.biUnion (fun i _ => hfiber i)).mono
  intro a ha
  exact Set.mem_iUnion.mpr ⟨a.1, Set.mem_iUnion.mpr ⟨ha, ⟨a.2, rfl⟩⟩⟩

def endpointName (D : FunctionDecisions P J V) : RegularName P V :=
  regularize (fun p y => ∃ a : J, D.decides p a y)

theorem endpoint_holds_of_decision (D : FunctionDecisions P J V)
    {p : P} {a : J} {y : V} (hy : D.decides p a y) : (endpointName D).holds p y :=
  fun q hqp => ⟨q, le_rfl, a, D.persistent hqp hy⟩

/-- Endpoint rows are themselves decided countable sets; their contents
need not share a fixed index family across different conditions. -/
def setEndpointName (B : FunctionDecisions P W1 (Set V)) : RegularName P V :=
  regularize (fun p y => ∃ i : W1, ∃ S : Set V, B.decides p i S ∧ y ∈ S)

theorem setEndpoint_holds_of_decision (B : FunctionDecisions P W1 (Set V))
    {p : P} {i : W1} {S : Set V} {y : V} (hS : B.decides p i S) (hy : y ∈ S) :
    (setEndpointName B).holds p y :=
  fun q hqp => ⟨q, le_rfl, i, S, B.persistent hqp hS, hy⟩

variable [LinearOrder V] [WellFoundedLT V]

omit [WellFoundedLT V] in
theorem row_support_of_witness (data : LineCoverData V) (D : FunctionDecisions P J V)
    (rowOf : J → W1)
    (hwitness : ∀ p : P, ∀ a : J, ∀ y : V, D.decides p a y →
      ∃ x : V, data.row x = rowOf a ∧ x ≤ y) :
    ∀ p : P, ∀ a : J, ∀ y : V, D.decides p a y → rowOf a ≤ data.row y := by
  intro p a y hy
  obtain ⟨x, hxrow, hxy⟩ := hwitness p a y hy
  exact hxrow ▸ data.row_mono hxy

/-- The entire relevant index prefix is countable, so one strengthening
fixes its values and bounds every later actual endpoint in the chosen row. -/
theorem exists_endpoint_row_bound (data : LineCoverData V) (D : FunctionDecisions P J V)
    (rowOf : J → W1) (hprefix : ∀ i : W1, #(rowPrefix rowOf i) ≤ ℵ₀)
    (hsupport : ∀ p : P, ∀ a : J, ∀ y : V, D.decides p a y → rowOf a ≤ data.row y)
    (hclosed : CountablyClosed P) (p : P) (i : W1) :
    ∃ q : P, q ≤ p ∧ ∃ bound : W1, RowBound data (endpointName D) q i bound := by
  classical
  let restricted : FunctionDecisions P (rowPrefix rowOf i) V :=
    Erdos1172Part3DecisionSelection.reindex D Subtype.val
  obtain ⟨q, hqp, hvalues⟩ := restricted.exists_simultaneous hclosed p (hprefix i)
  let chosen (a : rowPrefix rowOf i) : V := (hvalues a).choose
  have hchosen (a : rowPrefix rowOf i) : D.decides q a.val (chosen a) :=
    (hvalues a).choose_spec
  have hcodes : (Set.range (fun a : rowPrefix rowOf i => data.code (chosen a))).Countable :=
    Cardinal.le_aleph0_iff_set_countable.mp (Cardinal.mk_range_le.trans (hprefix i))
  obtain ⟨bound, hbound⟩ := exists_bound_of_countable
    (Set.range (fun a : rowPrefix rowOf i => data.code (chosen a))) hcodes
  refine ⟨q, hqp, bound, ?_⟩
  intro r hrq y hy hyrow
  obtain ⟨s, hsr, a, ha⟩ := hy r le_rfl
  have hain : a ∈ rowPrefix rowOf i := by
    change rowOf a ≤ i
    simpa only [hyrow] using hsupport s a y ha
  let index : rowPrefix rowOf i := ⟨a, hain⟩
  have heq : y = chosen index :=
    D.unique ha (D.persistent (hsr.trans hrq) (hchosen index))
  rw [heq]
  exact hbound _ ⟨index, rfl⟩

/-- Dense bounds on the actual endpoint name give a genuine head name
for the canonical line cover, without a ground endpoint-map assumption. -/
theorem exists_named_endpoint_head_of_row_support
    (data : LineCoverData V) (D : FunctionDecisions P J V) (rowOf : J → W1)
    (hprefix : ∀ i : W1, #(rowPrefix rowOf i) ≤ ℵ₀)
    (hsupport : ∀ p : P, ∀ a : J, ∀ y : V, D.decides p a y → rowOf a ≤ data.row y)
    (hclosed : CountablyClosed P) :
    ∃ F : FunctionDecisions P W1 W1,
      ∀ p : P, ∀ y : V, (endpointName D).holds p y → (coverName F data.cover).holds p y :=
  exists_named_line_cover_of_dense_row_bounds data (endpointName D)
    (exists_endpoint_row_bound data D rowOf hprefix hsupport hclosed)

theorem exists_named_endpoint_head
    (data : LineCoverData V) (D : FunctionDecisions P J V) (rowOf : J → W1)
    (hprefix : ∀ i : W1, #(rowPrefix rowOf i) ≤ ℵ₀)
    (hwitness : ∀ p : P, ∀ a : J, ∀ y : V, D.decides p a y →
      ∃ x : V, data.row x = rowOf a ∧ x ≤ y)
    (hclosed : CountablyClosed P) :
    ∃ F : FunctionDecisions P W1 W1,
      ∀ p : P, ∀ y : V, (endpointName D).holds p y → (coverName F data.cover).holds p y :=
  exists_named_endpoint_head_of_row_support data D rowOf hprefix
    (row_support_of_witness data D rowOf hwitness) hclosed

/-- Specialization to countably many endpoint indices at every source row. -/
theorem exists_named_sigma_endpoint_head
    (data : LineCoverData V) (Fiber : W1 → Type) (hFiber : ∀ i, #(Fiber i) ≤ ℵ₀)
    (D : FunctionDecisions P (Σ i : W1, Fiber i) V)
    (hwitness : ∀ p : P, ∀ a : (Σ i : W1, Fiber i), ∀ y : V, D.decides p a y →
      ∃ x : V, data.row x = a.1 ∧ x ≤ y)
    (hclosed : CountablyClosed P) :
    ∃ F : FunctionDecisions P W1 W1,
      ∀ p : P, ∀ y : V, (endpointName D).holds p y → (coverName F data.cover).holds p y :=
  exists_named_endpoint_head data D (fun a => a.1) (sigma_prefix_countable Fiber hFiber)
    hwitness hclosed

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
  have hchosen (i : Set.Iic j) : B.decides q i.val (chosen i) :=
    (hvalues i).choose_spec
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
  have hSeq : S = chosen index :=
    B.unique hS (B.persistent (hsr.trans hrq) (hchosen index))
  have hymem : y ∈ ⋃ i : Set.Iic j, chosen i :=
    Set.mem_iUnion.mpr ⟨index, hSeq ▸ hyS⟩
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
