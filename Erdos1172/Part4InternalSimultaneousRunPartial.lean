/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSimultaneousVertexHistory
public import Erdos1172.Part4InternalSimultaneousCoordinateHistory
public import Erdos1172.Part4InternalSimultaneousEntryCongruence
public import Erdos1172.Part4InternalPrefixFunction

@[expose] public section

/-!
# The actual family of lawful simultaneous prefixes

One prefix graph stores complete entries. Its two fixed-support decoders
are read only through the strict-past guards in the entry law. The graph
need not be injective, so a stopped branch can repeat its endpoint.
The set of lawful prefixes is separated from a fixed powerset family.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousRun

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosRelationGraph ErdosPartialInjection ErdosPrefixFunction
open ErdosSimultaneousEntry ErdosSimultaneousHistory

def runLaw (color : Bool) (R S top P : bSet 𝔹) : 𝔹 :=
  ⨅ i, ⨅ y, ⨅ Z, _root_.imp (pair i (pair y Z) ∈ᴮ P)
    (entryValid color i R S (vertexHistory P) (coordinateHistory P) top y Z)

def runPartial (color : Bool) (R S top P : bSet 𝔹) : 𝔹 :=
  prefixGraph omegaOne entrySpace P ⊓ runLaw color R S top P

theorem runLaw_apply {color : Bool} {R S top P i y Z : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R S top P) (Hpair : Γ ≤ pair i (pair y Z) ∈ᴮ P) :
    Γ ≤ entryValid color i R S (vertexHistory P) (coordinateHistory P) top y Z :=
  (le_inf (Hlaw.trans ((iInf_le _ i).trans ((iInf_le _ y).trans (iInf_le _ Z)))) Hpair).trans
    bv_imp_elim

theorem decodedEntry_ext_graph (color : Bool) (i R S top y Z : bSet 𝔹) :
    B_ext (fun P => entryValid color i R S (vertexHistory P) (coordinateHistory P) top y Z) := by
  intro P Q
  let Γ := P =ᴮ Q ⊓ entryValid color i R S (vertexHistory P) (coordinateHistory P) top y Z
  have HY : Γ ≤ vertexHistory P =ᴮ vertexHistory Q := vertexHistory_congr inf_le_left
  have HX : Γ ≤ coordinateHistory P =ᴮ coordinateHistory Q :=
    coordinateHistory_congr_graph inf_le_left
  have Hmid : Γ ≤ entryValid color i R S (vertexHistory Q) (coordinateHistory P) top y Z :=
    bv_rw'' (ϕ := fun Y => entryValid color i R S Y (coordinateHistory P) top y Z)
      HY inf_le_right (entryValid_ext_vertices color i R S (coordinateHistory P) top y Z)
  exact bv_rw'' (ϕ := fun X => entryValid color i R S (vertexHistory Q) X top y Z)
    HX Hmid (entryValid_ext_history color i R S (vertexHistory Q) top y Z)

theorem runLaw_ext_graph (color : Bool) (R S top : bSet 𝔹) :
    B_ext (runLaw color R S top) :=
  B_ext_iInf (h := fun i => B_ext_iInf (h := fun y => B_ext_iInf (h := fun Z =>
    B_ext_imp (h₁ := B_ext_mem_right) (h₂ := decodedEntry_ext_graph color i R S top y Z))))

theorem runPartial_ext_graph (color : Bool) (R S top : bSet 𝔹) :
    B_ext (runPartial color R S top) :=
  B_ext_inf (prefixGraph_ext_graph omegaOne entrySpace) (runLaw_ext_graph color R S top)

def runMaps (color : Bool) (R S top : bSet 𝔹) : bSet 𝔹 :=
  comprehend (runLaw color R S top) (prefixMaps omegaOne entrySpace)

theorem mem_runMaps_iff {color : Bool} {R S top P : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ P ∈ᴮ runMaps color R S top ↔ Γ ≤ runPartial color R S top P := by
  unfold runMaps
  rw [mem_comprehend_and (runLaw_ext_graph color R S top)]
  constructor
  · rintro ⟨Hp, Hlaw⟩
    exact le_inf (mem_prefixMaps_iff.mp Hp) Hlaw
  · intro H
    exact ⟨mem_prefixMaps_iff.mpr (H.trans inf_le_left), H.trans inf_le_right⟩

theorem mem_runMaps (color : Bool) (R S top P : bSet 𝔹) :
    P ∈ᴮ runMaps color R S top = runPartial color R S top P :=
  le_antisymm (mem_runMaps_iff.mp le_rfl) (mem_runMaps_iff.mpr le_rfl)

theorem runLaw_rowFunctions {color : Bool} {R S top P : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R S top P) : Γ ≤ rowFunctions P := by
  apply le_iInf
  intro i
  apply le_iInf
  intro y
  apply le_iInf
  intro Z
  rw [← deduction]
  exact (runLaw_apply (inf_le_left.trans Hlaw) inf_le_right).trans inf_le_left

theorem runPartial_function {color : Bool} {R S top P : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ runPartial color R S top P) :
    Γ ≤ is_function (graphDomain omegaOne entrySpace P) entrySpace P :=
  prefixGraph_function (H.trans inf_le_left)

theorem runPartial_rowFunctions {color : Bool} {R S top P : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ runPartial color R S top P) : Γ ≤ rowFunctions P :=
  runLaw_rowFunctions (H.trans inf_le_right)

theorem runPartial_stage_bound {color : Bool} {R S top P i y Z : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ runPartial color R S top P) (Hpair : Γ ≤ pair i (pair y Z) ∈ᴮ P) :
    Γ ≤ i ∈ᴮ omegaOne :=
  (mem_prod_iff.mp (mem_of_mem_subset (H.trans (inf_le_left.trans inf_le_left)) Hpair)).1

theorem runPartial_vertex_prefix {color : Bool} {R S top P i y Z : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ runPartial color R S top P) (Hpair : Γ ≤ pair i (pair y Z) ∈ᴮ P) :
    Γ ≤ is_func' i omegaTwo (vertexHistory P) :=
  vertexHistory_is_func'
    (subset_of_mem_Ord (runPartial_stage_bound H Hpair) omegaOne_Ord)
    (prefixGraph_is_func'_prefix (H.trans inf_le_left) Hpair)

theorem runPartial_coordinate_prefix {color : Bool} {R S top P i y Z : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ runPartial color R S top P) (Hpair : Γ ≤ pair i (pair y Z) ∈ᴮ P) :
    Γ ≤ is_func' (prod i omegaOne) omegaOne (coordinateHistory P) :=
  coordinateHistory_is_func'_prefix
    (subset_of_mem_Ord (runPartial_stage_bound H Hpair) omegaOne_Ord)
    (prefixGraph_is_func'_prefix (H.trans inf_le_left) Hpair) (runPartial_rowFunctions H)

theorem empty_runLaw {color : Bool} {R S top : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ runLaw color R S top (∅ : bSet 𝔹) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro y
  apply le_iInf
  intro Z
  rw [← deduction]
  exact (bot_of_mem_empty inf_le_right).trans bot_le

theorem empty_runPartial {color : Bool} {R S top : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ runPartial color R S top (∅ : bSet 𝔹) :=
  le_inf empty_prefixGraph empty_runLaw

theorem runMaps_nonempty {color : Bool} {R S top : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ (runMaps color R S top =ᴮ ∅)ᶜ :=
  nonempty_of_exists_mem _ (le_iSup_of_le (∅ : bSet 𝔹)
    (mem_runMaps_iff.mpr empty_runPartial))

/-- Old entries keep their exact law in any functional extension whose
stored rows remain actual functions. No prefix or success law is required
of the larger graph to establish this transfer. -/
theorem runEntry_of_extension {color : Bool} {R S top P Q i y Z : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ P ⊆ᴮ Q) (HfuncQ : Γ ≤ is_func Q) (HrowsQ : Γ ≤ rowFunctions Q)
    (HP : Γ ≤ runPartial color R S top P) (Hpair : Γ ≤ pair i (pair y Z) ∈ᴮ P) :
    Γ ≤ entryValid color i R S (vertexHistory Q) (coordinateHistory Q) top y Z :=
  entryValid_of_history_extension (vertexHistory_mono Hsub) (coordinateHistory_mono Hsub)
    (vertexHistory_is_func HfuncQ) (coordinateHistory_is_func HfuncQ HrowsQ)
    (runPartial_vertex_prefix HP Hpair) (runPartial_coordinate_prefix HP Hpair)
    (subset_of_mem_Ord (runPartial_stage_bound HP Hpair) omegaOne_Ord)
    (runLaw_apply (HP.trans inf_le_right) Hpair)

end bSet.ErdosSimultaneousRun
