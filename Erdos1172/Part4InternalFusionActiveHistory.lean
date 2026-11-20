/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionHistories
public import Erdos1172.Part4InternalCountableFamilyUnion
public import Erdos1172.Part4InternalCountableSuccessor
public import Erdos1172.Part4InternalSmallPoolOperations
public import Erdos1172.Part4InternalCountableSubsetCodes

@[expose] public section

/-!
# The complete active history at one ordered-fusion stage

Earlier active sets are united with the physical points chosen now from
successful earlier rows. The current block selection is not an input,
so its failure cannot discard the current points.

Internal countability follows from the countable-family union theorem
and the actual current-point graph. Pool containment follows from the
stored earlier blocks and their whole point sets, not an assumed bound
on the new physical points. No CH, normality, ideal closure, or successful
current block is required.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionActiveHistory

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosCanonicalBlocks ErdosBoundedFunctionValue
open ErdosFusionHistories ErdosCountableFamilyUnion ErdosCountableSuccessor
open ErdosSmallPoolOperations ErdosSmallFamilyUnion ErdosCountableSubsetCodes
open ErdosRelationGraph ErdosInitialSegments

private theorem insert_countable {A a : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ injects_into A bSet.omega) :
    Γ ≤ injects_into (bSet.insert1 a A) bSet.omega := by
  calc
    Γ = (Γ ⊓ a ∈ᴮ A) ⊔ (Γ ⊓ (a ∈ᴮ A)ᶜ) := by
      rw [← inf_sup_left, sup_compl_eq_top, inf_top_eq]
    _ ≤ injects_into (bSet.insert1 a A) bSet.omega := by
      apply sup_le
      · have Hsub : Γ ⊓ a ∈ᴮ A ≤ bSet.insert1 a A ⊆ᴮ A := by
          rw [subset_unfold']
          apply le_iInf
          intro x
          rw [← deduction]
          change (Γ ⊓ a ∈ᴮ A) ⊓ x ∈ᴮ (insert a A : bSet 𝔹) ≤ x ∈ᴮ A
          rw [mem_insert1, inf_sup_left]
          exact sup_le
            (mem_congr (bv_symm inf_le_right) bv_refl (inf_le_left.trans inf_le_right))
            inf_le_right
        exact injects_into_trans (injects_into_of_subset Hsub) (inf_le_left.trans HA)
      · exact insert_countable_of_fresh (inf_le_left.trans HA) inf_le_right

/-- Finite union countability, including mixed equality between the two
sets, follows without a cardinal-arithmetic or ideal hypothesis. -/
theorem binary_union_countable {A B : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ injects_into A bSet.omega) (HB : Γ ≤ injects_into B bSet.omega) :
    Γ ≤ injects_into (binary_union A B) bSet.omega := by
  have HT : Γ ≤ injects_into (bSet.insert1 A (bSet.insert1 B ∅)) bSet.omega :=
    insert_countable (insert_countable (injects_into_of_subset empty_subset))
  apply union_countable HT
  apply le_iInf
  intro C
  rw [← deduction]
  change Γ ⊓ C ∈ᴮ (insert A (insert B ∅) : bSet 𝔹) ≤ injects_into C bSet.omega
  simp only [mem_insert1, inf_sup_left]
  apply sup_le
  · exact bv_rw' (ϕ := fun X => injects_into X bSet.omega) inf_le_right
      (h_congr := B_ext_injects_into_left) (H_new := inf_le_left.trans HA)
  · apply sup_le
    · exact bv_rw' (ϕ := fun X => injects_into X bSet.omega) inf_le_right
        (h_congr := B_ext_injects_into_left) (H_new := inf_le_left.trans HB)
    · exact (bot_of_mem_empty inf_le_right).trans bot_le

def previousActive (ξ Acts : bSet 𝔹) : bSet 𝔹 :=
  bv_union (image ξ (bv_powerset omegaTwo) Acts)

def activeHistory (color : Bool) (R E ξ Blocks Z Acts : bSet 𝔹) : bSet 𝔹 :=
  binary_union (previousActive ξ Acts) (currentPoints color R E ξ Blocks Z)

theorem previousActive_subset {ξ Acts : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ previousActive ξ Acts ⊆ᴮ omegaTwo := indexed_union_subset

theorem activeHistory_subset {color : Bool} {R E ξ Blocks Z Acts : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ activeHistory color R E ξ Blocks Z Acts ⊆ᴮ omegaTwo :=
  binary_union_subset previousActive_subset currentPoints_subset

theorem previousActive_subset_activeHistory
    {color : Bool} {R E ξ Blocks Z Acts : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ previousActive ξ Acts ⊆ᴮ activeHistory color R E ξ Blocks Z Acts :=
  subset_binary_union_left

theorem currentPoints_subset_activeHistory
    {color : Bool} {R E ξ Blocks Z Acts : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ currentPoints color R E ξ Blocks Z ⊆ᴮ
      activeHistory color R E ξ Blocks Z Acts := subset_binary_union_right

theorem previousActive_countable {ξ Acts : bSet 𝔹} {Γ : 𝔹}
    (HActs : Γ ≤ is_func' ξ (bv_powerset omegaTwo) Acts)
    (Hcount : Γ ≤ injects_into ξ bSet.omega)
    (Hvalues : Γ ≤ countableValues ξ Acts) :
    Γ ≤ injects_into (previousActive ξ Acts) bSet.omega :=
  indexed_union_countable HActs Hcount Hvalues

/-- The complete current active set is countable independently of the
outcome of the current block selector. -/
theorem activeHistory_countable
    {color : Bool} {R E ξ Blocks Z Acts : bSet 𝔹} {Γ : 𝔹}
    (HActs : Γ ≤ is_func' ξ (bv_powerset omegaTwo) Acts)
    (Hvalues : Γ ≤ countableValues ξ Acts)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HZ : Γ ≤ is_function omegaOne omegaOne Z)
    (Hξ : Γ ≤ ξ ⊆ᴮ omegaOne) (Hcount : Γ ≤ injects_into ξ bSet.omega) :
    Γ ≤ injects_into (activeHistory color R E ξ Blocks Z Acts) bSet.omega :=
  binary_union_countable (previousActive_countable HActs Hcount Hvalues)
    (currentPoints_countable HE HElaw HZ Hξ Hcount)

/-- Decode the actual image graph without selecting an external row.
The witness and equality hold at the original Boolean condition. -/
theorem currentPoints_witness
    {color : Bool} {R E ξ Blocks Z x : bSet 𝔹} {Γ : 𝔹}
    (Hx : Γ ≤ x ∈ᴮ currentPoints color R E ξ Blocks Z) :
    ∃ ν : bSet 𝔹, Γ ≤ ν ∈ᴮ successfulRows color R ξ Blocks ∧
      Γ ≤ x =ᴮ currentPoint E Blocks Z ν := by
  obtain ⟨ν, Hν⟩ := exists_convert (mem_image_iff.mp Hx).2
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  have Hrel := (mem_relationGraph_iff
    (fun y => B_ext_term _ _ B_ext_bv_eq_right (currentPoint_congr E Blocks Z))
    (fun _ => B_ext_bv_eq_left)).mp (Hν.trans inf_le_right)
  exact ⟨ν, Hν.trans inf_le_left, Hrel.2.2⟩

/-- Bounds for all guarded earlier active values bound their actual
union. No functionality or nonempty history is needed for this implication. -/
theorem previousActive_subset_of_values {ξ Acts P : bSet 𝔹} {Γ : 𝔹}
    (Hvalues : Γ ≤ ⨅ ν, ⨅ A, _root_.imp
      (ν ∈ᴮ ξ ⊓ pair ν A ∈ᴮ Acts) (A ⊆ᴮ P)) :
    Γ ≤ previousActive ξ Acts ⊆ᴮ P := by
  apply union_subset_of_members_subset
  apply le_iInf
  intro A
  rw [← deduction]
  obtain ⟨ν, Hν⟩ := exists_convert ((mem_image_iff.mp
    (show Γ ⊓ A ∈ᴮ image ξ (bv_powerset omegaTwo) Acts ≤
      A ∈ᴮ image ξ (bv_powerset omegaTwo) Acts from inf_le_right)).2)
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  exact (le_inf (inf_le_left.trans (Hvalues.trans
    ((iInf_le _ ν).trans (iInf_le _ A)))) Hν).trans bv_imp_elim

/-- Current physical points are bounded by the whole earlier objects.
Their bound is derived, rather than supplied as a current-stage invariant. -/
theorem currentPoints_subset_of_pool
    {color : Bool} {R E ξ Blocks Z B P : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HBlocks : Γ ≤ is_function ξ (bv_powerset omegaTwo) Blocks)
    (HZ : Γ ≤ is_function omegaOne omegaOne Z) (Hξ : Γ ≤ ξ ⊆ᴮ omegaOne)
    (HEarlier : Γ ≤ earlierHistory color R ξ Blocks ⊆ᴮ B)
    (Hpoints : Γ ≤ bv_union B ⊆ᴮ P) :
    Γ ≤ currentPoints color R E ξ Blocks Z ⊆ᴮ P := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  let Δ := Γ ⊓ x ∈ᴮ currentPoints color R E ξ Blocks Z
  obtain ⟨ν, Hν, Hxeq⟩ := currentPoints_witness
    (show Δ ≤ x ∈ᴮ currentPoints color R E ξ Blocks Z from inf_le_right)
  have Hparts := mem_successfulRows_iff.mp Hν
  have Hspec := currentPoint_spec (inf_le_left.trans HE) (inf_le_left.trans HElaw)
    (inf_le_left.trans HZ) (mem_of_mem_subset (inf_le_left.trans Hξ) Hparts.1) Hparts.2
  have HxBlock : Δ ≤ x ∈ᴮ blockValue Blocks ν :=
    mem_congr (bv_symm Hxeq) bv_refl (Hspec.trans (inf_le_right.trans inf_le_right))
  have HAearlier : Δ ≤ blockValue Blocks ν ∈ᴮ earlierHistory color R ξ Blocks :=
    earlierHistory_mem_of_pair (inf_le_left.trans HBlocks)
      (graphValue_pair_mem (inf_le_left.trans HBlocks) Hparts.1) Hparts.2
  have HxUnion : Δ ≤ x ∈ᴮ bv_union B :=
    mem_bv_union_iff.mpr (le_iSup_of_le (blockValue Blocks ν)
      (le_inf (mem_of_mem_subset (inf_le_left.trans HEarlier) HAearlier) HxBlock))
  exact mem_of_mem_subset (inf_le_left.trans Hpoints) HxUnion

theorem activeHistory_subset_of_pool
    {color : Bool} {R E ξ Blocks Z Acts B P : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HBlocks : Γ ≤ is_function ξ (bv_powerset omegaTwo) Blocks)
    (HZ : Γ ≤ is_function omegaOne omegaOne Z) (Hξ : Γ ≤ ξ ⊆ᴮ omegaOne)
    (HEarlier : Γ ≤ earlierHistory color R ξ Blocks ⊆ᴮ B)
    (Hpoints : Γ ≤ bv_union B ⊆ᴮ P)
    (Hprevious : Γ ≤ previousActive ξ Acts ⊆ᴮ P) :
    Γ ≤ activeHistory color R E ξ Blocks Z Acts ⊆ᴮ P :=
  binary_union_subset Hprevious
    (currentPoints_subset_of_pool HE HElaw HBlocks HZ Hξ HEarlier Hpoints)

/-- A legitimate selector input, with current points retained even if
the upcoming block output is the empty failure value. -/
theorem activeHistory_mem_countableSubsets
    {color : Bool} {R E ξ Blocks Z Acts B P : bSet 𝔹} {Γ : 𝔹}
    (HActs : Γ ≤ is_func' ξ (bv_powerset omegaTwo) Acts)
    (Hvalues : Γ ≤ countableValues ξ Acts)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HBlocks : Γ ≤ is_function ξ (bv_powerset omegaTwo) Blocks)
    (HZ : Γ ≤ is_function omegaOne omegaOne Z)
    (Hξ : Γ ≤ ξ ⊆ᴮ omegaOne) (Hcount : Γ ≤ injects_into ξ bSet.omega)
    (HEarlier : Γ ≤ earlierHistory color R ξ Blocks ⊆ᴮ B)
    (Hpoints : Γ ≤ bv_union B ⊆ᴮ P)
    (Hprevious : Γ ≤ ⨅ ν, ⨅ A, _root_.imp
      (ν ∈ᴮ ξ ⊓ pair ν A ∈ᴮ Acts) (A ⊆ᴮ P)) :
    Γ ≤ activeHistory color R E ξ Blocks Z Acts ∈ᴮ countableSubsets P :=
  mem_countableSubsets_iff.mpr
    ⟨activeHistory_subset_of_pool HE HElaw HBlocks HZ Hξ HEarlier Hpoints
      (previousActive_subset_of_values Hprevious),
      activeHistory_countable HActs Hvalues HE HElaw HZ Hξ Hcount⟩

end bSet.ErdosFusionActiveHistory
