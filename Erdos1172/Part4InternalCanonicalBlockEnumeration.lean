/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFutureBlockWitness

@[expose] public section

/-!
# A single actual enumeration family for whole homogeneous block objects

Block objects are separated inside the powerset of omega-two. Every
enumeration graph has the fixed code bound `P(omegaOne × omegaTwo)`.
Bounded internal choice constructs one actual function on all block
objects. Equality of selected graphs for equal objects follows from the
functionality of that same family, not from an extensionality assumption
about arbitrary external choices of enumeration witnesses.

The construction has no CH, normal-ideal, ordinal-ranking, or successful
run hypothesis. An object is the whole actual image of its enumeration.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCanonicalBlocks

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosIncreasingPartial
open ErdosSmallFiberBound ErdosRelationGraph ErdosFutureBlockWitness

def blockEnumerationData (color : Bool) (R A f : bSet 𝔹) : 𝔹 :=
  is_injective_function omegaOne omegaTwo f ⊓
    (increasingOn omegaOne f ⊓
      (homogeneousUnion color R omegaOne omegaOne f f ⊓
        image omegaOne omegaTwo f =ᴮ A))

theorem blockEnumerationData_ext_object (color : Bool) (R f : bSet 𝔹) :
    B_ext (fun A => blockEnumerationData color R A f) :=
  B_ext_inf B_ext_const (B_ext_inf B_ext_const
    (B_ext_inf B_ext_const B_ext_bv_eq_right))

theorem blockEnumerationData_ext_graph (color : Bool) (R A : bSet 𝔹) :
    B_ext (blockEnumerationData color R A) :=
  B_ext_inf B_ext_injective_code
    (B_ext_inf (increasingOn_ext_graph omegaOne)
      (B_ext_inf (homogeneousUnion_self_ext_graph color R omegaOne)
        (B_ext_term (ϕ := fun B => B =ᴮ A) (t := image omegaOne omegaTwo)
          B_ext_bv_eq_left B_congr_image_right)))

def blockObjects (color : Bool) (R : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun A => ⨆ f, blockEnumerationData color R A f) (bv_powerset omegaTwo)

def blockEnumerationCodes : bSet 𝔹 := bv_powerset (prod omegaOne omegaTwo)

theorem mem_blockObjects_iff {color : Bool} {R A : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ A ∈ᴮ blockObjects color R ↔
      Γ ≤ A ⊆ᴮ omegaTwo ∧ Γ ≤ ⨆ f, blockEnumerationData color R A f := by
  unfold blockObjects
  rw [mem_comprehend_and
    (B_ext_iSup (h := fun f => blockEnumerationData_ext_object color R f))]
  constructor
  · rintro ⟨HA, Hdata⟩
    exact ⟨mem_powerset_iff.mp HA, Hdata⟩
  · rintro ⟨HA, Hdata⟩
    exact ⟨mem_powerset_iff.mpr HA, Hdata⟩

theorem blockObjects_subset {color : Bool} {R : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ blockObjects color R ⊆ᴮ bv_powerset omegaTwo :=
  comprehend_subset (ϕ := fun A => ⨆ f, blockEnumerationData color R A f)
    (bv_powerset omegaTwo)

theorem blockEnumerationData_mem_codes
    {color : Bool} {R A f : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ blockEnumerationData color R A f) : Γ ≤ f ∈ᴮ blockEnumerationCodes :=
  mem_powerset_iff.mpr (H.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))

theorem blockEnumerationData_mem_object
    {color : Bool} {R A f : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ blockEnumerationData color R A f) : Γ ≤ A ∈ᴮ blockObjects color R := by
  apply mem_blockObjects_iff.mpr
  exact ⟨bv_rw'' (ϕ := fun B => B ⊆ᴮ omegaTwo)
    (H.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))
    image_subset B_ext_subset_left, le_iSup_of_le f H⟩

theorem exists_block_enumeration {color : Bool} {R A : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ A ∈ᴮ blockObjects color R) :
    ∃ f : bSet 𝔹, Γ ≤ blockEnumerationData color R A f :=
  exists_convert (mem_blockObjects_iff.mp HA).2 (blockEnumerationData_ext_graph color R A)

def blockEnumerationFamilyLaw (color : Bool) (R E : bSet 𝔹) : 𝔹 :=
  ⨅ A, ⨅ f, _root_.imp (A ∈ᴮ blockObjects color R ⊓ pair A f ∈ᴮ E)
    (blockEnumerationData color R A f)

theorem blockEnumerationFamilyLaw_apply
    {color : Bool} {R E A f : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HA : Γ ≤ A ∈ᴮ blockObjects color R) (Hpair : Γ ≤ pair A f ∈ᴮ E) :
    Γ ≤ blockEnumerationData color R A f :=
  (le_inf (Hlaw.trans ((iInf_le _ A).trans (iInf_le _ f))) (le_inf HA Hpair)).trans bv_imp_elim

/-- One bounded selector covers all internal block objects at the original
Boolean condition. The internal domain may be empty; no block existence
or supplied coherent enumeration family is assumed. -/
theorem exists_block_enumeration_family (color : Bool) (R : bSet 𝔹) {Γ : 𝔹} :
    ∃ E : bSet 𝔹, Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E ⊓
      blockEnumerationFamilyLaw color R E := by
  apply exists_selector_of_pointwise (P := blockEnumerationData color R)
    (blockEnumerationData_ext_object color R) (blockEnumerationData_ext_graph color R)
  apply le_iInf
  intro A
  rw [← deduction]
  obtain ⟨f, Hf⟩ := exists_block_enumeration
    (show Γ ⊓ A ∈ᴮ blockObjects color R ≤ A ∈ᴮ blockObjects color R from inf_le_right)
  exact le_iSup_of_le f (le_inf (blockEnumerationData_mem_codes Hf) Hf)

theorem selected_enumeration_data
    {color : Bool} {R E A f : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (Hlaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (Hpair : Γ ≤ pair A f ∈ᴮ E) : Γ ≤ blockEnumerationData color R A f :=
  blockEnumerationFamilyLaw_apply Hlaw (mem_domain_of_is_function Hpair HE) Hpair

theorem exists_selected_enumeration
    {color : Bool} {R E A : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (Hlaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HA : Γ ≤ A ∈ᴮ blockObjects color R) :
    ∃ f : bSet 𝔹, Γ ≤ pair A f ∈ᴮ E ∧ Γ ≤ blockEnumerationData color R A f := by
  have Hex : Γ ≤ ⨆ f, f ∈ᴮ blockEnumerationCodes ⊓ pair A f ∈ᴮ E :=
    (le_inf ((is_total_of_is_function HE).trans (iInf_le _ A)) HA).trans bv_imp_elim
  obtain ⟨f, Hf⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  exact ⟨f, Hf.trans inf_le_right, selected_enumeration_data HE Hlaw (Hf.trans inf_le_right)⟩

/-- Coherence is a consequence of functionality of this same actual
selector. This does not assert equality for two independently chosen
enumeration families, or extensionality of external witness selection. -/
theorem selected_enumerations_equal
    {color : Bool} {R E A B f g : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HAB : Γ ≤ A =ᴮ B) (HAf : Γ ≤ pair A f ∈ᴮ E) (HBg : Γ ≤ pair B g ∈ᴮ E) :
    Γ ≤ f =ᴮ g :=
  eq_of_is_function_of_eq HE HAB HAf HBg

end bSet.ErdosCanonicalBlocks
