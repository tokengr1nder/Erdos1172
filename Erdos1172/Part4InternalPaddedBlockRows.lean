/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCanonicalBlockEnumeration
public import Erdos1172.Part4InternalBoundedFallbackChoice

@[expose] public section

/-!
# Padding an actual family of earlier whole blocks

An actual injection assigns each earlier block object an omega-one
coordinate. The fixed enumeration family supplies its original selected
row there; an already valid seed row fills coordinates with no candidate.
Injectivity of the coordinate assignment and functionality of the same
enumeration family make every existing candidate unique, so bounded
fallback choice retains each earlier selected graph exactly.

Empty and Boolean-mixed earlier families are allowed. No reservoir,
compatible extension, or fusion history is constructed or assumed here.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosPaddedBlockRows

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosIncreasingPartial ErdosCanonicalBlocks
open ErdosSmallFiberBound ErdosBoundedFallbackChoice

def rowCandidate (Earlier h E σ r : bSet 𝔹) : 𝔹 :=
  ⨆ A, A ∈ᴮ Earlier ⊓ (pair A σ ∈ᴮ h ⊓ pair A r ∈ᴮ E)

theorem rowCandidate_ext_index (Earlier h E r : bSet 𝔹) :
    B_ext (fun σ => rowCandidate Earlier h E σ r) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_const
    (B_ext_inf B_ext_pair_mem_right B_ext_const))

theorem rowCandidate_ext_row (Earlier h E σ : bSet 𝔹) :
    B_ext (rowCandidate Earlier h E σ) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_const
    (B_ext_inf B_ext_const B_ext_pair_mem_right))

theorem rowCandidate_witness {Earlier h E σ r : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ rowCandidate Earlier h E σ r) :
    ∃ A : bSet 𝔹, Γ ≤ A ∈ᴮ Earlier ⊓ (pair A σ ∈ᴮ h ⊓ pair A r ∈ᴮ E) :=
  exists_convert H (B_ext_inf B_ext_mem_left (B_ext_inf B_ext_pair_mem_left B_ext_pair_mem_left))

theorem rowCandidate_unique {color : Bool} {R Earlier h E σ r s : bSet 𝔹} {Γ : 𝔹}
    (Hh : Γ ≤ is_inj h)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (Hr : Γ ≤ rowCandidate Earlier h E σ r)
    (Hs : Γ ≤ rowCandidate Earlier h E σ s) : Γ ≤ r =ᴮ s := by
  obtain ⟨A, HA⟩ := rowCandidate_witness Hr
  obtain ⟨B, HB⟩ := rowCandidate_witness Hs
  have HAB : Γ ≤ A =ᴮ B := eq_of_is_inj_of_eq Hh bv_refl
    (HA.trans (inf_le_right.trans inf_le_left)) (HB.trans (inf_le_right.trans inf_le_left))
  exact selected_enumerations_equal HE HAB
    (HA.trans (inf_le_right.trans inf_le_right)) (HB.trans (inf_le_right.trans inf_le_right))

def rowProperties (color : Bool) (R r : bSet 𝔹) : 𝔹 :=
  is_injective_function omegaOne omegaTwo r ⊓
    (increasingOn omegaOne r ⊓ homogeneousUnion color R omegaOne omegaOne r r)

theorem rowProperties_ext_graph (color : Bool) (R : bSet 𝔹) :
    B_ext (rowProperties color R) :=
  B_ext_inf B_ext_injective_code (B_ext_inf (increasingOn_ext_graph omegaOne)
    (ErdosFutureBlockWitness.homogeneousUnion_self_ext_graph color R omegaOne))

theorem rowProperties_of_blockEnumerationData
    {color : Bool} {R A r : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ blockEnumerationData color R A r) : Γ ≤ rowProperties color R r :=
  le_inf (H.trans inf_le_left) (le_inf (H.trans (inf_le_right.trans inf_le_left))
    (H.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))))

theorem rowCandidate_rowProperties
    {color : Bool} {R Earlier h E σ r : bSet 𝔹} {Γ : 𝔹}
    (HEarlier : Γ ≤ Earlier ⊆ᴮ blockObjects color R)
    (Hlaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (Hcandidate : Γ ≤ rowCandidate Earlier h E σ r) : Γ ≤ rowProperties color R r := by
  obtain ⟨A, HA⟩ := rowCandidate_witness Hcandidate
  exact rowProperties_of_blockEnumerationData (blockEnumerationFamilyLaw_apply Hlaw
    (mem_of_mem_subset HEarlier (HA.trans inf_le_left))
    (HA.trans (inf_le_right.trans inf_le_right)))

def paddedRowValidity (color : Bool) (R Rows : bSet 𝔹) : 𝔹 :=
  ⨅ σ, ⨅ r, _root_.imp (σ ∈ᴮ omegaOne ⊓ pair σ r ∈ᴮ Rows) (rowProperties color R r)

def paddedRowCoverage (Earlier E Rows : bSet 𝔹) : 𝔹 :=
  ⨅ A, ⨅ r, _root_.imp (A ∈ᴮ Earlier ⊓ pair A r ∈ᴮ E)
    (⨆ σ, σ ∈ᴮ omegaOne ⊓ pair σ r ∈ᴮ Rows)

theorem paddedRowValidity_apply {color : Bool} {R Rows σ r : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ paddedRowValidity color R Rows)
    (Hσ : Γ ≤ σ ∈ᴮ omegaOne) (Hpair : Γ ≤ pair σ r ∈ᴮ Rows) :
    Γ ≤ rowProperties color R r :=
  (le_inf (H.trans ((iInf_le _ σ).trans (iInf_le _ r))) (le_inf Hσ Hpair)).trans bv_imp_elim

theorem paddedRowCoverage_witness {Earlier E Rows A r : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ paddedRowCoverage Earlier E Rows)
    (HA : Γ ≤ A ∈ᴮ Earlier) (Hpair : Γ ≤ pair A r ∈ᴮ E) :
    ∃ σ : bSet 𝔹, Γ ≤ σ ∈ᴮ omegaOne ⊓ pair σ r ∈ᴮ Rows :=
  exists_convert
    ((le_inf (H.trans ((iInf_le _ A).trans (iInf_le _ r))) (le_inf HA Hpair)).trans bv_imp_elim)
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)

theorem fallback_rowProperties
    {color : Bool} {R Earlier h E seed Seed Rows σ r : bSet 𝔹} {Γ : 𝔹}
    (HEarlier : Γ ≤ Earlier ⊆ᴮ blockObjects color R)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (Hseed : Γ ≤ blockEnumerationData color R Seed seed)
    (HRows : Γ ≤ is_function omegaOne blockEnumerationCodes Rows)
    (Hfallback : Γ ≤ fallbackFamilyLaw omegaOne blockEnumerationCodes
      (rowCandidate Earlier h E) seed Rows)
    (Hpair : Γ ≤ pair σ r ∈ᴮ Rows) : Γ ≤ rowProperties color R r := by
  have Hdata := selected_fallbackData HRows Hfallback Hpair
  apply (le_inf (le_refl Γ) Hdata).trans
  unfold fallbackData
  rw [inf_sup_left]
  apply sup_le
  · exact rowCandidate_rowProperties (inf_le_left.trans HEarlier)
      (inf_le_left.trans HElaw) (inf_le_right.trans inf_le_right)
  · exact bv_rw' (ϕ := rowProperties color R) (inf_le_right.trans inf_le_right)
      (h_congr := rowProperties_ext_graph color R)
      (H_new := inf_le_left.trans (rowProperties_of_blockEnumerationData Hseed))

/-- At an occupied coordinate, bounded fallback choice must retain the
unique original selected row, not merely another row for the same object. -/
theorem fallback_retains_earlier_row
    {color : Bool} {R Earlier h E seed Rows A r : bSet 𝔹} {Γ : 𝔹}
    (Hh : Γ ≤ is_injective_function Earlier omegaOne h)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HRows : Γ ≤ is_function omegaOne blockEnumerationCodes Rows)
    (Hfallback : Γ ≤ fallbackFamilyLaw omegaOne blockEnumerationCodes
      (rowCandidate Earlier h E) seed Rows)
    (HA : Γ ≤ A ∈ᴮ Earlier) (HAr : Γ ≤ pair A r ∈ᴮ E) :
    ∃ σ : bSet 𝔹, Γ ≤ σ ∈ᴮ omegaOne ⊓ pair σ r ∈ᴮ Rows := by
  have Hσex : Γ ≤ ⨆ σ, σ ∈ᴮ omegaOne ⊓ pair A σ ∈ᴮ h :=
    (le_inf ((is_total_of_is_function (Hh.trans inf_le_left)).trans (iInf_le _ A)) HA).trans
      bv_imp_elim
  obtain ⟨σ, Hσ⟩ := exists_convert Hσex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hcandidate : Γ ≤ rowCandidate Earlier h E σ r :=
    le_iSup_of_le A (le_inf HA (le_inf (Hσ.trans inf_le_right) HAr))
  have Hex : Γ ≤ candidateValue blockEnumerationCodes (rowCandidate Earlier h E) σ :=
    le_iSup_of_le r (le_inf (mem_codomain_of_is_function HAr HE) Hcandidate)
  have Hsex : Γ ≤ ⨆ s, s ∈ᴮ blockEnumerationCodes ⊓ pair σ s ∈ᴮ Rows :=
    (le_inf ((is_total_of_is_function HRows).trans (iInf_le _ σ))
      (Hσ.trans inf_le_left)).trans bv_imp_elim
  obtain ⟨s, Hs⟩ := exists_convert Hsex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hselected : Γ ≤ rowCandidate Earlier h E σ s :=
    selected_candidate HRows Hfallback (Hs.trans inf_le_right) Hex
  have Hsr : Γ ≤ s =ᴮ r := rowCandidate_unique (Hh.trans inf_le_right) HE Hselected Hcandidate
  exact ⟨σ, le_inf (Hσ.trans inf_le_left)
    (mem_congr (pair_congr bv_refl Hsr) bv_refl (Hs.trans inf_le_right))⟩

/-- Earlier objects themselves cannot disappear vacuously: the fixed
enumeration function supplies a graph for each object, and coverage
places that very selected graph at an actual omega-one coordinate. -/
theorem exists_padded_row_for_object
    {color : Bool} {R Earlier E Rows A : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HEarlier : Γ ≤ Earlier ⊆ᴮ blockObjects color R)
    (Hcoverage : Γ ≤ paddedRowCoverage Earlier E Rows) (HA : Γ ≤ A ∈ᴮ Earlier) :
    ∃ σ r : bSet 𝔹, Γ ≤ σ ∈ᴮ omegaOne ∧ Γ ≤ pair A r ∈ᴮ E ∧
      Γ ≤ pair σ r ∈ᴮ Rows ∧ Γ ≤ blockEnumerationData color R A r := by
  obtain ⟨r, HAr, Hdata⟩ := exists_selected_enumeration HE HElaw (mem_of_mem_subset HEarlier HA)
  obtain ⟨σ, Hσ⟩ := paddedRowCoverage_witness Hcoverage HA HAr
  exact ⟨σ, r, Hσ.trans inf_le_left, HAr, Hσ.trans inf_le_right, Hdata⟩

/-- Construct an actual full row family from an internally small family
of earlier objects, retaining the fixed enumeration family on all of
them and using the given valid seed on unused coordinates. -/
theorem exists_padded_block_rows
    {color : Bool} {R Earlier E Seed seed : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HEarlier : Γ ≤ Earlier ⊆ᴮ blockObjects color R)
    (Hsmall : Γ ≤ injects_into Earlier omegaOne)
    (Hseed : Γ ≤ blockEnumerationData color R Seed seed) :
    ∃ Rows : bSet 𝔹, Γ ≤ is_function omegaOne blockEnumerationCodes Rows ⊓
      (paddedRowValidity color R Rows ⊓ paddedRowCoverage Earlier E Rows) := by
  obtain ⟨h, Hh⟩ := exists_convert (injection_into_of_injects_into Hsmall) B_ext_injective_code
  obtain ⟨Rows, HRows⟩ := exists_fallback_selector
    (D := omegaOne) (P := rowCandidate Earlier h E)
    (rowCandidate_ext_index Earlier h E) (rowCandidate_ext_row Earlier h E)
    (blockEnumerationData_mem_codes Hseed)
  refine ⟨Rows, le_inf (HRows.trans inf_le_left) (le_inf ?_ ?_)⟩
  · apply le_iInf
    intro σ
    apply le_iInf
    intro r
    rw [← deduction]
    exact fallback_rowProperties (inf_le_left.trans HEarlier) (inf_le_left.trans HElaw)
      (inf_le_left.trans Hseed) (inf_le_left.trans (HRows.trans inf_le_left))
      (inf_le_left.trans (HRows.trans inf_le_right)) (inf_le_right.trans inf_le_right)
  · apply le_iInf
    intro A
    apply le_iInf
    intro r
    rw [← deduction]
    obtain ⟨σ, Hσ⟩ := fallback_retains_earlier_row (inf_le_left.trans Hh)
      (inf_le_left.trans HE) (inf_le_left.trans (HRows.trans inf_le_left))
      (inf_le_left.trans (HRows.trans inf_le_right))
      (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)
    exact le_iSup_of_le σ Hσ

end bSet.ErdosPaddedBlockRows
