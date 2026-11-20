/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalBlockCandidate
public import Erdos1172.Part4InternalBlockImageTransfer
public import Erdos1172.Part4InternalSeedBlock
public import Erdos1172.Part4InternalPaddedBlockRows

@[expose] public section

/-!
# A whole-block candidate from a large active-neighborhood future

The seed and actual padded row family allow the earlier family to be
empty or Boolean-mixed. The proved one-block extension is converted to
its exact whole image; all earlier coordinates still come from the same
fixed enumeration family. The resulting candidate mentions only the
original future and the two selector input sets, not the later thinned
future used to witness its existence.

Uniform adjacency of the supplied large future to all active points is
explicit. Countability of the active set does not supply that premise.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosBlockCandidateExistence

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosIdeal ErdosDenseBasis ErdosColargeIntersection
open ErdosCanonicalBlocks ErdosPaddedBlockRows ErdosOneBlockExtension
open ErdosBlockCandidate ErdosBlockImageTransfer ErdosSeedBlock

theorem activeCompatible_subset_target {color : Bool} {R Active L A : bSet 𝔹} {Γ : 𝔹}
    (Hactive : Γ ≤ activeCompatible color R Active L) (HA : Γ ≤ A ⊆ᴮ L) :
    Γ ≤ activeCompatible color R Active A := by
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  exact activeCompatible_apply (inf_le_left.trans Hactive)
    (inf_le_right.trans inf_le_left)
    (mem_of_mem_subset (inf_le_left.trans HA) (inf_le_right.trans inf_le_right))

theorem objectsBefore_of_padded_rows
    {color : Bool} {R E Earlier Rows f A : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HEarlier : Γ ≤ Earlier ⊆ᴮ blockObjects color R)
    (Hcoverage : Γ ≤ paddedRowCoverage Earlier E Rows)
    (Hbefore : Γ ≤ rowsBeforeBlock Rows f)
    (Hdata : Γ ≤ blockEnumerationData color R A f) :
    Γ ≤ objectsBefore Earlier A := by
  apply le_iInf
  intro B
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  obtain ⟨σ, r, Hσ, _, Hσr, Hrdata⟩ := exists_padded_row_for_object
    (inf_le_left.trans HE) (inf_le_left.trans HElaw) (inf_le_left.trans HEarlier)
    (inf_le_left.trans Hcoverage) (inf_le_right.trans inf_le_left)
  exact rowsBeforeBlock_apply (inf_le_left.trans Hbefore) Hσ Hσr
    (rangeMem_of_blockObject_mem Hrdata (inf_le_right.trans (inf_le_right.trans inf_le_left)))
    (rangeMem_of_blockObject_mem (inf_le_left.trans Hdata)
      (inf_le_right.trans (inf_le_right.trans inf_le_right)))

theorem oldRowsCompatible_of_padded_rows
    {color : Bool} {R J E Earlier Rows f K A : bSet 𝔹} {Γ : 𝔹}
    (Hcoverage : Γ ≤ paddedRowCoverage Earlier E Rows)
    (HK : Γ ≤ is_function omegaOne (bv_powerset omegaOne) K)
    (Hcolarge : Γ ≤ ⨅ σ, ⨅ C, _root_.imp (pair σ C ∈ᴮ K) (colarge omegaOne J C))
    (Hcross : Γ ≤ commonRowCrossEdges color R Rows f K)
    (Hdata : Γ ≤ blockEnumerationData color R A f) :
    Γ ≤ oldRowsCompatible color R J E Earlier A := by
  apply le_iInf
  intro B
  apply le_iInf
  intro r
  rw [← deduction]
  let Δ := Γ ⊓ (B ∈ᴮ Earlier ⊓ pair B r ∈ᴮ E)
  obtain ⟨σ, Hσ⟩ := paddedRowCoverage_witness (inf_le_left.trans Hcoverage)
    (show Δ ≤ B ∈ᴮ Earlier from inf_le_right.trans inf_le_left)
    (show Δ ≤ pair B r ∈ᴮ E from inf_le_right.trans inf_le_right)
  have HCex : Δ ≤ ⨆ C, C ∈ᴮ bv_powerset omegaOne ⊓ pair σ C ∈ᴮ K :=
    (le_inf (inf_le_left.trans ((is_total_of_is_function HK).trans (iInf_le _ σ)))
      (Hσ.trans inf_le_left)).trans bv_imp_elim
  obtain ⟨C, HC⟩ := exists_convert HCex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have HlargeC : Δ ≤ colarge omegaOne J C :=
    (le_inf (inf_le_left.trans (Hcolarge.trans ((iInf_le _ σ).trans (iInf_le _ C))))
      (HC.trans inf_le_right)).trans bv_imp_elim
  refine le_iSup_of_le C (le_inf HlargeC ?_)
  apply le_iInf
  intro i
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  exact (commonRowCrossEdges_apply
    (inf_le_left.trans (inf_le_left.trans Hcross))
    (inf_le_left.trans (Hσ.trans inf_le_right)) (inf_le_left.trans (HC.trans inf_le_right))
    (inf_le_right.trans inf_le_left) (inf_le_right.trans (inf_le_right.trans inf_le_left))
    (rangeMem_of_blockObject_mem (inf_le_left.trans (inf_le_left.trans Hdata))
      (inf_le_right.trans (inf_le_right.trans inf_le_right)))).trans inf_le_right

/-- The large active-neighborhood future is a witness of candidate
existence, not a parameter of the eventual fixed block selector. -/
theorem exists_candidate_of_large_active_future
    {color : Bool} {R J I B E S Earlier Active L : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (Hproper : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hdiag : Γ ≤ diagonalClosure omegaOne J)
    (HB : Γ ≤ is_function I (bv_powerset omegaOne) B)
    (HBpos : Γ ≤ positiveValues omegaOne J I B)
    (Hdense : Γ ≤ denseValues omegaOne J I B) (HI : Γ ≤ injects_into I omegaOne)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HEarlier : Γ ≤ Earlier ⊆ᴮ blockObjects color R)
    (Hsmall : Γ ≤ injects_into Earlier omegaOne)
    (Hno : Γ ≤ (hasTwoBlock color R omegaOne bSet.omega omegaTwo)ᶜ)
    (HnoOpp : Γ ≤ (hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo)ᶜ)
    (HL : Γ ≤ L ⊆ᴮ omegaTwo) (Hlarge : Γ ≤ injects_into omegaTwo L)
    (HLS : Γ ≤ L ⊆ᴮ S) (Hactive : Γ ≤ activeCompatible color R Active L) :
    ∃ A : bSet 𝔹, Γ ≤ blockCandidate color R J E S Earlier Active A := by
  obtain ⟨seed, Hseed⟩ := exists_seed_block (color := color) (R := R)
    HCH Hproper Habsorb Hclosure Hdiag HL Hlarge HnoOpp
  have HseedData := block_image_data HL (Hseed.trans inf_le_left)
    (Hseed.trans (inf_le_right.trans inf_le_left))
    (Hseed.trans (inf_le_right.trans inf_le_right))
  obtain ⟨Rows, HRows⟩ := exists_padded_block_rows HE HElaw HEarlier Hsmall HseedData
  have HrowValid := HRows.trans (inf_le_right.trans inf_le_left)
  have Hcoverage := HRows.trans (inf_le_right.trans inf_le_right)
  have HrowInj : Γ ≤ ⨅ σ, ⨅ r, _root_.imp
      (σ ∈ᴮ omegaOne ⊓ pair σ r ∈ᴮ Rows)
      (is_injective_function omegaOne omegaTwo r) := by
    apply le_iInf
    intro σ
    apply le_iInf
    intro r
    rw [← deduction]
    exact (paddedRowValidity_apply (inf_le_left.trans HrowValid)
      (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)).trans inf_le_left
  have HrowHom : Γ ≤ ⨅ σ, ⨅ r, _root_.imp
      (σ ∈ᴮ omegaOne ⊓ pair σ r ∈ᴮ Rows)
      (homogeneousUnion color R omegaOne omegaOne r r) := by
    apply le_iInf
    intro σ
    apply le_iInf
    intro r
    rw [← deduction]
    exact (paddedRowValidity_apply (inf_le_left.trans HrowValid)
      (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)).trans
      (inf_le_right.trans inf_le_right)
  obtain ⟨f, K, Hblock⟩ := exists_one_block_extension HCH Hproper Habsorb Hclosure Hdiag
    HB HBpos Hdense HI (HRows.trans inf_le_left) HrowInj HrowHom Hno HnoOpp HL Hlarge
  have Hdata := block_image_data HL (Hblock.trans inf_le_left)
    (Hblock.trans (inf_le_right.trans inf_le_left))
    (Hblock.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))
  have Hbefore := Hblock.trans (inf_le_right.trans (inf_le_right.trans
    (inf_le_right.trans inf_le_left)))
  have Hcommon := Hblock.trans (inf_le_right.trans (inf_le_right.trans
    (inf_le_right.trans inf_le_right)))
  have HimageSub := block_image_subset_future
    (is_func'_of_is_function (Hblock.trans (inf_le_left.trans inf_le_left)))
  exact ⟨image omegaOne omegaTwo f, blockCandidate_of_data
    (blockEnumerationData_mem_object Hdata) (subset_trans' HimageSub HLS)
    (objectsBefore_of_padded_rows HE HElaw HEarlier Hcoverage Hbefore Hdata)
    (oldRowsCompatible_of_padded_rows Hcoverage (Hcommon.trans inf_le_left)
      (Hcommon.trans (inf_le_right.trans inf_le_left))
      (Hcommon.trans (inf_le_right.trans inf_le_right)) Hdata)
    (activeCompatible_subset_target Hactive HimageSub)⟩

end bSet.ErdosBlockCandidateExistence
