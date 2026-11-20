/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalMaskedTailWitness
public import Erdos1172.Part4InternalFusionMaskedFamily
public import Erdos1172.Part4InternalPartitionSentence

@[expose] public section

/-!
# The internal balanced partition relation from a normal dense ideal

The successful omega-one fusion, co-large active masks, countable tail,
coherent survivor coordinates, and physical point maps are constructed.
The two target exclusions are discharged by Boolean complementation;
every graph is covered using the same graph-independent ideal and basis.

This is a conditional internal partition theorem and its exact sentence
interpretation. It does not construct a Boolean algebra or an ideal,
force full GCH, or prove the relative-consistency question of Problem 1172.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosPartitionFromIdeal

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosDenseBasis ErdosPartition ErdosCanonicalBlocks
open ErdosFusionMaskedFamily ErdosFusionPreparation ErdosFusionRun ErdosFusionRunSuccess
open ErdosFusionGlobalRowLaw ErdosFusionRunBlockOrder ErdosCountableTailRun
open ErdosMaskedTailWitness

theorem opposite_target_of_exclusions
    {color : Bool} {R J I D : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HJ : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hdiag : Γ ≤ diagonalClosure omegaOne J)
    (HD : Γ ≤ is_function I (bv_powerset omegaOne) D)
    (HDpos : Γ ≤ positiveValues omegaOne J I D)
    (Hdense : Γ ≤ denseValues omegaOne J I D)
    (HI : Γ ≤ injects_into I omegaOne)
    (Hno : Γ ≤ (hasTwoBlock color R omegaOne bSet.omega omegaTwo)ᶜ)
    (HnoOpp : Γ ≤ (hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo)ᶜ) :
    Γ ≤ hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo := by
  obtain ⟨E, F, B, P, Y, top, Run, Hdata⟩ :=
    exists_prepared_masked_fusion_run (S := omegaTwo) HCH HJ Habsorb Hclosure Hdiag
      HD HDpos Hdense HI Hno HnoOpp subset_self injects_into_refl
  have Hprep := Hdata.trans inf_le_left
  have Henum := Hprep.trans inf_le_left
  have Hselector := Hprep.trans inf_le_right
  have HE := Henum.trans inf_le_left
  have HElaw := Henum.trans inf_le_right
  have HF := Hselector.trans inf_le_left
  have HFlaw := Hselector.trans (inf_le_right.trans inf_le_left)
  have Hactual := Hdata.trans (inf_le_right.trans inf_le_left)
  have HRun := Hactual.trans (inf_le_right.trans inf_le_left)
  have HrunLaw := Hactual.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have Hsuccess := Hactual.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  have Hlaws := Hdata.trans (inf_le_right.trans inf_le_right)
  have Hleast := Hlaws.trans inf_le_left
  have Hactive := Hlaws.trans (inf_le_right.trans inf_le_left)
  have Horder := Hlaws.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have Hmasks := Hlaws.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  have HBlocks := fullBlocks_is_function HRun HrunLaw
  have Hfamily := fullBlockFamily_subset HE HElaw HF HFlaw HRun HrunLaw Hsuccess
  have Hsmall := fullBlockFamily_small HRun HrunLaw
  obtain ⟨G, Tail, HtailData⟩ := exists_countable_tail (S := omegaTwo)
    HCH HJ Habsorb Hclosure Hdiag HD HDpos Hdense HI HE HElaw Hfamily Hsmall
    Hno HnoOpp subset_self injects_into_refl
  have HTail := HtailData.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have Htail := HtailData.trans
    (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))
  exact hasTwoBlock_of_masked_tail HJ Hclosure HE HElaw HBlocks Hfamily
    (is_func'_of_is_function (fullCoordinates_is_function HRun HrunLaw))
    (coordinateCandidateLaw_of_fullLeastLaw Hleast) Hactive Horder HTail Htail Hmasks

/-- Neither color is chosen externally: the conclusion is the actual
Boolean join of the two exact target values. -/
theorem two_color_target_of_normal_dense_ideal
    {R J I D : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HJ : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hdiag : Γ ≤ diagonalClosure omegaOne J)
    (HD : Γ ≤ is_function I (bv_powerset omegaOne) D)
    (HDpos : Γ ≤ positiveValues omegaOne J I D)
    (Hdense : Γ ≤ denseValues omegaOne J I D)
    (HI : Γ ≤ injects_into I omegaOne) :
    Γ ≤ hasTwoBlock false R omegaOne bSet.omega omegaTwo ⊔
      hasTwoBlock true R omegaOne bSet.omega omegaTwo := by
  rw [← compl_compl (hasTwoBlock false R omegaOne bSet.omega omegaTwo ⊔
    hasTwoBlock true R omegaOne bSet.omega omegaTwo), ← imp_bot, ← deduction]
  let Δ := Γ ⊓ (hasTwoBlock false R omegaOne bSet.omega omegaTwo ⊔
    hasTwoBlock true R omegaOne bSet.omega omegaTwo)ᶜ
  have Hno : Δ ≤ (hasTwoBlock false R omegaOne bSet.omega omegaTwo)ᶜ :=
    inf_le_right.trans (compl_le_compl le_sup_left)
  have HnoOpp : Δ ≤ (hasTwoBlock true R omegaOne bSet.omega omegaTwo)ᶜ :=
    inf_le_right.trans (compl_le_compl le_sup_right)
  have Htarget := opposite_target_of_exclusions (color := false)
    (inf_le_left.trans HCH) (inf_le_left.trans HJ) (inf_le_left.trans Habsorb)
    (inf_le_left.trans Hclosure) (inf_le_left.trans Hdiag) (inf_le_left.trans HD)
    (inf_le_left.trans HDpos) (inf_le_left.trans Hdense) (inf_le_left.trans HI) Hno HnoOpp
  exact bv_absurd _ Htarget HnoOpp

/-- The ideal and dense basis are fixed before the universal coloring
quantifier. All fusion and tail hypotheses have been discharged. -/
theorem part4Value_of_normal_dense_ideal
    {J I D : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HJ : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hdiag : Γ ≤ diagonalClosure omegaOne J)
    (HD : Γ ≤ is_function I (bv_powerset omegaOne) D)
    (HDpos : Γ ≤ positiveValues omegaOne J I D)
    (Hdense : Γ ≤ denseValues omegaOne J I D)
    (HI : Γ ≤ injects_into I omegaOne) : Γ ≤ (part4Value : 𝔹) := by
  apply le_iInf
  intro R
  exact two_color_target_of_normal_dense_ideal HCH HJ Habsorb Hclosure Hdiag
    HD HDpos Hdense HI

end bSet.ErdosPartitionFromIdeal

namespace Erdos1172Part4InternalIdealPartition

open Fol
open bSet bSet.ErdosOmegaTwo bSet.ErdosIdeal bSet.ErdosDenseBasis
open Erdos1172Part4InternalPartitionSentence

variable {β : Type 0} [NontrivialCompleteBooleanAlgebra β]

/-- The already verified closed sentence has precisely the constructed
partition value. This forcing statement retains every ideal hypothesis. -/
theorem forces_part4Sentence_of_normal_dense_ideal
    {J I D : bSet β} {Γ : β}
    (HCH : Γ ≤ (CH : β))
    (HJ : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hdiag : Γ ≤ diagonalClosure omegaOne J)
    (HD : Γ ≤ is_function I (bv_powerset omegaOne) D)
    (HDpos : Γ ≤ positiveValues omegaOne J I D)
    (Hdense : Γ ≤ denseValues omegaOne J I D)
    (HI : Γ ≤ injects_into I omegaOne) : Γ ⊩[V β] part4Sentence :=
  forces_part4Sentence_iff.mpr
    (bSet.ErdosPartitionFromIdeal.part4Value_of_normal_dense_ideal
      HCH HJ Habsorb Hclosure Hdiag HD HDpos Hdense HI)

end Erdos1172Part4InternalIdealPartition
