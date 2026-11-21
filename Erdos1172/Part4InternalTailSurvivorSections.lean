/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCountableTailRun
public import Erdos1172.Part4InternalFusionSeedBridge
public import Erdos1172.Part4InternalFusionMaskedTailCross
public import Erdos1172.Part4InternalFusionRowCandidateCongruence

@[expose] public section

/-!
# Deterministic survivor sets for the actual countable block tail

Whole-block sections are used directly; no independently chosen family of
compatibility masks is required. Actual tail candidates make all old-row
sections co-large and make the strictly later sections of a tail row
co-large. Countable closure gives the two concrete intersections.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosTailSurvivorSections

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosPartition ErdosCanonicalBlocks
open ErdosCountableTailRun ErdosBlockCandidate ErdosFusionRowCandidates
open ErdosFusionSeedBridge ErdosFusionMaskedTail ErdosColargeIntersection
open ErdosIndexedIntersection ErdosFusionHistoryCongruence ErdosDenseBasis

def tailCommon (color : Bool) (R E Tail b D : bSet 𝔹) : bSet 𝔹 :=
  indexedIntersection omegaOne (fusionSectionFamily (!color) R E b Tail bSet.omega) D

def oldSurvivors (color : Bool) (R E Tail X ν b : bSet 𝔹) : bSet 𝔹 :=
  difference (activeMask X ν) (difference omegaOne (tailCommon color R E Tail b bSet.omega))

def laterSurvivors (color : Bool) (R E Tail m b : bSet 𝔹) : bSet 𝔹 :=
  tailCommon color R E Tail b (activatedStages bSet.omega m)

theorem tailCandidatesLaw_apply {color : Bool} {R J E S B Tail n A : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ tailCandidatesLaw color R J E S B Tail)
    (Hpair : Γ ≤ pair n A ∈ᴮ Tail) :
    Γ ≤ blockCandidate color R J E S (binary_union B (image n (bv_powerset omegaTwo) Tail)) ∅ A :=
  ((le_inf (H.trans ((iInf_le _ n).trans (iInf_le _ A))) Hpair).trans bv_imp_elim).trans inf_le_left

theorem tailCommon_subset {color : Bool} {R E Tail b D : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ tailCommon color R E Tail b D ⊆ᴮ omegaOne := indexedIntersection_subset

theorem tailCommon_mem_section {color : Bool} {R E Tail b D n v : bSet 𝔹} {Γ : 𝔹}
    (Hv : Γ ≤ v ∈ᴮ tailCommon color R E Tail b D)
    (HnD : Γ ≤ n ∈ᴮ D) (Hn : Γ ≤ n ∈ᴮ bSet.omega) :
    Γ ≤ v ∈ᴮ fusionSection (!color) R E b Tail n :=
  (le_inf ((mem_indexedIntersection_iff.mp Hv).2.trans
    ((iInf_le _ n).trans (iInf_le _ (fusionSection (!color) R E b Tail n))))
    (le_inf HnD (fusionSectionFamily_pair Hn))).trans bv_imp_elim

theorem tailCommon_congr_object (color : Bool) (R E Tail D : bSet 𝔹) :
    B_congr (fun b => tailCommon color R E Tail b D) := by
  intro b c Γ H
  exact indexedIntersection_congr_family omegaOne D
    (fusionSectionFamily_congr_object (!color) R E Tail bSet.omega H)

theorem tailCommon_congr_domain (color : Bool) (R E Tail b : bSet 𝔹) :
    B_congr (tailCommon color R E Tail b) :=
  comprehend_parameter_congr omegaOne
    (fun D v => ⨅ n, ⨅ A, _root_.imp
      (n ∈ᴮ D ⊓ pair n A ∈ᴮ fusionSectionFamily (!color) R E b Tail bSet.omega)
      (v ∈ᴮ A))
    (fun _ => B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_mem_left))))
    (fun _ => B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_inf B_ext_mem_right B_ext_const) (h₂ := B_ext_const))))

theorem activeMask_congr_row (X : bSet 𝔹) : B_congr (activeMask X) :=
  comprehend_parameter_congr omegaOne
    (fun ν v => ⨆ ξ, (ξ ∈ᴮ omegaOne ⊓ ν ∈ᴮ ξ) ⊓ pair (pair ξ ν) v ∈ᴮ X)
    (fun _ => B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_pair_mem_right))
    (fun v => B_ext_iSup (h := fun _ =>
      B_ext_inf (B_ext_inf B_ext_const B_ext_mem_left)
        (B_ext_pair_right (ϕ := fun q => pair q v ∈ᴮ X) B_ext_pair_mem_left)))

theorem oldSurvivors_congr_row (color : Bool) (R E Tail X b : bSet 𝔹) :
    B_congr (fun ν => oldSurvivors color R E Tail X ν b) := by
  intro ν μ Γ H
  exact difference_congr_left (activeMask_congr_row X H)

theorem oldSurvivors_congr_object (color : Bool) (R E Tail X ν : bSet 𝔹) :
    B_congr (oldSurvivors color R E Tail X ν) := by
  intro b c Γ H
  exact difference_congr_right
    (difference_congr_right (tailCommon_congr_object color R E Tail bSet.omega H))

theorem laterSurvivors_congr_stage (color : Bool) (R E Tail b : bSet 𝔹) :
    B_congr (fun m => laterSurvivors color R E Tail m b) := by
  intro m n Γ H
  exact tailCommon_congr_domain color R E Tail b (activatedStages_congr_row bSet.omega H)

theorem laterSurvivors_congr_object (color : Bool) (R E Tail m : bSet 𝔹) :
    B_congr (laterSurvivors color R E Tail m) :=
  tailCommon_congr_object color R E Tail (activatedStages bSet.omega m)

theorem oldSurvivors_mem_mask {color : Bool} {R E Tail X ν b v : bSet 𝔹} {Γ : 𝔹}
    (Hv : Γ ≤ v ∈ᴮ oldSurvivors color R E Tail X ν b) :
    Γ ≤ v ∈ᴮ activeMask X ν := by
  have H : Γ ≤ v ∈ᴮ activeMask X ν ⊓
      (v ∈ᴮ difference omegaOne (tailCommon color R E Tail b bSet.omega))ᶜ := by
    rwa [← mem_difference]
  exact H.trans inf_le_left

theorem oldSurvivors_mem_common {color : Bool} {R E Tail X ν b v : bSet 𝔹} {Γ : 𝔹}
    (Hv : Γ ≤ v ∈ᴮ oldSurvivors color R E Tail X ν b) :
    Γ ≤ v ∈ᴮ tailCommon color R E Tail b bSet.omega := by
  have Hbound : Γ ≤ v ∈ᴮ omegaOne := mem_of_mem_subset activeMask_subset (oldSurvivors_mem_mask Hv)
  have Hnot : Γ ≤ (v ∈ᴮ difference omegaOne (tailCommon color R E Tail b bSet.omega))ᶜ := by
    have H := Hv
    change Γ ≤ v ∈ᴮ difference (activeMask X ν)
      (difference omegaOne (tailCommon color R E Tail b bSet.omega)) at H
    rw [mem_difference] at H
    exact H.trans inf_le_right
  rw [← compl_compl (v ∈ᴮ tailCommon color R E Tail b bSet.omega), ← imp_bot, ← deduction]
  apply bv_absurd _ ?_ (inf_le_left.trans Hnot)
  rw [mem_difference]
  exact le_inf (inf_le_left.trans Hbound) inf_le_right

theorem oldSurvivors_subset {color : Bool} {R E Tail X ν b : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ oldSurvivors color R E Tail X ν b ⊆ᴮ omegaOne :=
  subset_trans' difference_subset activeMask_subset

theorem laterSurvivors_subset {color : Bool} {R E Tail m b : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ laterSurvivors color R E Tail m b ⊆ᴮ omegaOne := tailCommon_subset

theorem tailCommon_colarge {color : Bool} {R J E Tail b D : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J) (Hclosure : Γ ≤ countableClosure J)
    (HD : Γ ≤ D ⊆ᴮ bSet.omega) (Hcount : Γ ≤ injects_into D bSet.omega)
    (Hsections : Γ ≤ ⨅ n, _root_.imp (n ∈ᴮ D)
      (colarge omegaOne J (fusionSection (!color) R E b Tail n))) :
    Γ ≤ colarge omegaOne J (tailCommon color R E Tail b D) := by
  apply indexedIntersection_colarge_of_colarge_values HJ Hclosure
    (is_func'_subset_of_is_func'
      (is_func'_of_is_function (fusionSectionFamily_is_function
        (edgeColor := !color) (R := R) (E := E) (b := b) (Blocks := Tail)
        (D := bSet.omega))) HD) Hcount
  apply le_iInf
  intro n
  apply le_iInf
  intro A
  rw [← deduction]
  have Hvalue := (mem_fusionSectionFamily_iff.mp
    (show Γ ⊓ (n ∈ᴮ D ⊓ pair n A ∈ᴮ fusionSectionFamily (!color) R E b Tail bSet.omega) ≤
      pair n A ∈ᴮ fusionSectionFamily (!color) R E b Tail bSet.omega from
        inf_le_right.trans inf_le_right)).2.2
  have Hlarge : Γ ⊓ (n ∈ᴮ D ⊓
      pair n A ∈ᴮ fusionSectionFamily (!color) R E b Tail bSet.omega) ≤
      colarge omegaOne J (fusionSection (!color) R E b Tail n) :=
    (le_inf (inf_le_left.trans (Hsections.trans (iInf_le _ n)))
      (inf_le_right.trans inf_le_left)).trans bv_imp_elim
  exact bv_rw' (ϕ := colarge omegaOne J) Hvalue
    (h_congr := colarge_ext_common omegaOne J) (H_new := Hlarge)

theorem old_tailCommon_colarge
    {color : Bool} {R J E S B Tail b : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J) (Hclosure : Γ ≤ countableClosure J)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HB : Γ ≤ B ⊆ᴮ blockObjects color R)
    (HTail : Γ ≤ is_function bSet.omega (bv_powerset omegaTwo) Tail)
    (Htail : Γ ≤ tailCandidatesLaw color R J E S B Tail) (Hb : Γ ≤ b ∈ᴮ B) :
    Γ ≤ colarge omegaOne J (tailCommon color R E Tail b bSet.omega) := by
  apply tailCommon_colarge HJ Hclosure subset_self injects_into_refl
  apply le_iInf
  intro n
  rw [← deduction]
  let Δ := Γ ⊓ n ∈ᴮ bSet.omega
  have Hex : Δ ≤ ⨆ A, A ∈ᴮ bv_powerset omegaTwo ⊓ pair n A ∈ᴮ Tail :=
    (le_inf (inf_le_left.trans ((is_total_of_is_function HTail).trans (iInf_le _ n)))
      inf_le_right).trans bv_imp_elim
  obtain ⟨A, HA⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hbefore : Δ ≤ b ∈ᴮ binary_union B (image n (bv_powerset omegaTwo) Tail) := by
    rw [mem_binary_union]
    exact (inf_le_left.trans Hb).trans le_sup_left
  exact fusionSection_colarge_of_blockCandidate (inf_le_left.trans HJ)
    (inf_le_left.trans HE) (mem_of_mem_subset (inf_le_left.trans HB) (inf_le_left.trans Hb))
    (inf_le_left.trans (HTail.trans (inf_le_left.trans inf_le_left)))
    (HA.trans inf_le_right) Hbefore
    (tailCandidatesLaw_apply (inf_le_left.trans Htail) (HA.trans inf_le_right))

theorem laterSurvivors_colarge
    {color : Bool} {R J E S B Tail m b : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J) (Hclosure : Γ ≤ countableClosure J)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HTail : Γ ≤ is_function bSet.omega (bv_powerset omegaTwo) Tail)
    (Htail : Γ ≤ tailCandidatesLaw color R J E S B Tail)
    (Hmb : Γ ≤ pair m b ∈ᴮ Tail) :
    Γ ≤ colarge omegaOne J (laterSurvivors color R E Tail m b) := by
  have Hb := blockCandidate_object (tailCandidatesLaw_apply Htail Hmb)
  apply tailCommon_colarge HJ Hclosure activatedStages_subset
    (activatedStages_countable omega_mem_omegaOne)
  apply le_iInf
  intro n
  rw [← deduction]
  let Δ := Γ ⊓ n ∈ᴮ activatedStages bSet.omega m
  have Hn := mem_activatedStages_iff.mp
    (show Δ ≤ n ∈ᴮ activatedStages bSet.omega m from inf_le_right)
  have Hex : Δ ≤ ⨆ A, A ∈ᴮ bv_powerset omegaTwo ⊓ pair n A ∈ᴮ Tail :=
    (le_inf (inf_le_left.trans ((is_total_of_is_function HTail).trans (iInf_le _ n)))
      Hn.1).trans bv_imp_elim
  obtain ⟨A, HA⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hbefore : Δ ≤ b ∈ᴮ binary_union B (image n (bv_powerset omegaTwo) Tail) := by
    rw [mem_binary_union]
    exact (mem_image (inf_le_left.trans Hmb) Hn.2
      (inf_le_left.trans (mem_codomain_of_is_function Hmb HTail))).trans le_sup_right
  exact fusionSection_colarge_of_blockCandidate (inf_le_left.trans HJ)
    (inf_le_left.trans HE) (inf_le_left.trans Hb)
    (inf_le_left.trans (HTail.trans (inf_le_left.trans inf_le_left)))
    (HA.trans inf_le_right) Hbefore
    (tailCandidatesLaw_apply (inf_le_left.trans Htail) (HA.trans inf_le_right))

theorem oldSurvivors_colarge
    {color : Bool} {R J E S B Tail X ν b : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J) (Hclosure : Γ ≤ countableClosure J)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HB : Γ ≤ B ⊆ᴮ blockObjects color R)
    (HTail : Γ ≤ is_function bSet.omega (bv_powerset omegaTwo) Tail)
    (Htail : Γ ≤ tailCandidatesLaw color R J E S B Tail) (Hb : Γ ≤ b ∈ᴮ B)
    (Hmask : Γ ≤ colarge omegaOne J (activeMask X ν)) :
    Γ ≤ colarge omegaOne J (oldSurvivors color R E Tail X ν b) :=
  colarge_difference_of_small HJ Hmask
    ((old_tailCommon_colarge HJ Hclosure HE HB HTail Htail Hb).trans inf_le_right)

theorem oldSurvivor_cross_tail {color : Bool}
    {R E Tail X ν b v n A x y : bSet 𝔹} {Γ : 𝔹}
    (HTail : Γ ≤ is_function bSet.omega (bv_powerset omegaTwo) Tail)
    (Hv : Γ ≤ v ∈ᴮ oldSurvivors color R E Tail X ν b)
    (HnA : Γ ≤ pair n A ∈ᴮ Tail)
    (Hvx : Γ ≤ pair v x ∈ᴮ canonicalRow E b) (Hy : Γ ≤ y ∈ᴮ A) :
    Γ ≤ graphColor (!color) R x y :=
  fusionSection_apply (tailCommon_mem_section (oldSurvivors_mem_common Hv)
    (mem_domain_of_is_function HnA HTail) (mem_domain_of_is_function HnA HTail)) HnA Hvx Hy

theorem laterSurvivor_cross_tail {color : Bool}
    {R E Tail m b v n A x y : bSet 𝔹} {Γ : 𝔹}
    (HTail : Γ ≤ is_function bSet.omega (bv_powerset omegaTwo) Tail)
    (Hv : Γ ≤ v ∈ᴮ laterSurvivors color R E Tail m b)
    (Hmn : Γ ≤ m ∈ᴮ n) (HnA : Γ ≤ pair n A ∈ᴮ Tail)
    (Hvx : Γ ≤ pair v x ∈ᴮ canonicalRow E b) (Hy : Γ ≤ y ∈ᴮ A) :
    Γ ≤ graphColor (!color) R x y :=
  fusionSection_apply (tailCommon_mem_section Hv
    (mem_activatedStages_iff.mpr ⟨mem_domain_of_is_function HnA HTail, Hmn⟩)
    (mem_domain_of_is_function HnA HTail)) HnA Hvx Hy

end bSet.ErdosTailSurvivorSections
