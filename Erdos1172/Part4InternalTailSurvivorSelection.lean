/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalTailSurvivorSections

@[expose] public section

/-!
# Coherent internal survivor coordinates at the original condition

One actual function selects coordinates for all old rows, and another
selects coordinates for all tail rows. Their predicates use globally
congruent graph evaluation, so equality of mixed index names is respected.
Properness and countable closure, together with the already derived
section co-largeness, prove totality of these selections at the same
Boolean condition. No coherent external witness choices are assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosTailSurvivorSelection

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosPartition ErdosCanonicalBlocks
open ErdosCountableTailRun ErdosFusionHistories ErdosBoundedFunctionValue
open ErdosFusionRowCandidates ErdosFusionMaskedTail ErdosColargeIntersection
open ErdosTailSurvivorSections ErdosSmallFiberBound

def oldChoiceSet (color : Bool) (R E Tail Blocks X ν : bSet 𝔹) : bSet 𝔹 :=
  oldSurvivors color R E Tail X ν (blockValue Blocks ν)

def tailChoiceSet (color : Bool) (R E Tail m : bSet 𝔹) : bSet 𝔹 :=
  laterSurvivors color R E Tail m (blockValue Tail m)

def oldCoordinateLaw (color : Bool) (R E Tail Blocks X u : bSet 𝔹) : 𝔹 :=
  ⨅ ν, ⨅ b, ⨅ v, _root_.imp (pair ν b ∈ᴮ Blocks ⊓ pair ν v ∈ᴮ u)
    (v ∈ᴮ oldSurvivors color R E Tail X ν b)

def tailCoordinateLaw (color : Bool) (R E Tail v : bSet 𝔹) : 𝔹 :=
  ⨅ m, ⨅ b, ⨅ w, _root_.imp (pair m b ∈ᴮ Tail ⊓ pair m w ∈ᴮ v)
    (w ∈ᴮ laterSurvivors color R E Tail m b)

theorem oldChoiceSet_congr (color : Bool) (R E Tail Blocks X : bSet 𝔹) :
    B_congr (oldChoiceSet color R E Tail Blocks X) := by
  intro ν μ Γ H
  exact bv_trans
    (oldSurvivors_congr_row color R E Tail X (blockValue Blocks ν) H)
    (oldSurvivors_congr_object color R E Tail X μ (blockValue_congr Blocks H))

theorem tailChoiceSet_congr (color : Bool) (R E Tail : bSet 𝔹) :
    B_congr (tailChoiceSet color R E Tail) := by
  intro m n Γ H
  exact bv_trans (laterSurvivors_congr_stage color R E Tail (blockValue Tail m) H)
    (laterSurvivors_congr_object color R E Tail n (blockValue_congr Tail H))

theorem oldChoiceSet_mem_ext_index (color : Bool) (R E Tail Blocks X v : bSet 𝔹) :
    B_ext (fun ν => v ∈ᴮ oldChoiceSet color R E Tail Blocks X ν) :=
  B_ext_term (ϕ := fun C => v ∈ᴮ C) (t := oldChoiceSet color R E Tail Blocks X)
    B_ext_mem_right (oldChoiceSet_congr color R E Tail Blocks X)

theorem tailChoiceSet_mem_ext_index (color : Bool) (R E Tail v : bSet 𝔹) :
    B_ext (fun m => v ∈ᴮ tailChoiceSet color R E Tail m) :=
  B_ext_term (ϕ := fun C => v ∈ᴮ C) (t := tailChoiceSet color R E Tail)
    B_ext_mem_right (tailChoiceSet_congr color R E Tail)

theorem oldCoordinateLaw_apply
    {color : Bool} {R E Tail Blocks X u ν b v : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ oldCoordinateLaw color R E Tail Blocks X u)
    (Hνb : Γ ≤ pair ν b ∈ᴮ Blocks) (Hνv : Γ ≤ pair ν v ∈ᴮ u) :
    Γ ≤ v ∈ᴮ oldSurvivors color R E Tail X ν b :=
  (le_inf (H.trans ((iInf_le _ ν).trans ((iInf_le _ b).trans (iInf_le _ v))))
    (le_inf Hνb Hνv)).trans bv_imp_elim

theorem tailCoordinateLaw_apply
    {color : Bool} {R E Tail v m b w : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ tailCoordinateLaw color R E Tail v)
    (Hmb : Γ ≤ pair m b ∈ᴮ Tail) (Hmw : Γ ≤ pair m w ∈ᴮ v) :
    Γ ≤ w ∈ᴮ laterSurvivors color R E Tail m b :=
  (le_inf (H.trans ((iInf_le _ m).trans ((iInf_le _ b).trans (iInf_le _ w))))
    (le_inf Hmb Hmw)).trans bv_imp_elim

theorem oldCoordinateLaw_mask
    {color : Bool} {R E Tail Blocks X u ν b v : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ oldCoordinateLaw color R E Tail Blocks X u)
    (Hνb : Γ ≤ pair ν b ∈ᴮ Blocks) (Hνv : Γ ≤ pair ν v ∈ᴮ u) :
    Γ ≤ v ∈ᴮ activeMask X ν :=
  oldSurvivors_mem_mask (oldCoordinateLaw_apply H Hνb Hνv)

theorem oldCoordinateLaw_cross_tail
    {color : Bool} {R E Tail Blocks X u ν b v n A x y : bSet 𝔹} {Γ : 𝔹}
    (HTail : Γ ≤ is_function bSet.omega (bv_powerset omegaTwo) Tail)
    (H : Γ ≤ oldCoordinateLaw color R E Tail Blocks X u)
    (Hνb : Γ ≤ pair ν b ∈ᴮ Blocks) (Hνv : Γ ≤ pair ν v ∈ᴮ u)
    (HnA : Γ ≤ pair n A ∈ᴮ Tail)
    (Hvx : Γ ≤ pair v x ∈ᴮ canonicalRow E b) (Hy : Γ ≤ y ∈ᴮ A) :
    Γ ≤ graphColor (!color) R x y :=
  oldSurvivor_cross_tail HTail (oldCoordinateLaw_apply H Hνb Hνv) HnA Hvx Hy

theorem tailCoordinateLaw_cross_tail
    {color : Bool} {R E Tail v m b w n A x y : bSet 𝔹} {Γ : 𝔹}
    (HTail : Γ ≤ is_function bSet.omega (bv_powerset omegaTwo) Tail)
    (H : Γ ≤ tailCoordinateLaw color R E Tail v)
    (Hmb : Γ ≤ pair m b ∈ᴮ Tail) (Hmw : Γ ≤ pair m w ∈ᴮ v)
    (Hmn : Γ ≤ m ∈ᴮ n) (HnA : Γ ≤ pair n A ∈ᴮ Tail)
    (Hwx : Γ ≤ pair w x ∈ᴮ canonicalRow E b) (Hy : Γ ≤ y ∈ᴮ A) :
    Γ ≤ graphColor (!color) R x y :=
  laterSurvivor_cross_tail HTail (tailCoordinateLaw_apply H Hmb Hmw) Hmn HnA Hwx Hy

theorem exists_old_survivor_coordinates
    {color : Bool} {R J E S Blocks X Tail : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ properIdeal omegaOne J) (Hclosure : Γ ≤ countableClosure J)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HBlocks : Γ ≤ is_function omegaOne (bv_powerset omegaTwo) Blocks)
    (HB : Γ ≤ image omegaOne (bv_powerset omegaTwo) Blocks ⊆ᴮ blockObjects color R)
    (HTail : Γ ≤ is_function bSet.omega (bv_powerset omegaTwo) Tail)
    (Htail : Γ ≤ tailCandidatesLaw color R J E S
      (image omegaOne (bv_powerset omegaTwo) Blocks) Tail)
    (Hmasks : Γ ≤ ⨅ ν, _root_.imp (ν ∈ᴮ omegaOne) (colarge omegaOne J (activeMask X ν))) :
    ∃ u : bSet 𝔹, Γ ≤ is_function omegaOne omegaOne u ⊓
      oldCoordinateLaw color R E Tail Blocks X u := by
  have Hpointwise : Γ ≤ ⨅ ν, _root_.imp (ν ∈ᴮ omegaOne)
      (⨆ v, v ∈ᴮ omegaOne ⊓ v ∈ᴮ oldChoiceSet color R E Tail Blocks X ν) := by
    apply le_iInf
    intro ν
    rw [← deduction]
    let Δ := Γ ⊓ ν ∈ᴮ omegaOne
    have Hpair : Δ ≤ pair ν (blockValue Blocks ν) ∈ᴮ Blocks :=
      graphValue_pair_mem (inf_le_left.trans HBlocks) inf_le_right
    have Hb : Δ ≤ blockValue Blocks ν ∈ᴮ image omegaOne (bv_powerset omegaTwo) Blocks :=
      mem_image Hpair inf_le_right (mem_codomain_of_is_function Hpair (inf_le_left.trans HBlocks))
    have Hmask : Δ ≤ colarge omegaOne J (activeMask X ν) :=
      (le_inf (inf_le_left.trans (Hmasks.trans (iInf_le _ ν))) inf_le_right).trans bv_imp_elim
    have Hlarge : Δ ≤ colarge omegaOne J (oldChoiceSet color R E Tail Blocks X ν) :=
      oldSurvivors_colarge (inf_le_left.trans (HJ.trans inf_le_left))
        (inf_le_left.trans Hclosure) (inf_le_left.trans HE) (inf_le_left.trans HB)
        (inf_le_left.trans HTail) (inf_le_left.trans Htail) Hb Hmask
    obtain ⟨v, Hv⟩ := exists_mem_of_colarge (inf_le_left.trans HJ) Hlarge
    exact le_iSup_of_le v (le_inf (mem_of_mem_subset oldSurvivors_subset Hv) Hv)
  obtain ⟨u, Hu⟩ := exists_selector_of_pointwise
    (fun v => oldChoiceSet_mem_ext_index color R E Tail Blocks X v)
    (fun _ => B_ext_mem_left) Hpointwise
  refine ⟨u, le_inf (Hu.trans inf_le_left) ?_⟩
  apply le_iInf
  intro ν
  apply le_iInf
  intro b
  apply le_iInf
  intro v
  rw [← deduction]
  let Δ := Γ ⊓ (pair ν b ∈ᴮ Blocks ⊓ pair ν v ∈ᴮ u)
  have Hνb : Δ ≤ pair ν b ∈ᴮ Blocks := inf_le_right.trans inf_le_left
  have Hν : Δ ≤ ν ∈ᴮ omegaOne := mem_domain_of_is_function Hνb (inf_le_left.trans HBlocks)
  have Hv : Δ ≤ v ∈ᴮ oldChoiceSet color R E Tail Blocks X ν :=
    (le_inf (inf_le_left.trans ((Hu.trans inf_le_right).trans
      ((iInf_le _ ν).trans (iInf_le _ v))))
      (le_inf Hν (inf_le_right.trans inf_le_right))).trans bv_imp_elim
  have Hb : Δ ≤ blockValue Blocks ν =ᴮ b := graphValue_eq_of_pair (inf_le_left.trans HBlocks) Hνb
  exact mem_congr bv_refl (oldSurvivors_congr_object color R E Tail X ν Hb) Hv

theorem exists_tail_survivor_coordinates
    {color : Bool} {R J E S B Tail : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ properIdeal omegaOne J) (Hclosure : Γ ≤ countableClosure J)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HTail : Γ ≤ is_function bSet.omega (bv_powerset omegaTwo) Tail)
    (Htail : Γ ≤ tailCandidatesLaw color R J E S B Tail) :
    ∃ v : bSet 𝔹, Γ ≤ is_function bSet.omega omegaOne v ⊓ tailCoordinateLaw color R E Tail v := by
  have Hpointwise : Γ ≤ ⨅ m, _root_.imp (m ∈ᴮ bSet.omega)
      (⨆ w, w ∈ᴮ omegaOne ⊓ w ∈ᴮ tailChoiceSet color R E Tail m) := by
    apply le_iInf
    intro m
    rw [← deduction]
    let Δ := Γ ⊓ m ∈ᴮ bSet.omega
    have Hpair : Δ ≤ pair m (blockValue Tail m) ∈ᴮ Tail :=
      graphValue_pair_mem (inf_le_left.trans HTail) inf_le_right
    have Hlarge : Δ ≤ colarge omegaOne J (tailChoiceSet color R E Tail m) :=
      laterSurvivors_colarge (inf_le_left.trans (HJ.trans inf_le_left))
        (inf_le_left.trans Hclosure) (inf_le_left.trans HE)
        (inf_le_left.trans HTail) (inf_le_left.trans Htail) Hpair
    obtain ⟨w, Hw⟩ := exists_mem_of_colarge (inf_le_left.trans HJ) Hlarge
    exact le_iSup_of_le w (le_inf (mem_of_mem_subset laterSurvivors_subset Hw) Hw)
  obtain ⟨v, Hv⟩ := exists_selector_of_pointwise
    (fun w => tailChoiceSet_mem_ext_index color R E Tail w) (fun _ => B_ext_mem_left) Hpointwise
  refine ⟨v, le_inf (Hv.trans inf_le_left) ?_⟩
  apply le_iInf
  intro m
  apply le_iInf
  intro b
  apply le_iInf
  intro w
  rw [← deduction]
  let Δ := Γ ⊓ (pair m b ∈ᴮ Tail ⊓ pair m w ∈ᴮ v)
  have Hmb : Δ ≤ pair m b ∈ᴮ Tail := inf_le_right.trans inf_le_left
  have Hm : Δ ≤ m ∈ᴮ bSet.omega := mem_domain_of_is_function Hmb (inf_le_left.trans HTail)
  have Hw : Δ ≤ w ∈ᴮ tailChoiceSet color R E Tail m :=
    (le_inf (inf_le_left.trans ((Hv.trans inf_le_right).trans
      ((iInf_le _ m).trans (iInf_le _ w))))
      (le_inf Hm (inf_le_right.trans inf_le_right))).trans bv_imp_elim
  have Hb : Δ ≤ blockValue Tail m =ᴮ b := graphValue_eq_of_pair (inf_le_left.trans HTail) Hmb
  exact mem_congr bv_refl (laterSurvivors_congr_object color R E Tail m Hb) Hw

/-- Two actual coherent selections are produced at precisely the
original condition. Their full guarded laws retain the selected whole
objects and the same canonical enumeration. -/
theorem exists_survivor_coordinates
    {color : Bool} {R J E S Blocks X Tail : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ properIdeal omegaOne J) (Hclosure : Γ ≤ countableClosure J)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HBlocks : Γ ≤ is_function omegaOne (bv_powerset omegaTwo) Blocks)
    (HB : Γ ≤ image omegaOne (bv_powerset omegaTwo) Blocks ⊆ᴮ blockObjects color R)
    (HTail : Γ ≤ is_function bSet.omega (bv_powerset omegaTwo) Tail)
    (Htail : Γ ≤ tailCandidatesLaw color R J E S
      (image omegaOne (bv_powerset omegaTwo) Blocks) Tail)
    (Hmasks : Γ ≤ ⨅ ν, _root_.imp (ν ∈ᴮ omegaOne) (colarge omegaOne J (activeMask X ν))) :
    ∃ u v : bSet 𝔹, Γ ≤ is_function omegaOne omegaOne u ⊓
      (is_function bSet.omega omegaOne v ⊓
        (oldCoordinateLaw color R E Tail Blocks X u ⊓ tailCoordinateLaw color R E Tail v)) := by
  obtain ⟨u, Hu⟩ := exists_old_survivor_coordinates HJ Hclosure HE HBlocks HB HTail Htail Hmasks
  obtain ⟨v, Hv⟩ := exists_tail_survivor_coordinates HJ Hclosure HE HTail Htail
  exact ⟨u, v, le_inf (Hu.trans inf_le_left) (le_inf (Hv.trans inf_le_left)
    (le_inf (Hu.trans inf_le_right) (Hv.trans inf_le_right)))⟩

end bSet.ErdosTailSurvivorSelection
