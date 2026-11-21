/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionSeedBridge
public import Erdos1172.Part4InternalBirthGreedyRange

@[expose] public section

/-!
# Literal birth-masked whole-block sections

The full family has value omega-one at and before the birth, and the
actual whole-block section afterward. It is an actual supported function.
On an activated prefix its exact candidate set agrees with the original
fusion candidate set, including every recorded earlier coordinate.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionBirthSections

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosFusionRowCandidates ErdosRelationGraph
open ErdosColargeIntersection ErdosGreedyPartial ErdosRowCandidates
open ErdosSimultaneousTraces ErdosBlockCandidate

def birthSection (color : Bool) (R E b Blocks ν j : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun v => _root_.imp (ν ∈ᴮ j)
    (sectionRequirement color R E b Blocks j v)) omegaOne

theorem mem_birthSection_iff
    {color : Bool} {R E b Blocks ν j v : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ v ∈ᴮ birthSection color R E b Blocks ν j ↔
      Γ ≤ v ∈ᴮ omegaOne ∧ Γ ≤ _root_.imp (ν ∈ᴮ j) (sectionRequirement color R E b Blocks j v) :=
  mem_comprehend_and (B_ext_imp (h₁ := B_ext_const)
    (h₂ := sectionRequirement_ext_coordinate color R E b Blocks j))

theorem birthSection_subset
    {color : Bool} {R E b Blocks ν j : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ birthSection color R E b Blocks ν j ⊆ᴮ omegaOne :=
  comprehend_subset (ϕ := fun v => _root_.imp (ν ∈ᴮ j)
    (sectionRequirement color R E b Blocks j v)) omegaOne

theorem birthSection_congr_stage (color : Bool) (R E b Blocks ν : bSet 𝔹) :
    B_congr (birthSection color R E b Blocks ν) := by
  intro j k Γ Hjk
  have Hext (v : bSet 𝔹) : B_ext (fun t => _root_.imp (ν ∈ᴮ t)
      (sectionRequirement color R E b Blocks t v)) :=
    B_ext_imp (h₁ := B_ext_mem_right) (h₂ := sectionRequirement_ext_stage color R E b Blocks v)
  apply mem_ext
  · apply le_iInf
    intro v
    rw [← deduction]
    have Hv := mem_birthSection_iff.mp
      (show Γ ⊓ v ∈ᴮ birthSection color R E b Blocks ν j ≤
        v ∈ᴮ birthSection color R E b Blocks ν j from inf_le_right)
    exact mem_birthSection_iff.mpr ⟨Hv.1, bv_rw'' (inf_le_left.trans Hjk) Hv.2 (Hext v)⟩
  · apply le_iInf
    intro v
    rw [← deduction]
    have Hv := mem_birthSection_iff.mp
      (show Γ ⊓ v ∈ᴮ birthSection color R E b Blocks ν k ≤
        v ∈ᴮ birthSection color R E b Blocks ν k from inf_le_right)
    exact mem_birthSection_iff.mpr ⟨Hv.1,
      bv_rw' (inf_le_left.trans Hjk) (h_congr := Hext v) (H_new := Hv.2)⟩

theorem birthSection_eq_active
    {color : Bool} {R E b Blocks ν j : bSet 𝔹} {Γ : 𝔹}
    (Hactive : Γ ≤ ν ∈ᴮ j) :
    Γ ≤ birthSection color R E b Blocks ν j =ᴮ fusionSection color R E b Blocks j := by
  apply mem_ext
  · apply le_iInf
    intro v
    rw [← deduction]
    have Hv := mem_birthSection_iff.mp
      (show Γ ⊓ v ∈ᴮ birthSection color R E b Blocks ν j ≤
        v ∈ᴮ birthSection color R E b Blocks ν j from inf_le_right)
    exact mem_fusionSection_iff.mpr
      ⟨Hv.1, (le_inf Hv.2 (inf_le_left.trans Hactive)).trans bv_imp_elim⟩
  · apply le_iInf
    intro v
    rw [← deduction]
    have Hv := mem_fusionSection_iff.mp
      (show Γ ⊓ v ∈ᴮ fusionSection color R E b Blocks j ≤
        v ∈ᴮ fusionSection color R E b Blocks j from inf_le_right)
    apply mem_birthSection_iff.mpr
    refine ⟨Hv.1, ?_⟩
    rw [← deduction]
    exact inf_le_left.trans Hv.2

theorem birthSection_eq_inactive
    {color : Bool} {R E b Blocks ν j : bSet 𝔹} {Γ : 𝔹}
    (Hinactive : Γ ≤ (ν ∈ᴮ j)ᶜ) :
    Γ ≤ birthSection color R E b Blocks ν j =ᴮ omegaOne := by
  apply subset_ext birthSection_subset
  rw [subset_unfold']
  apply le_iInf
  intro v
  rw [← deduction]
  apply mem_birthSection_iff.mpr
  refine ⟨inf_le_right, ?_⟩
  rw [← deduction]
  exact (bv_absurd _ inf_le_right (inf_le_left.trans (inf_le_left.trans Hinactive))).trans bot_le

def birthSectionFamily (color : Bool) (R E b Blocks ν : bSet 𝔹) : bSet 𝔹 :=
  relationGraph omegaOne (bv_powerset omegaOne)
    (fun j A => A =ᴮ birthSection color R E b Blocks ν j)

private theorem family_ext_left (color : Bool) (R E b Blocks ν A : bSet 𝔹) :
    B_ext (fun j => A =ᴮ birthSection color R E b Blocks ν j) :=
  B_ext_term (ϕ := fun C => A =ᴮ C) (t := birthSection color R E b Blocks ν)
    B_ext_bv_eq_right (birthSection_congr_stage color R E b Blocks ν)

theorem mem_birthSectionFamily_iff
    {color : Bool} {R E b Blocks ν j A : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair j A ∈ᴮ birthSectionFamily color R E b Blocks ν ↔
      Γ ≤ j ∈ᴮ omegaOne ∧ Γ ≤ A ∈ᴮ bv_powerset omegaOne ∧
        Γ ≤ A =ᴮ birthSection color R E b Blocks ν j :=
  mem_relationGraph_iff (family_ext_left color R E b Blocks ν) (fun _ => B_ext_bv_eq_left)

theorem birthSectionFamily_is_function
    {color : Bool} {R E b Blocks ν : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ is_function omegaOne (bv_powerset omegaOne) (birthSectionFamily color R E b Blocks ν) := by
  apply relationGraph_is_function (family_ext_left color R E b Blocks ν) (fun _ => B_ext_bv_eq_left)
  · apply le_iInf
    intro j
    rw [← deduction]
    exact le_iSup_of_le (birthSection color R E b Blocks ν j)
      (le_inf (mem_powerset_iff.mpr birthSection_subset) bv_refl)
  · intro j k A B Δ _ _ _ _ _ HA HB Hjk
    exact bv_trans HA (bv_trans (birthSection_congr_stage color R E b Blocks ν Hjk) (bv_symm HB))

theorem birthSectionFamily_colarge_values
    {color : Bool} {R J E b Blocks ν : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J)
    (Hsections : Γ ≤ ⨅ j, _root_.imp (j ∈ᴮ omegaOne ⊓ ν ∈ᴮ j)
      (colarge omegaOne J (fusionSection color R E b Blocks j))) :
    Γ ≤ ⨅ j, ⨅ A, _root_.imp
      (j ∈ᴮ omegaOne ⊓ pair j A ∈ᴮ birthSectionFamily color R E b Blocks ν)
      (colarge omegaOne J A) := by
  apply le_iInf
  intro j
  apply le_iInf
  intro A
  rw [← deduction]
  let Δ := Γ ⊓ (j ∈ᴮ omegaOne ⊓ pair j A ∈ᴮ birthSectionFamily color R E b Blocks ν)
  have Hdata := mem_birthSectionFamily_iff.mp
    (show Δ ≤ pair j A ∈ᴮ birthSectionFamily color R E b Blocks ν from
      inf_le_right.trans inf_le_right)
  have Hmasked : Δ ≤ colarge omegaOne J (birthSection color R E b Blocks ν j) := by
    apply (le_inf le_rfl (show Δ ≤ (ν ∈ᴮ j) ⊔ (ν ∈ᴮ j)ᶜ from by simp)).trans
    rw [inf_sup_left]
    apply sup_le
    · have Hsection : Δ ⊓ ν ∈ᴮ j ≤ colarge omegaOne J (fusionSection color R E b Blocks j) :=
        (le_inf (inf_le_left.trans (inf_le_left.trans (Hsections.trans (iInf_le _ j))))
          (le_inf (inf_le_left.trans Hdata.1) inf_le_right)).trans bv_imp_elim
      exact bv_rw' (ϕ := colarge omegaOne J) (birthSection_eq_active inf_le_right)
        (h_congr := colarge_ext_common omegaOne J) (H_new := Hsection)
    · exact bv_rw' (ϕ := colarge omegaOne J) (birthSection_eq_inactive inf_le_right)
        (h_congr := colarge_ext_common omegaOne J)
        (H_new := ErdosSeedBlock.colarge_self_of_isIdeal (inf_le_left.trans (inf_le_left.trans HJ)))
  exact bv_rw' (ϕ := colarge omegaOne J) Hdata.2.2
    (h_congr := colarge_ext_common omegaOne J) (H_new := Hmasked)

private theorem admissible_of_guarded_pairs
    {δ seed F G h k v : bSet 𝔹} {Γ : 𝔹}
    (HF : ∀ j A Δ, Δ ≤ Γ → Δ ≤ j ∈ᴮ δ → Δ ≤ pair j A ∈ᴮ G → Δ ≤ pair j A ∈ᴮ F)
    (Hh : ∀ j w Δ, Δ ≤ Γ → Δ ≤ j ∈ᴮ δ → Δ ≤ pair j w ∈ᴮ k → Δ ≤ pair j w ∈ᴮ h)
    (Hv : Γ ≤ rowAdmissible δ seed F h v) :
    Γ ≤ rowAdmissible δ seed G k v := by
  refine le_inf (Hv.trans inf_le_left)
    (le_inf (Hv.trans (inf_le_right.trans inf_le_left)) (le_inf ?_ ?_))
  · apply le_iInf
    intro j
    apply le_iInf
    intro A
    rw [← deduction]
    exact (le_inf (inf_le_left.trans (Hv.trans
      ((inf_le_right.trans (inf_le_right.trans inf_le_left)).trans
        ((iInf_le _ j).trans (iInf_le _ A)))))
      (le_inf (inf_le_right.trans inf_le_left)
        (HF j A _ inf_le_left (inf_le_right.trans inf_le_left)
          (inf_le_right.trans inf_le_right)))).trans bv_imp_elim
  · apply le_iInf
    intro j
    apply le_iInf
    intro w
    rw [← deduction]
    exact (le_inf (inf_le_left.trans (Hv.trans
      ((inf_le_right.trans (inf_le_right.trans inf_le_right)).trans
        ((iInf_le _ j).trans (iInf_le _ w)))))
      (le_inf (inf_le_right.trans inf_le_left)
        (Hh j w _ inf_le_left (inf_le_right.trans inf_le_left)
          (inf_le_right.trans inf_le_right)))).trans bv_imp_elim

/-- Exact equality, not just inclusion: all active previous sections
and coordinates, including failed intermediate stages, are preserved. -/
theorem birth_rowCandidates_eq_fusion
    {color : Bool} {R E b top Blocks X ξ ν : bSet 𝔹} {Γ : 𝔹}
    (HX : Γ ≤ is_func' (prod omegaOne omegaOne) omegaOne X)
    (Hξ : Γ ≤ ξ ⊆ᴮ omegaOne) (Hν : Γ ≤ ν ∈ᴮ omegaOne) :
    Γ ≤ rowCandidates (activatedStages ξ ν) (fusionSeed color R E b top)
      (birthSectionFamily color R E b Blocks ν) (rowHistory omegaOne X ν) =ᴮ
      fusionRowCandidates color R E b top ξ ν Blocks X := by
  have HXξ := is_func'_subset_of_is_func' HX (ErdosPartialInjection.prod_domain_mono Hξ)
  have Hleft : Γ ≤ is_func' (activatedStages ξ ν) omegaOne (rowHistory omegaOne X ν) :=
    is_func'_subset_of_is_func'
    (is_func'_of_is_function (rowHistory_is_function HX Hν))
    (subset_trans' activatedStages_subset Hξ)
  have Hright := activated_rowHistory_is_func' HXξ Hν
  have Hfamilies (j A : bSet 𝔹) (Δ : 𝔹) (HΔ : Δ ≤ Γ)
      (Hj : Δ ≤ j ∈ᴮ activatedStages ξ ν) :
      (Δ ≤ pair j A ∈ᴮ birthSectionFamily color R E b Blocks ν) ↔
        Δ ≤ pair j A ∈ᴮ fusionSectionFamily color R E b Blocks ξ := by
    have Hactive := mem_activatedStages_iff.mp Hj
    have Heq := birthSection_eq_active (color := color) (R := R) (E := E)
      (b := b) (Blocks := Blocks) Hactive.2
    constructor
    · intro Hpair
      have Hdata := mem_birthSectionFamily_iff.mp Hpair
      exact mem_fusionSectionFamily_iff.mpr ⟨Hactive.1, Hdata.2.1, bv_trans Hdata.2.2 Heq⟩
    · intro Hpair
      have Hdata := mem_fusionSectionFamily_iff.mp Hpair
      exact mem_birthSectionFamily_iff.mpr
        ⟨mem_of_mem_subset (HΔ.trans Hξ) Hactive.1, Hdata.2.1, bv_trans Hdata.2.2 (bv_symm Heq)⟩
  have Hrows (j v : bSet 𝔹) (Δ : 𝔹) (HΔ : Δ ≤ Γ)
      (Hj : Δ ≤ j ∈ᴮ activatedStages ξ ν) :
      (Δ ≤ pair j v ∈ᴮ rowHistory omegaOne X ν) ↔ Δ ≤ pair j v ∈ᴮ rowHistory ξ X ν := by
    have Hjξ := (mem_activatedStages_iff.mp Hj).1
    constructor
    · intro Hpair
      have Hdata := mem_rowHistory_iff.mp Hpair
      exact mem_rowHistory_iff.mpr ⟨Hjξ, Hdata.2.1, Hdata.2.2⟩
    · intro Hpair
      have Hdata := mem_rowHistory_iff.mp Hpair
      exact mem_rowHistory_iff.mpr ⟨mem_of_mem_subset (HΔ.trans Hξ) Hjξ, Hdata.2.1, Hdata.2.2⟩
  apply mem_ext
  · apply le_iInf
    intro v
    rw [← deduction]
    apply (mem_rowCandidates_iff (inf_le_left.trans Hright)).mpr
    exact admissible_of_guarded_pairs
      (fun j A Δ HΔ Hj Hpair => (Hfamilies j A Δ (HΔ.trans inf_le_left) Hj).mpr Hpair)
      (fun j w Δ HΔ Hj Hpair => (Hrows j w Δ (HΔ.trans inf_le_left) Hj).mpr Hpair)
      ((mem_rowCandidates_iff (inf_le_left.trans Hleft)).mp inf_le_right)
  · apply le_iInf
    intro v
    rw [← deduction]
    apply (mem_rowCandidates_iff (inf_le_left.trans Hleft)).mpr
    exact admissible_of_guarded_pairs
      (fun j A Δ HΔ Hj Hpair => (Hfamilies j A Δ (HΔ.trans inf_le_left) Hj).mp Hpair)
      (fun j w Δ HΔ Hj Hpair => (Hrows j w Δ (HΔ.trans inf_le_left) Hj).mp Hpair)
      ((mem_rowCandidates_iff (inf_le_left.trans Hright)).mp inf_le_right)

end bSet.ErdosFusionBirthSections
