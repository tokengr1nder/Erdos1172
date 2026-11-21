/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSimultaneousCandidates
public import Erdos1172.Part4InternalSimultaneousTraces

@[expose] public section

/-!
The direct simultaneous constraints define exactly the ordinary row
candidate set formed from the actual section and coordinate traces.
Consequently every countable stage has a co-large candidate set and an
actual least member. The ideal and section-value hypotheses are row-specific;
there is no assumed successful run, global family of chosen values, or CH.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousCandidates

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosPartition ErdosRowCandidates
open ErdosOrdinalLeast ErdosColargeIntersection ErdosSimultaneousTraces

theorem mem_simultaneousCandidates_iff_rowCandidates
    {δ S Y X top σ seed v : bSet 𝔹} {Γ : 𝔹}
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (HY : Γ ≤ is_func' δ omegaTwo Y)
    (HX : Γ ≤ is_func' (prod δ omegaOne) omegaOne X)
    (Hσ : Γ ≤ σ ∈ᴮ omegaOne) (Hseed : Γ ≤ pair (pair σ top) seed ∈ᴮ S) :
    (Γ ≤ v ∈ᴮ simultaneousCandidates δ S Y X top σ) ↔
      Γ ≤ v ∈ᴮ rowCandidates δ seed (sectionTrace δ S Y σ) (rowHistory δ X σ) := by
  have Hhistory : Γ ≤ is_func' δ omegaOne (rowHistory δ X σ) :=
    (rowHistory_is_function HX Hσ).trans inf_le_left
  rw [mem_rowCandidates_iff Hhistory]
  constructor
  · intro Hv
    refine le_inf (mem_simultaneousCandidates_iff.mp Hv).1
      (le_inf (simultaneousCandidate_mem_seed Hv Hseed) (le_inf ?_ ?_))
    · apply le_iInf
      intro j
      apply le_iInf
      intro A
      rw [← deduction]
      let Δ := Γ ⊓ (j ∈ᴮ δ ⊓ pair j A ∈ᴮ sectionTrace δ S Y σ)
      obtain ⟨y, Hjy, HyA⟩ := sectionTrace_witness
        (show Δ ≤ pair j A ∈ᴮ sectionTrace δ S Y σ from inf_le_right.trans inf_le_right)
      exact simultaneousCandidate_mem_previous_section (inf_le_left.trans Hv)
        (inf_le_right.trans inf_le_left) Hjy HyA
    · apply le_iInf
      intro j
      apply le_iInf
      intro w
      rw [← deduction]
      exact simultaneousCandidate_above_previous (inf_le_left.trans Hv)
        (inf_le_right.trans inf_le_left)
        (rowHistory_apply (inf_le_right.trans inf_le_right))
  · intro Hv
    have Hvω : Γ ≤ v ∈ᴮ omegaOne := Hv.trans inf_le_left
    have Hvseed : Γ ≤ v ∈ᴮ seed := Hv.trans (inf_le_right.trans inf_le_left)
    have Hvsections : Γ ≤ ⨅ j, ⨅ A, _root_.imp
        (j ∈ᴮ δ ⊓ pair j A ∈ᴮ sectionTrace δ S Y σ) (v ∈ᴮ A) :=
      Hv.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
    have Hvprevious : Γ ≤ ⨅ j, ⨅ w, _root_.imp
        (j ∈ᴮ δ ⊓ pair j w ∈ᴮ rowHistory δ X σ) (w ∈ᴮ v) :=
      Hv.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
    apply mem_simultaneousCandidates_iff.mpr
    refine ⟨Hvω, le_inf ?_ (le_inf ?_ ?_)⟩
    · apply le_iInf
      intro A
      rw [← deduction]
      have HseedA : Γ ⊓ pair (pair σ top) A ∈ᴮ S ≤ seed =ᴮ A :=
        eq_of_is_func_of_eq (inf_le_left.trans (HS.trans inf_le_left)) bv_refl
          (inf_le_left.trans Hseed) inf_le_right
      exact mem_congr bv_refl HseedA (inf_le_left.trans Hvseed)
    · apply le_iInf
      intro j
      apply le_iInf
      intro y
      apply le_iInf
      intro A
      rw [← deduction]
      let Δ := Γ ⊓ (j ∈ᴮ δ ⊓ (pair j y ∈ᴮ Y ⊓ pair (pair σ y) A ∈ᴮ S))
      have HjA : Δ ≤ pair j A ∈ᴮ sectionTrace δ S Y σ :=
        (sectionTrace_pair_iff (inf_le_left.trans HY) (inf_le_left.trans HS)
          (inf_le_left.trans Hσ) (inf_le_right.trans inf_le_left)
          (inf_le_right.trans (inf_le_right.trans inf_le_left))).mpr
          (inf_le_right.trans (inf_le_right.trans inf_le_right))
      exact (le_inf (inf_le_left.trans
        (Hvsections.trans ((iInf_le _ j).trans (iInf_le _ A))))
        (le_inf (inf_le_right.trans inf_le_left) HjA)).trans bv_imp_elim
    · apply le_iInf
      intro j
      apply le_iInf
      intro w
      rw [← deduction]
      let Δ := Γ ⊓ (j ∈ᴮ δ ⊓ pair (pair j σ) w ∈ᴮ X)
      have Hjw : Δ ≤ pair j w ∈ᴮ rowHistory δ X σ :=
        (rowHistory_pair_iff (inf_le_left.trans HX) (inf_le_left.trans Hσ)
          (inf_le_right.trans inf_le_left)).mpr (inf_le_right.trans inf_le_right)
      exact (le_inf (inf_le_left.trans
        (Hvprevious.trans ((iInf_le _ j).trans (iInf_le _ w))))
        (le_inf (inf_le_right.trans inf_le_left) Hjw)).trans bv_imp_elim

/-- Exact local equality. A known seed value and functionality suffice;
the endpoint does not itself need a separate membership hypothesis. -/
theorem simultaneousCandidates_eq_rowCandidates
    {δ S Y X top σ seed : bSet 𝔹} {Γ : 𝔹}
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (HY : Γ ≤ is_func' δ omegaTwo Y)
    (HX : Γ ≤ is_func' (prod δ omegaOne) omegaOne X)
    (Hσ : Γ ≤ σ ∈ᴮ omegaOne) (Hseed : Γ ≤ pair (pair σ top) seed ∈ᴮ S) :
    Γ ≤ simultaneousCandidates δ S Y X top σ =ᴮ
      rowCandidates δ seed (sectionTrace δ S Y σ) (rowHistory δ X σ) := by
  apply mem_ext
  · apply le_iInf
    intro v
    rw [← deduction]
    exact (mem_simultaneousCandidates_iff_rowCandidates
      (inf_le_left.trans HS) (inf_le_left.trans HY) (inf_le_left.trans HX)
      (inf_le_left.trans Hσ) (inf_le_left.trans Hseed)).mp inf_le_right
  · apply le_iInf
    intro v
    rw [← deduction]
    exact (mem_simultaneousCandidates_iff_rowCandidates
      (inf_le_left.trans HS) (inf_le_left.trans HY) (inf_le_left.trans HX)
      (inf_le_left.trans Hσ) (inf_le_left.trans Hseed)).mpr inf_le_right

/-- Only values at the chosen row are needed to control its trace. -/
theorem sectionTrace_row_colarge_values {δ S Y σ J : bSet 𝔹} {Γ : 𝔹}
    (HY : Γ ≤ is_func' δ omegaTwo Y)
    (Hvalues : Γ ≤ ⨅ y, ⨅ A, _root_.imp
      (y ∈ᴮ omegaTwo ⊓ pair (pair σ y) A ∈ᴮ S) (colarge omegaOne J A)) :
    Γ ≤ ⨅ j, ⨅ A, _root_.imp
      (j ∈ᴮ δ ⊓ pair j A ∈ᴮ sectionTrace δ S Y σ) (colarge omegaOne J A) := by
  apply le_iInf
  intro j
  apply le_iInf
  intro A
  rw [← deduction]
  let Δ := Γ ⊓ (j ∈ᴮ δ ⊓ pair j A ∈ᴮ sectionTrace δ S Y σ)
  obtain ⟨y, Hjy, HyA⟩ := sectionTrace_witness
    (show Δ ≤ pair j A ∈ᴮ sectionTrace δ S Y σ from inf_le_right.trans inf_le_right)
  have Hy : Δ ≤ y ∈ᴮ omegaTwo := value_mem_codomain
    (inf_le_left.trans HY) (inf_le_right.trans inf_le_left) Hjy
  exact (le_inf (inf_le_left.trans (Hvalues.trans ((iInf_le _ y).trans (iInf_le _ A))))
    (le_inf Hy HyA)).trans bv_imp_elim

theorem simultaneousCandidates_colarge {J δ S Y X top σ : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J) (Hδ : Γ ≤ δ ∈ᴮ omegaOne)
    (Htop : Γ ≤ top ∈ᴮ omegaTwo)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (HY : Γ ≤ is_func' δ omegaTwo Y)
    (HX : Γ ≤ is_func' (prod δ omegaOne) omegaOne X)
    (Hσ : Γ ≤ σ ∈ᴮ omegaOne)
    (Hvalues : Γ ≤ ⨅ y, ⨅ A, _root_.imp
      (y ∈ᴮ omegaTwo ⊓ pair (pair σ y) A ∈ᴮ S) (colarge omegaOne J A)) :
    Γ ≤ colarge omegaOne J (simultaneousCandidates δ S Y X top σ) := by
  have HseedEx : Γ ≤ ⨆ A, A ∈ᴮ bv_powerset omegaOne ⊓ pair (pair σ top) A ∈ᴮ S :=
    (le_inf ((HS.trans inf_le_right).trans (iInf_le _ (pair σ top)))
      (mem_prod_iff.mpr ⟨Hσ, Htop⟩)).trans bv_imp_elim
  obtain ⟨seed, Hseed⟩ := exists_convert HseedEx (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have HseedColarge : Γ ≤ colarge omegaOne J seed :=
    (le_inf (Hvalues.trans ((iInf_le _ top).trans (iInf_le _ seed)))
      (le_inf Htop (Hseed.trans inf_le_right))).trans bv_imp_elim
  have HtraceValues := sectionTrace_row_colarge_values HY Hvalues
  have HtraceSmall : Γ ≤ ⨅ j, ⨅ A, _root_.imp
      (j ∈ᴮ δ ⊓ pair j A ∈ᴮ sectionTrace δ S Y σ) (difference omegaOne A ∈ᴮ J) := by
    apply le_iInf
    intro j
    apply le_iInf
    intro A
    rw [← deduction]
    exact ((le_inf (inf_le_left.trans
      (HtraceValues.trans ((iInf_le _ j).trans (iInf_le _ A)))) inf_le_right).trans
      bv_imp_elim).trans inf_le_right
  have HrowColarge := rowCandidates_colarge HJ Habsorb Hclosure Hδ HseedColarge
    ((sectionTrace_is_function HY HS Hσ).trans inf_le_left) HtraceSmall
    ((rowHistory_is_function HX Hσ).trans inf_le_left)
  have Heq := simultaneousCandidates_eq_rowCandidates HS HY HX Hσ (Hseed.trans inf_le_right)
  exact le_inf simultaneousCandidates_subset
    (mem_congr (bv_symm (difference_congr_right Heq)) bv_refl (HrowColarge.trans inf_le_right))

/-- A least member is produced at the same Boolean condition from the
row-specific ideal data. No candidate-nonemptiness premise is supplied. -/
theorem exists_least_simultaneousCandidate {J δ S Y X top σ : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J) (Hδ : Γ ≤ δ ∈ᴮ omegaOne)
    (Htop : Γ ≤ top ∈ᴮ omegaTwo)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (HY : Γ ≤ is_func' δ omegaTwo Y)
    (HX : Γ ≤ is_func' (prod δ omegaOne) omegaOne X)
    (Hσ : Γ ≤ σ ∈ᴮ omegaOne)
    (Hvalues : Γ ≤ ⨅ y, ⨅ A, _root_.imp
      (y ∈ᴮ omegaTwo ⊓ pair (pair σ y) A ∈ᴮ S) (colarge omegaOne J A)) :
    ∃ v : bSet 𝔹, Γ ≤ colarge omegaOne J (simultaneousCandidates δ S Y X top σ) ⊓
      leastIn (simultaneousCandidates δ S Y X top σ) v := by
  have Hcolarge := simultaneousCandidates_colarge (HJ.trans inf_le_left)
    Habsorb Hclosure Hδ Htop HS HY HX Hσ Hvalues
  have Hnonempty : Γ ≤ (simultaneousCandidates δ S Y X top σ =ᴮ ∅)ᶜ :=
    positive_not_empty (HJ.trans inf_le_left) (colarge_positive HJ Hcolarge)
  obtain ⟨v, Hv⟩ := exists_least_of_nonempty omegaOne_Ord simultaneousCandidates_subset Hnonempty
  exact ⟨v, le_inf Hcolarge Hv⟩

end bSet.ErdosSimultaneousCandidates
