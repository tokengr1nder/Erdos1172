/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSimultaneousRunStopping
public import Erdos1172.Part4InternalSimultaneousRunLaws

@[expose] public section

/-!
# Active row coordinates belong to every decoded vertex section

Success is unnecessary for this common-row conclusion. If a target vertex
is the endpoint, its section is the seed section, satisfied by every row
value. Otherwise, comparing its stage with the active value's stage uses
the earlier-section law, the current active constraint, or the old active
triangle constraint. All case splits are internal Boolean splits.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousRun

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosSimultaneousHistory

/-- An active row value satisfies every decoded vertex section, even when
the target vertex is the sentinel. Neither full totality nor success is
needed once the relevant actual decoded pairs are given. -/
theorem active_coordinate_mem_section_of_run
    {color : Bool} {R S top P i σ v j y A : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hσi : Γ ≤ σ ∈ᴮ i)
    (Hcoord : Γ ≤ pair (pair i σ) v ∈ᴮ coordinateHistory P)
    (Hvertex : Γ ≤ pair j y ∈ᴮ vertexHistory P)
    (Hsection : Γ ≤ pair (pair σ y) A ∈ᴮ S) : Γ ≤ v ∈ᴮ A := by
  calc
    Γ = (Γ ⊓ y =ᴮ top) ⊔ (Γ ⊓ (y =ᴮ top)ᶜ) := by
      rw [← inf_sup_left, sup_compl_eq_top, inf_top_eq]
    _ ≤ v ∈ᴮ A := by
      apply sup_le
      · have Hseed : Γ ⊓ y =ᴮ top ≤ pair (pair σ top) A ∈ᴮ S :=
          mem_congr (pair_congr (pair_congr bv_refl inf_le_right) bv_refl)
            bv_refl (inf_le_left.trans Hsection)
        exact coordinate_mem_seed_of_run (inf_le_left.trans Hlaw)
          (inf_le_left.trans Hcoord) Hseed
      · let Δ := Γ ⊓ (y =ᴮ top)ᶜ
        have HΔ : Δ ≤ Γ := inf_le_left
        have Hne : Δ ≤ (y =ᴮ top)ᶜ := inf_le_right
        have Hi : Δ ≤ i ∈ᴮ omegaOne :=
          HΔ.trans (coordinateHistory_pair_iff.mp Hcoord).1
        have Hj : Δ ≤ j ∈ᴮ omegaOne :=
          HΔ.trans (mem_vertexHistory_iff.mp Hvertex).1
        have Hcases := epsilon_trichotomy_of_Ord Hj Hi omegaOne_Ord
        apply (le_inf (le_refl Δ) Hcases).trans
        rw [inf_sup_left, inf_sup_left]
        apply sup_le
        · apply sup_le
          · have Hbase : Δ ⊓ j =ᴮ i ≤ Γ := inf_le_left.trans HΔ
            have Hcurrent : Δ ⊓ j =ᴮ i ≤ pair i y ∈ᴮ vertexHistory P :=
              mem_congr (pair_congr inf_le_right bv_refl) bv_refl (Hbase.trans Hvertex)
            exact nonstop_stage_current_active_section (Hbase.trans Hlaw) Hcurrent
              (inf_le_left.trans Hne) (Hbase.trans Hσi) (Hbase.trans Hcoord)
              (Hbase.trans Hsection)
          · have Hbase : Δ ⊓ j ∈ᴮ i ≤ Γ := inf_le_left.trans HΔ
            exact coordinate_mem_previous_section_of_run (Hbase.trans Hlaw)
              (Hbase.trans Hcoord) inf_le_right (Hbase.trans Hvertex)
              (Hbase.trans Hsection)
        · have Hbase : Δ ⊓ i ∈ᴮ j ≤ Γ := inf_le_left.trans HΔ
          exact nonstop_stage_old_active_section (Hbase.trans Hlaw) (Hbase.trans Hvertex)
            (inf_le_left.trans Hne) inf_le_right (Hbase.trans Hσi)
            (Hbase.trans Hcoord) (Hbase.trans Hsection)

/-- A single active coordinate obeys the full internally quantified
common-section law, with arbitrary target stages and section names. -/
theorem active_coordinate_mem_all_sections_of_run
    {color : Bool} {R S top P i σ v : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hσi : Γ ≤ σ ∈ᴮ i)
    (Hcoord : Γ ≤ pair (pair i σ) v ∈ᴮ coordinateHistory P) :
    Γ ≤ ⨅ j, ⨅ y, ⨅ A, _root_.imp
      (pair j y ∈ᴮ vertexHistory P ⊓ pair (pair σ y) A ∈ᴮ S) (v ∈ᴮ A) := by
  apply le_iInf
  intro j
  apply le_iInf
  intro y
  apply le_iInf
  intro A
  rw [← deduction]
  exact active_coordinate_mem_section_of_run (inf_le_left.trans Hlaw)
    (inf_le_left.trans Hσi) (inf_le_left.trans Hcoord)
    (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)

/-- Any actual set whose members have internally witnessed active stages
is a common row set. Witnesses may be mixed names and need not be chosen
as an external enumeration or a separately supplied function. -/
theorem common_row_values_of_active_values
    {color : Bool} {R S top P σ C : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hactive : Γ ≤ ⨅ v, _root_.imp (v ∈ᴮ C)
      (⨆ i, σ ∈ᴮ i ⊓ pair (pair i σ) v ∈ᴮ coordinateHistory P)) :
    Γ ≤ ⨅ v, _root_.imp (v ∈ᴮ C)
      (⨅ j, ⨅ y, ⨅ A, _root_.imp
        (pair j y ∈ᴮ vertexHistory P ⊓ pair (pair σ y) A ∈ᴮ S) (v ∈ᴮ A)) := by
  apply le_iInf
  intro v
  rw [← deduction]
  have Hex : Γ ⊓ v ∈ᴮ C ≤
      ⨆ i, σ ∈ᴮ i ⊓ pair (pair i σ) v ∈ᴮ coordinateHistory P :=
    (le_inf (inf_le_left.trans (Hactive.trans (iInf_le _ v))) inf_le_right).trans
      bv_imp_elim
  obtain ⟨i, Hi⟩ := exists_convert Hex
    (B_ext_inf B_ext_mem_right (B_ext_pair_left B_ext_pair_mem_left))
  exact active_coordinate_mem_all_sections_of_run (inf_le_left.trans Hlaw)
    (Hi.trans inf_le_left) (Hi.trans inf_le_right)

/-- Subset form of the common-row law, suitable for comparing the actual
active tail with a canonical intersection of all decoded sections. -/
theorem common_row_of_active_values
    {color : Bool} {R S top P σ C : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hactive : Γ ≤ ⨅ v, _root_.imp (v ∈ᴮ C)
      (⨆ i, σ ∈ᴮ i ⊓ pair (pair i σ) v ∈ᴮ coordinateHistory P)) :
    Γ ≤ ⨅ j, ⨅ y, ⨅ A, _root_.imp
      (pair j y ∈ᴮ vertexHistory P ⊓ pair (pair σ y) A ∈ᴮ S) (C ⊆ᴮ A) := by
  have Hvalues := common_row_values_of_active_values Hlaw Hactive
  apply le_iInf
  intro j
  apply le_iInf
  intro y
  apply le_iInf
  intro A
  rw [← deduction, subset_unfold']
  apply le_iInf
  intro v
  rw [← deduction]
  let Δ := (Γ ⊓ (pair j y ∈ᴮ vertexHistory P ⊓ pair (pair σ y) A ∈ᴮ S)) ⊓ v ∈ᴮ C
  have Hbase : Δ ≤ Γ := inf_le_left.trans inf_le_left
  have Hall : Δ ≤ ⨅ k, ⨅ z, ⨅ B, _root_.imp
      (pair k z ∈ᴮ vertexHistory P ⊓ pair (pair σ z) B ∈ᴮ S) (v ∈ᴮ B) :=
    (le_inf (Hbase.trans (Hvalues.trans (iInf_le _ v))) inf_le_right).trans bv_imp_elim
  exact (le_inf (Hall.trans ((iInf_le _ j).trans ((iInf_le _ y).trans (iInf_le _ A))))
    (inf_le_left.trans inf_le_right)).trans bv_imp_elim

end bSet.ErdosSimultaneousRun
