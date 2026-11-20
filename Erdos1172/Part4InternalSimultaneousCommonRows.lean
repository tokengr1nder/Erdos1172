/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalIncreasingTail
public import Erdos1172.Part4InternalSimultaneousRunActiveSections
public import Erdos1172.Part4InternalSimultaneousRunRowRange

@[expose] public section

/-!
The canonical intersection of all decoded vertex sections is co-large
in each supplied normal row ideal. A co-large tail of the actual row
range witnesses this, including when the vertex run has stopped.
No success, CH, common-set premise, or external family of witnesses is
used. This is not a construction of a homogeneous vertex block.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousRun

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosPartition ErdosRelationGraph
open ErdosSimultaneousEntry ErdosSimultaneousHistory ErdosSimultaneousTraces
open ErdosIncreasingTail ErdosGreedyPartial ErdosColargeIntersection

def commonRow (S P σ : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun v => ⨅ j, ⨅ y, ⨅ A, _root_.imp
    (pair j y ∈ᴮ vertexHistory P ⊓ pair (pair σ y) A ∈ᴮ S) (v ∈ᴮ A)) omegaOne

theorem mem_commonRow_iff {S P σ v : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ v ∈ᴮ commonRow S P σ ↔
      Γ ≤ v ∈ᴮ omegaOne ∧ Γ ≤ ⨅ j, ⨅ y, ⨅ A, _root_.imp
        (pair j y ∈ᴮ vertexHistory P ⊓ pair (pair σ y) A ∈ᴮ S) (v ∈ᴮ A) :=
  mem_comprehend_and (B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_mem_left)))))

theorem commonRow_subset {S P σ : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ commonRow S P σ ⊆ᴮ omegaOne :=
  comprehend_subset (ϕ := fun v => ⨅ j, ⨅ y, ⨅ A, _root_.imp
    (pair j y ∈ᴮ vertexHistory P ⊓ pair (pair σ y) A ∈ᴮ S) (v ∈ᴮ A)) omegaOne

theorem commonRow_mem_section {S P σ v j y A : bSet 𝔹} {Γ : 𝔹}
    (Hv : Γ ≤ v ∈ᴮ commonRow S P σ)
    (Hvertex : Γ ≤ pair j y ∈ᴮ vertexHistory P)
    (Hsection : Γ ≤ pair (pair σ y) A ∈ᴮ S) : Γ ≤ v ∈ᴮ A :=
  (le_inf ((mem_commonRow_iff.mp Hv).2.trans
    ((iInf_le _ j).trans ((iInf_le _ y).trans (iInf_le _ A))))
    (le_inf Hvertex Hsection)).trans bv_imp_elim

theorem commonRow_subset_section {S P σ j y A : bSet 𝔹} {Γ : 𝔹}
    (Hvertex : Γ ≤ pair j y ∈ᴮ vertexHistory P)
    (Hsection : Γ ≤ pair (pair σ y) A ∈ᴮ S) : Γ ≤ commonRow S P σ ⊆ᴮ A := by
  rw [subset_unfold']
  apply le_iInf
  intro v
  rw [← deduction]
  exact commonRow_mem_section inf_le_right (inf_le_left.trans Hvertex)
    (inf_le_left.trans Hsection)

theorem commonRow_subset_range_section {S P σ y A : bSet 𝔹} {Γ : 𝔹}
    (Hy : Γ ≤ rangeMem omegaOne (vertexHistory P) y)
    (Hsection : Γ ≤ pair (pair σ y) A ∈ᴮ S) : Γ ≤ commonRow S P σ ⊆ᴮ A := by
  obtain ⟨j, Hj⟩ := exists_convert Hy
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  exact commonRow_subset_section (Hj.trans inf_le_right) Hsection

theorem active_coordinate_mem_commonRow
    {color : Bool} {R S top P i σ v : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R S top P) (Hσi : Γ ≤ σ ∈ᴮ i)
    (Hcoord : Γ ≤ pair (pair i σ) v ∈ᴮ coordinateHistory P) :
    Γ ≤ v ∈ᴮ commonRow S P σ :=
  mem_commonRow_iff.mpr ⟨(coordinateHistory_pair_iff.mp Hcoord).2.2.1,
    active_coordinate_mem_all_sections_of_run Hlaw Hσi Hcoord⟩

/-- This is the tail of the actual decoded row, not a fresh sequence. -/
theorem run_row_tail_subset_commonRow
    {color : Bool} {R S top P σ seed v : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ is_function omegaOne entrySpace P)
    (Hlaw : Γ ≤ runLaw color R S top P)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Hσ : Γ ≤ σ ∈ᴮ omegaOne) (Hseed : Γ ≤ pair (pair σ top) seed ∈ᴮ S)
    (Hσv : Γ ≤ pair σ v ∈ᴮ rowHistory omegaOne (coordinateHistory P) σ) :
    Γ ≤ tailRange (rowHistory omegaOne (coordinateHistory P) σ) v ⊆ᴮ commonRow S P σ := by
  have Hf := is_func'_of_is_function (run_row_is_function HP Hlaw Hσ)
  have Hinc := run_row_increasing HP Hlaw HS Hσ Hseed
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  obtain ⟨i, _, Hσi, Hix⟩ := tailRange_witness (inf_le_left.trans Hf)
    (inf_le_left.trans Hinc) (inf_le_left.trans Hσ) (inf_le_left.trans Hσv) inf_le_right
  exact active_coordinate_mem_commonRow (inf_le_left.trans Hlaw) Hσi (rowHistory_apply Hix)

/-- Normality yields a co-large common set even for a stopped full run. -/
theorem run_commonRow_colarge_of_seed
    {color : Bool} {J R S top P σ seed : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hnormal : Γ ≤ diagonalClosure omegaOne J)
    (HP : Γ ≤ is_function omegaOne entrySpace P)
    (Hlaw : Γ ≤ runLaw color R S top P)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Hσ : Γ ≤ σ ∈ᴮ omegaOne) (Hseed : Γ ≤ pair (pair σ top) seed ∈ᴮ S)
    (HseedColarge : Γ ≤ colarge omegaOne J seed)
    (Hvalues : Γ ≤ ⨅ y, ⨅ A, _root_.imp
      (y ∈ᴮ omegaTwo ⊓ pair (pair σ y) A ∈ᴮ S) (colarge omegaOne J A)) :
    Γ ≤ colarge omegaOne J (commonRow S P σ) := by
  have Hf := is_func'_of_is_function (run_row_is_function HP Hlaw Hσ)
  have Hex : Γ ≤ ⨆ v, v ∈ᴮ omegaOne ⊓
      pair σ v ∈ᴮ rowHistory omegaOne (coordinateHistory P) σ :=
    (le_inf ((Hf.trans inf_le_right).trans (iInf_le _ σ)) Hσ).trans bv_imp_elim
  obtain ⟨v, Hv⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hrange := run_row_range_colarge HJ Habsorb Hclosure Hnormal HP Hlaw HS Hσ
    Hseed HseedColarge Hvalues
  exact colarge_of_subset HJ
    (tailRange_colarge HJ Habsorb Hclosure Hrange (Hv.trans inf_le_left))
    (run_row_tail_subset_commonRow HP Hlaw HS Hσ Hseed (Hv.trans inf_le_right))
    commonRow_subset

/-- Total section data supplies the seed itself. It is not a separate
chosen or assumed row witness. No successful-run premise is used. -/
theorem run_commonRow_colarge
    {color : Bool} {J R S top P σ : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hnormal : Γ ≤ diagonalClosure omegaOne J)
    (HP : Γ ≤ is_function omegaOne entrySpace P)
    (Hlaw : Γ ≤ runLaw color R S top P)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Htop : Γ ≤ top ∈ᴮ omegaTwo) (Hσ : Γ ≤ σ ∈ᴮ omegaOne)
    (Hvalues : Γ ≤ ⨅ y, ⨅ A, _root_.imp
      (y ∈ᴮ omegaTwo ⊓ pair (pair σ y) A ∈ᴮ S) (colarge omegaOne J A)) :
    Γ ≤ colarge omegaOne J (commonRow S P σ) := by
  have Hex : Γ ≤ ⨆ seed, seed ∈ᴮ bv_powerset omegaOne ⊓ pair (pair σ top) seed ∈ᴮ S :=
    (le_inf ((HS.trans inf_le_right).trans (iInf_le _ (pair σ top)))
      (mem_prod_iff.mpr ⟨Hσ, Htop⟩)).trans bv_imp_elim
  obtain ⟨seed, Hseed⟩ := exists_convert Hex
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hcolarge : Γ ≤ colarge omegaOne J seed :=
    (le_inf (Hvalues.trans ((iInf_le _ top).trans (iInf_le _ seed)))
      (le_inf Htop (Hseed.trans inf_le_right))).trans bv_imp_elim
  exact run_commonRow_colarge_of_seed HJ Habsorb Hclosure Hnormal HP Hlaw HS Hσ
    (Hseed.trans inf_le_right) Hcolarge Hvalues

end bSet.ErdosSimultaneousRun
