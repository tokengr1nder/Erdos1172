/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSimultaneousCommonRows

@[expose] public section

/-!
# The coherent family of canonical common rows

The canonical common sets form one actual internal function on omega-one.
Normal ideal witnesses need not be chosen coherently: their guarded
internal existence suffices to construct a full run, and every applicable
row ideal makes the corresponding canonical set co-large. The run is
allowed to stop. No successful branch or homogeneous block is asserted.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousRun

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosPartition ErdosRelationGraph
open ErdosColargeIntersection ErdosSimultaneousEntry ErdosSimultaneousHistory
open ErdosSimultaneousRowChoice

private theorem commonRow_requirement_ext_row (S P v : bSet 𝔹) :
    B_ext (fun σ => ⨅ j, ⨅ y, ⨅ A, _root_.imp
      (pair j y ∈ᴮ vertexHistory P ⊓ pair (pair σ y) A ∈ᴮ S) (v ∈ᴮ A)) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ => B_ext_iInf (h := fun A =>
    B_ext_imp (h₁ := B_ext_inf B_ext_const
      (B_ext_pair_left (ϕ := fun z => pair z A ∈ᴮ S) B_ext_pair_mem_left))
      (h₂ := B_ext_const))))

/-- Congruence is unconditional and does not depend on run totality. -/
theorem commonRow_congr_row (S P : bSet 𝔹) : B_congr (commonRow S P) := by
  intro σ τ Γ H
  apply mem_ext
  · apply le_iInf
    intro v
    rw [← deduction]
    have Hv := mem_commonRow_iff.mp
      (show Γ ⊓ v ∈ᴮ commonRow S P σ ≤ v ∈ᴮ commonRow S P σ from inf_le_right)
    exact mem_commonRow_iff.mpr ⟨Hv.1,
      bv_rw'' (ϕ := fun ρ => ⨅ j, ⨅ y, ⨅ A, _root_.imp
        (pair j y ∈ᴮ vertexHistory P ⊓ pair (pair ρ y) A ∈ᴮ S) (v ∈ᴮ A))
        (inf_le_left.trans H) Hv.2 (commonRow_requirement_ext_row S P v)⟩
  · apply le_iInf
    intro v
    rw [← deduction]
    have Hv := mem_commonRow_iff.mp
      (show Γ ⊓ v ∈ᴮ commonRow S P τ ≤ v ∈ᴮ commonRow S P τ from inf_le_right)
    exact mem_commonRow_iff.mpr ⟨Hv.1,
      bv_rw'' (ϕ := fun ρ => ⨅ j, ⨅ y, ⨅ A, _root_.imp
        (pair j y ∈ᴮ vertexHistory P ⊓ pair (pair ρ y) A ∈ᴮ S) (v ∈ᴮ A))
        (inf_le_left.trans (bv_symm H)) Hv.2 (commonRow_requirement_ext_row S P v)⟩

def commonRows (S P : bSet 𝔹) : bSet 𝔹 :=
  relationGraph omegaOne (bv_powerset omegaOne)
    (fun σ C => C =ᴮ commonRow S P σ)

private theorem commonRows_value_ext_row (S P C : bSet 𝔹) :
    B_ext (fun σ => C =ᴮ commonRow S P σ) :=
  B_ext_term (ϕ := fun A => C =ᴮ A) (t := commonRow S P)
    B_ext_bv_eq_right (commonRow_congr_row S P)

theorem mem_commonRows_iff {S P σ C : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair σ C ∈ᴮ commonRows S P ↔
      Γ ≤ σ ∈ᴮ omegaOne ∧ Γ ≤ C ∈ᴮ bv_powerset omegaOne ∧ Γ ≤ C =ᴮ commonRow S P σ :=
  mem_relationGraph_iff (commonRows_value_ext_row S P) (fun _ => B_ext_bv_eq_left)

theorem commonRows_apply {S P σ C : bSet 𝔹} {Γ : 𝔹}
    (Hpair : Γ ≤ pair σ C ∈ᴮ commonRows S P) : Γ ≤ C =ᴮ commonRow S P σ :=
  (mem_commonRows_iff.mp Hpair).2.2

theorem commonRows_is_function (S P : bSet 𝔹) {Γ : 𝔹} :
    Γ ≤ is_function omegaOne (bv_powerset omegaOne) (commonRows S P) := by
  apply relationGraph_is_function (P := fun σ C => C =ᴮ commonRow S P σ)
    (commonRows_value_ext_row S P) (fun _ => B_ext_bv_eq_left)
  · apply le_iInf
    intro σ
    rw [← deduction]
    exact le_iSup_of_le (commonRow S P σ) (le_inf (mem_powerset_iff.mpr commonRow_subset) bv_refl)
  · intro σ τ C D Δ _ _ _ _ _ HC HD Hστ
    exact bv_trans HC (bv_trans (commonRow_congr_row S P Hστ) (bv_symm HD))

def rowNormalIdealData (S σ J : bSet 𝔹) : 𝔹 :=
  rowIdealData S σ J ⊓ diagonalClosure omegaOne J

theorem run_commonRow_colarge_of_normalData
    {color : Bool} {R S top P σ J : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ is_function omegaOne entrySpace P)
    (Hlaw : Γ ≤ runLaw color R S top P)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Htop : Γ ≤ top ∈ᴮ omegaTwo) (Hσ : Γ ≤ σ ∈ᴮ omegaOne)
    (Hdata : Γ ≤ rowNormalIdealData S σ J) :
    Γ ≤ colarge omegaOne J (commonRow S P σ) := by
  have Hrow : Γ ≤ rowIdealData S σ J := Hdata.trans inf_le_left
  exact run_commonRow_colarge
    (Hrow.trans (inf_le_left.trans inf_le_left))
    (Hrow.trans (inf_le_right.trans inf_le_left))
    (Hrow.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))
    (Hdata.trans inf_le_right) HP Hlaw HS Htop Hσ
    (Hrow.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))

theorem run_commonRows_value_colarge
    {color : Bool} {R S top P σ J C : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ is_function omegaOne entrySpace P)
    (Hlaw : Γ ≤ runLaw color R S top P)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Htop : Γ ≤ top ∈ᴮ omegaTwo)
    (Hdata : Γ ≤ rowNormalIdealData S σ J)
    (HC : Γ ≤ pair σ C ∈ᴮ commonRows S P) : Γ ≤ colarge omegaOne J C := by
  have Hcolarge := run_commonRow_colarge_of_normalData HP Hlaw HS Htop
    (mem_commonRows_iff.mp HC).1 Hdata
  have Heq := commonRows_apply HC
  exact le_inf (subset_trans' (subset_of_eq Heq) (Hcolarge.trans inf_le_left))
    (mem_congr (bv_symm (difference_congr_right Heq)) bv_refl (Hcolarge.trans inf_le_right))

theorem run_commonRows_colarge_values
    {color : Bool} {R S top P : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ is_function omegaOne entrySpace P)
    (Hlaw : Γ ≤ runLaw color R S top P)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Htop : Γ ≤ top ∈ᴮ omegaTwo) :
    Γ ≤ ⨅ σ, ⨅ J, ⨅ C, _root_.imp
      (rowNormalIdealData S σ J ⊓ pair σ C ∈ᴮ commonRows S P)
      (colarge omegaOne J C) := by
  apply le_iInf
  intro σ
  apply le_iInf
  intro J
  apply le_iInf
  intro C
  rw [← deduction]
  exact run_commonRows_value_colarge (inf_le_left.trans HP) (inf_le_left.trans Hlaw)
    (inf_le_left.trans HS) (inf_le_left.trans Htop)
    (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)

end bSet.ErdosSimultaneousRun
