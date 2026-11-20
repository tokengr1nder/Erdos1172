/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSimultaneousVertex
public import Erdos1172.Part4InternalRowCandidateCongruence

@[expose] public section

/-!
# Stability of simultaneous next-vertex candidates

Functional history extensions preserve the exact guarded candidate set.
Old active coordinates lie in the earlier rectangular domain, while only
the current prefix is needed from the current row graph. Equality of
arbitrary stage and history names gives unconditional congruence.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousVertex

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosRelationGraph ErdosRowCandidates

/-- More history pairs impose more constraints; the active-coordinate
guards themselves are unchanged. -/
theorem futureCandidates_antitone_histories
    {color : Bool} {δ R S Y X Z Y' X' Z' top : bSet 𝔹} {Γ : 𝔹}
    (HY : Γ ≤ Y ⊆ᴮ Y') (HX : Γ ≤ X ⊆ᴮ X') (HZ : Γ ≤ Z ⊆ᴮ Z') :
    Γ ≤ futureCandidates color δ R S Y' X' Z' top ⊆ᴮ
      futureCandidates color δ R S Y X Z top := by
  rw [subset_unfold']
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ y ∈ᴮ futureCandidates color δ R S Y' X' Z' top
  have HΔ : Δ ≤ Γ := inf_le_left
  have Hy : Δ ≤ y ∈ᴮ futureCandidates color δ R S Y' X' Z' top := inf_le_right
  have Hparts := mem_futureCandidates_iff.mp Hy
  refine mem_futureCandidates_iff.mpr ⟨Hparts.1,
    le_inf ?_ (le_inf (futureCandidate_color_top Hy) (le_inf ?_ ?_))⟩
  · apply le_iInf
    intro j
    apply le_iInf
    intro v
    rw [← deduction]
    exact futureCandidate_above_previous (inf_le_left.trans Hy)
      (inf_le_right.trans inf_le_left)
      (mem_of_mem_subset ((inf_le_left.trans HΔ).trans HY)
        (inf_le_right.trans inf_le_right))
  · apply le_iInf
    intro j
    apply le_iInf
    intro σ
    apply le_iInf
    intro w
    apply le_iInf
    intro A
    rw [← deduction]
    exact futureCandidate_old_active_section (inf_le_left.trans Hy)
      (inf_le_right.trans (inf_le_left.trans inf_le_left))
      (inf_le_right.trans (inf_le_left.trans inf_le_right))
      (mem_of_mem_subset ((inf_le_left.trans HΔ).trans HX)
        (inf_le_right.trans (inf_le_right.trans inf_le_left)))
      (inf_le_right.trans (inf_le_right.trans inf_le_right))
  · apply le_iInf
    intro σ
    apply le_iInf
    intro w
    apply le_iInf
    intro A
    rw [← deduction]
    exact futureCandidate_current_active_section (inf_le_left.trans Hy)
      (inf_le_right.trans inf_le_left)
      (mem_of_mem_subset ((inf_le_left.trans HΔ).trans HZ)
        (inf_le_right.trans (inf_le_right.trans inf_le_left)))
      (inf_le_right.trans (inf_le_right.trans inf_le_right))

/-- A functional extension cannot change an already total active prefix.
No totality of the current row outside `δ`, and no support restriction
outside the guarded domains, is assumed. -/
theorem futureCandidates_eq_of_extension
    {color : Bool} {δ R S Y X Z Y' X' Z' top : bSet 𝔹} {Γ : 𝔹}
    (HsubY : Γ ≤ Y ⊆ᴮ Y') (HsubX : Γ ≤ X ⊆ᴮ X') (HsubZ : Γ ≤ Z ⊆ᴮ Z')
    (HfuncY : Γ ≤ is_func Y') (HfuncX : Γ ≤ is_func X')
    (HfuncZ : Γ ≤ is_func Z')
    (HY : Γ ≤ is_func' δ omegaTwo Y)
    (HX : Γ ≤ is_func' (prod δ omegaOne) omegaOne X)
    (HZ : Γ ≤ is_func' δ omegaOne Z) (Hδ : Γ ≤ δ ⊆ᴮ omegaOne) :
    Γ ≤ futureCandidates color δ R S Y X Z top =ᴮ
      futureCandidates color δ R S Y' X' Z' top := by
  rw [eq_iff_subset_subset]
  refine le_inf ?_ (futureCandidates_antitone_histories HsubY HsubX HsubZ)
  rw [subset_unfold']
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ y ∈ᴮ futureCandidates color δ R S Y X Z top
  have HΔ : Δ ≤ Γ := inf_le_left
  have Hy : Δ ≤ y ∈ᴮ futureCandidates color δ R S Y X Z top := inf_le_right
  have Hparts := mem_futureCandidates_iff.mp Hy
  refine mem_futureCandidates_iff.mpr ⟨Hparts.1,
    le_inf ?_ (le_inf (futureCandidate_color_top Hy) (le_inf ?_ ?_))⟩
  · apply le_iInf
    intro j
    apply le_iInf
    intro v
    rw [← deduction]
    have Hbase : Δ ⊓ (j ∈ᴮ δ ⊓ pair j v ∈ᴮ Y') ≤ Γ := inf_le_left.trans HΔ
    have Hjv := prefix_pair_of_extension (Hbase.trans HsubY)
      (Hbase.trans HfuncY) (Hbase.trans HY)
      (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)
    exact futureCandidate_above_previous (inf_le_left.trans Hy)
      (inf_le_right.trans inf_le_left) Hjv
  · apply le_iInf
    intro j
    apply le_iInf
    intro σ
    apply le_iInf
    intro w
    apply le_iInf
    intro A
    rw [← deduction]
    let Λ := Δ ⊓ ((j ∈ᴮ δ ⊓ σ ∈ᴮ j) ⊓
      (pair (pair j σ) w ∈ᴮ X' ⊓ pair (pair σ y) A ∈ᴮ S))
    have Hbase : Λ ≤ Γ := inf_le_left.trans HΔ
    have Hj : Λ ≤ j ∈ᴮ δ := inf_le_right.trans (inf_le_left.trans inf_le_left)
    have Hσj : Λ ≤ σ ∈ᴮ j := inf_le_right.trans (inf_le_left.trans inf_le_right)
    have Hjω : Λ ≤ j ∈ᴮ omegaOne := mem_of_mem_subset (Hbase.trans Hδ) Hj
    have Hσω : Λ ≤ σ ∈ᴮ omegaOne := mem_of_mem_Ord Hσj Hjω omegaOne_Ord
    have Hjσ : Λ ≤ pair j σ ∈ᴮ prod δ omegaOne := mem_prod Hj Hσω
    have Hjw := prefix_pair_of_extension (Hbase.trans HsubX)
      (Hbase.trans HfuncX) (Hbase.trans HX) Hjσ
      (inf_le_right.trans (inf_le_right.trans inf_le_left))
    exact futureCandidate_old_active_section (inf_le_left.trans Hy) Hj Hσj Hjw
      (inf_le_right.trans (inf_le_right.trans inf_le_right))
  · apply le_iInf
    intro σ
    apply le_iInf
    intro w
    apply le_iInf
    intro A
    rw [← deduction]
    have Hbase : Δ ⊓ (σ ∈ᴮ δ ⊓
        (pair σ w ∈ᴮ Z' ⊓ pair (pair σ y) A ∈ᴮ S)) ≤ Γ := inf_le_left.trans HΔ
    have Hσw := prefix_pair_of_extension (Hbase.trans HsubZ)
      (Hbase.trans HfuncZ) (Hbase.trans HZ)
      (inf_le_right.trans inf_le_left)
      (inf_le_right.trans (inf_le_right.trans inf_le_left))
    exact futureCandidate_current_active_section (inf_le_left.trans Hy)
      (inf_le_right.trans inf_le_left) Hσw
      (inf_le_right.trans (inf_le_right.trans inf_le_right))

theorem futureRequirements_ext_stage (color : Bool) (R S Y X Z top y : bSet 𝔹) :
    B_ext (fun δ => futureRequirements color δ R S Y X Z top y) :=
  B_ext_inf
    (B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_inf B_ext_mem_right B_ext_const) (h₂ := B_ext_const))))
    (B_ext_inf B_ext_const
      (B_ext_inf
        (B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
          B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
            B_ext_imp
              (h₁ := B_ext_inf (B_ext_inf B_ext_mem_right B_ext_const) B_ext_const)
              (h₂ := B_ext_const))))))
        (B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ => B_ext_iInf
          (h := fun _ => B_ext_imp
            (h₁ := B_ext_inf B_ext_mem_right B_ext_const) (h₂ := B_ext_const)))))))

theorem futureRequirements_ext_vertices (color : Bool) (δ R S X Z top y : bSet 𝔹) :
    B_ext (fun Y => futureRequirements color δ R S Y X Z top y) :=
  B_ext_inf
    (B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_inf B_ext_const B_ext_mem_right) (h₂ := B_ext_const))))
    B_ext_const

theorem futureRequirements_ext_history (color : Bool) (δ R S Y Z top y : bSet 𝔹) :
    B_ext (fun X => futureRequirements color δ R S Y X Z top y) :=
  B_ext_inf B_ext_const
    (B_ext_inf B_ext_const
      (B_ext_inf
        (B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
          B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
            B_ext_imp
              (h₁ := B_ext_inf B_ext_const (B_ext_inf B_ext_mem_right B_ext_const))
              (h₂ := B_ext_const))))))
        B_ext_const))

private theorem congr_comprehend_parameter
    (P : bSet 𝔹 → bSet 𝔹 → 𝔹) (top : bSet 𝔹)
    (Hvalue : ∀ a, B_ext (P a))
    (Hparameter : ∀ y, B_ext (fun a => P a y)) :
    B_congr (fun a => comprehend (P a) top) := by
  intro a b Γ Hab
  apply mem_ext
  · apply le_iInf
    intro y
    rw [← deduction]
    have Hy := (mem_comprehend_and (Hvalue a)).mp
      (show Γ ⊓ y ∈ᴮ comprehend (P a) top ≤
        y ∈ᴮ comprehend (P a) top from inf_le_right)
    exact (mem_comprehend_and (Hvalue b)).mpr ⟨Hy.1,
      bv_rw'' (ϕ := fun z => P z y) (inf_le_left.trans Hab) Hy.2 (Hparameter y)⟩
  · apply le_iInf
    intro y
    rw [← deduction]
    have Hy := (mem_comprehend_and (Hvalue b)).mp
      (show Γ ⊓ y ∈ᴮ comprehend (P b) top ≤
        y ∈ᴮ comprehend (P b) top from inf_le_right)
    exact (mem_comprehend_and (Hvalue a)).mpr ⟨Hy.1,
      bv_rw'' (ϕ := fun z => P z y) (inf_le_left.trans (bv_symm Hab)) Hy.2
        (Hparameter y)⟩

/-- Congruence of the guarded stage is independent of ordinal or function assumptions. -/
theorem futureCandidates_congr_stage (color : Bool) (R S Y X Z top : bSet 𝔹) :
    B_congr (fun δ => futureCandidates color δ R S Y X Z top) :=
  congr_comprehend_parameter (fun δ => futureRequirements color δ R S Y X Z top) top
    (fun δ => futureRequirements_ext_value color δ R S Y X Z top)
    (fun y => futureRequirements_ext_stage color R S Y X Z top y)

theorem futureCandidates_congr_vertices (color : Bool) (δ R S X Z top : bSet 𝔹) :
    B_congr (fun Y => futureCandidates color δ R S Y X Z top) :=
  congr_comprehend_parameter (fun Y => futureRequirements color δ R S Y X Z top) top
    (fun Y => futureRequirements_ext_value color δ R S Y X Z top)
    (fun y => futureRequirements_ext_vertices color δ R S X Z top y)

theorem futureCandidates_congr_history (color : Bool) (δ R S Y Z top : bSet 𝔹) :
    B_congr (fun X => futureCandidates color δ R S Y X Z top) :=
  congr_comprehend_parameter (fun X => futureRequirements color δ R S Y X Z top) top
    (fun X => futureRequirements_ext_value color δ R S Y X Z top)
    (fun y => futureRequirements_ext_history color δ R S Y Z top y)

end bSet.ErdosSimultaneousVertex
