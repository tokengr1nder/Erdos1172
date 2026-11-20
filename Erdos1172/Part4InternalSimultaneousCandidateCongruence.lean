/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSimultaneousCandidates
public import Erdos1172.Part4InternalRowCandidateCongruence

@[expose] public section

/-!
# Stability of exact simultaneous candidates

Only guarded earlier coordinates constrain a simultaneous row candidate.
A functional extension cannot change these coordinates when the old
histories are already total there. The graphs may contain later support.
Congruence under equality of arbitrary names is unconditional.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousCandidates

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosRelationGraph ErdosRowCandidates

/-- Adding history pairs can only impose more candidate constraints. -/
theorem simultaneousCandidates_antitone_histories
    {δ S Y X Y' X' top σ : bSet 𝔹} {Γ : 𝔹}
    (HY : Γ ≤ Y ⊆ᴮ Y') (HX : Γ ≤ X ⊆ᴮ X') :
    Γ ≤ simultaneousCandidates δ S Y' X' top σ ⊆ᴮ
      simultaneousCandidates δ S Y X top σ := by
  rw [subset_unfold']
  apply le_iInf
  intro v
  rw [← deduction]
  let Δ := Γ ⊓ v ∈ᴮ simultaneousCandidates δ S Y' X' top σ
  have HΔ : Δ ≤ Γ := inf_le_left
  have Hv : Δ ≤ v ∈ᴮ simultaneousCandidates δ S Y' X' top σ := inf_le_right
  have Hparts := mem_simultaneousCandidates_iff.mp Hv
  refine mem_simultaneousCandidates_iff.mpr ⟨Hparts.1,
    le_inf (Hparts.2.trans inf_le_left) (le_inf ?_ ?_)⟩
  · apply le_iInf
    intro j
    apply le_iInf
    intro y
    apply le_iInf
    intro A
    rw [← deduction]
    exact simultaneousCandidate_mem_previous_section (inf_le_left.trans Hv)
      (inf_le_right.trans inf_le_left)
      (mem_of_mem_subset ((inf_le_left.trans HΔ).trans HY)
        (inf_le_right.trans (inf_le_right.trans inf_le_left)))
      (inf_le_right.trans (inf_le_right.trans inf_le_right))
  · apply le_iInf
    intro j
    apply le_iInf
    intro w
    rw [← deduction]
    exact simultaneousCandidate_above_previous (inf_le_left.trans Hv)
      (inf_le_right.trans inf_le_left)
      (mem_of_mem_subset ((inf_le_left.trans HΔ).trans HX)
        (inf_le_right.trans inf_le_right))

/-- Total old histories and functional extensions have the same exact
candidate set. The row guard places every accessed row coordinate in the
old rectangular domain; no support restriction outside that domain is used. -/
theorem simultaneousCandidates_eq_of_extension
    {δ S Y X Y' X' top σ : bSet 𝔹} {Γ : 𝔹}
    (HsubY : Γ ≤ Y ⊆ᴮ Y') (HsubX : Γ ≤ X ⊆ᴮ X')
    (HfuncY : Γ ≤ is_func Y') (HfuncX : Γ ≤ is_func X')
    (HY : Γ ≤ is_func' δ omegaTwo Y)
    (HX : Γ ≤ is_func' (prod δ omegaOne) omegaOne X)
    (Hσ : Γ ≤ σ ∈ᴮ omegaOne) :
    Γ ≤ simultaneousCandidates δ S Y X top σ =ᴮ
      simultaneousCandidates δ S Y' X' top σ := by
  rw [eq_iff_subset_subset]
  refine le_inf ?_ (simultaneousCandidates_antitone_histories HsubY HsubX)
  rw [subset_unfold']
  apply le_iInf
  intro v
  rw [← deduction]
  let Δ := Γ ⊓ v ∈ᴮ simultaneousCandidates δ S Y X top σ
  have HΔ : Δ ≤ Γ := inf_le_left
  have Hv : Δ ≤ v ∈ᴮ simultaneousCandidates δ S Y X top σ := inf_le_right
  have Hparts := mem_simultaneousCandidates_iff.mp Hv
  refine mem_simultaneousCandidates_iff.mpr ⟨Hparts.1,
    le_inf (Hparts.2.trans inf_le_left) (le_inf ?_ ?_)⟩
  · apply le_iInf
    intro j
    apply le_iInf
    intro y
    apply le_iInf
    intro A
    rw [← deduction]
    have Hbase : Δ ⊓ (j ∈ᴮ δ ⊓
        (pair j y ∈ᴮ Y' ⊓ pair (pair σ y) A ∈ᴮ S)) ≤ Γ :=
      inf_le_left.trans HΔ
    have Hjy := prefix_pair_of_extension (Hbase.trans HsubY)
      (Hbase.trans HfuncY) (Hbase.trans HY)
      (inf_le_right.trans inf_le_left)
      (inf_le_right.trans (inf_le_right.trans inf_le_left))
    exact simultaneousCandidate_mem_previous_section (inf_le_left.trans Hv)
      (inf_le_right.trans inf_le_left) Hjy
      (inf_le_right.trans (inf_le_right.trans inf_le_right))
  · apply le_iInf
    intro j
    apply le_iInf
    intro w
    rw [← deduction]
    have Hbase : Δ ⊓ (j ∈ᴮ δ ⊓ pair (pair j σ) w ∈ᴮ X') ≤ Γ :=
      inf_le_left.trans HΔ
    have Hjσ : Δ ⊓ (j ∈ᴮ δ ⊓ pair (pair j σ) w ∈ᴮ X') ≤
        pair j σ ∈ᴮ prod δ omegaOne :=
      mem_prod (inf_le_right.trans inf_le_left) (Hbase.trans Hσ)
    have Hjw := prefix_pair_of_extension (Hbase.trans HsubX)
      (Hbase.trans HfuncX) (Hbase.trans HX) Hjσ
      (inf_le_right.trans inf_le_right)
    exact simultaneousCandidate_above_previous (inf_le_left.trans Hv)
      (inf_le_right.trans inf_le_left) Hjw

theorem rowRequirements_ext_stage (S Y X top σ v : bSet 𝔹) :
    B_ext (fun δ => rowRequirements δ S Y X top σ v) :=
  B_ext_inf B_ext_const
    (B_ext_inf
      (B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ => B_ext_iInf
        (h := fun _ => B_ext_imp
          (h₁ := B_ext_inf B_ext_mem_right B_ext_const) (h₂ := B_ext_const)))))
      (B_ext_iInf (h := fun _ => B_ext_iInf
        (h := fun _ => B_ext_imp
          (h₁ := B_ext_inf B_ext_mem_right B_ext_const) (h₂ := B_ext_const)))))

theorem rowRequirements_ext_vertices (δ S X top σ v : bSet 𝔹) :
    B_ext (fun Y => rowRequirements δ S Y X top σ v) :=
  B_ext_inf B_ext_const
    (B_ext_inf
      (B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ => B_ext_iInf
        (h := fun _ => B_ext_imp
          (h₁ := B_ext_inf B_ext_const (B_ext_inf B_ext_mem_right B_ext_const))
          (h₂ := B_ext_const)))))
      B_ext_const)

theorem rowRequirements_ext_history (δ S Y top σ v : bSet 𝔹) :
    B_ext (fun X => rowRequirements δ S Y X top σ v) :=
  B_ext_inf B_ext_const
    (B_ext_inf B_ext_const
      (B_ext_iInf (h := fun _ => B_ext_iInf
        (h := fun _ => B_ext_imp
          (h₁ := B_ext_inf B_ext_const B_ext_mem_right) (h₂ := B_ext_const)))))

private theorem congr_comprehend_parameter
    (P : bSet 𝔹 → bSet 𝔹 → 𝔹)
    (Hvalue : ∀ a, B_ext (P a))
    (Hparameter : ∀ v, B_ext (fun a => P a v)) :
    B_congr (fun a => comprehend (P a) omegaOne) := by
  intro a b Γ Hab
  apply mem_ext
  · apply le_iInf
    intro v
    rw [← deduction]
    have Hv := (mem_comprehend_and (Hvalue a)).mp
      (show Γ ⊓ v ∈ᴮ comprehend (P a) omegaOne ≤
        v ∈ᴮ comprehend (P a) omegaOne from inf_le_right)
    exact (mem_comprehend_and (Hvalue b)).mpr ⟨Hv.1,
      bv_rw'' (ϕ := fun z => P z v) (inf_le_left.trans Hab) Hv.2 (Hparameter v)⟩
  · apply le_iInf
    intro v
    rw [← deduction]
    have Hv := (mem_comprehend_and (Hvalue b)).mp
      (show Γ ⊓ v ∈ᴮ comprehend (P b) omegaOne ≤
        v ∈ᴮ comprehend (P b) omegaOne from inf_le_right)
    exact (mem_comprehend_and (Hvalue a)).mpr ⟨Hv.1,
      bv_rw'' (ϕ := fun z => P z v) (inf_le_left.trans (bv_symm Hab)) Hv.2
        (Hparameter v)⟩

/-- Stage congruence requires neither an ordinal premise nor total histories. -/
theorem simultaneousCandidates_congr_stage (S Y X top σ : bSet 𝔹) :
    B_congr (fun δ => simultaneousCandidates δ S Y X top σ) :=
  congr_comprehend_parameter (fun δ => rowRequirements δ S Y X top σ)
    (fun δ => rowRequirements_ext_value δ S Y X top σ)
    (fun v => rowRequirements_ext_stage S Y X top σ v)

/-- Equality of arbitrary vertex-history names preserves the candidate name. -/
theorem simultaneousCandidates_congr_vertices (δ S X top σ : bSet 𝔹) :
    B_congr (fun Y => simultaneousCandidates δ S Y X top σ) :=
  congr_comprehend_parameter (fun Y => rowRequirements δ S Y X top σ)
    (fun Y => rowRequirements_ext_value δ S Y X top σ)
    (fun v => rowRequirements_ext_vertices δ S X top σ v)

/-- Equality of arbitrary rectangular row-history names is sufficient. -/
theorem simultaneousCandidates_congr_history (δ S Y top σ : bSet 𝔹) :
    B_congr (fun X => simultaneousCandidates δ S Y X top σ) :=
  congr_comprehend_parameter (fun X => rowRequirements δ S Y X top σ)
    (fun X => rowRequirements_ext_value δ S Y X top σ)
    (fun v => rowRequirements_ext_history δ S Y top σ v)

end bSet.ErdosSimultaneousCandidates
