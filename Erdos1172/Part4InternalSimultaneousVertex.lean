/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalOrdinalFallback
public import Erdos1172.Part4InternalGraphNeighborhood

@[expose] public section

/-!
# Actual next-vertex candidates for a simultaneous run

Earlier vertices constrain order and color. Old row values constrain only
the active triangle `σ < j < δ`, and the current row graph constrains only
`σ < δ`. Sections and histories are read from actual internal graph names.
The current vertex is not read back from the history. The candidate set
lies strictly below the fixed endpoint; an empty candidate set is handled
by the proved least-or-endpoint fallback, including mixed Boolean cases.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousVertex

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosRelationGraph ErdosOrdinalLeast
open ErdosOrdinalFallback

def futureRequirements (color : Bool) (δ R S Y X Z top y : bSet 𝔹) : 𝔹 :=
  (⨅ j, ⨅ v, _root_.imp (j ∈ᴮ δ ⊓ pair j v ∈ᴮ Y)
    (v ∈ᴮ y ⊓ graphColor color R v y)) ⊓
  (graphColor color R y top ⊓
    ((⨅ j, ⨅ σ, ⨅ w, ⨅ A, _root_.imp
      ((j ∈ᴮ δ ⊓ σ ∈ᴮ j) ⊓
        (pair (pair j σ) w ∈ᴮ X ⊓ pair (pair σ y) A ∈ᴮ S)) (w ∈ᴮ A)) ⊓
      (⨅ σ, ⨅ w, ⨅ A, _root_.imp
        (σ ∈ᴮ δ ⊓ (pair σ w ∈ᴮ Z ⊓ pair (pair σ y) A ∈ᴮ S)) (w ∈ᴮ A))))

theorem futureRequirements_ext_value (color : Bool) (δ R S Y X Z top : bSet 𝔹) :
    B_ext (futureRequirements color δ R S Y X Z top) :=
  B_ext_inf
    (B_ext_iInf (h := fun _ => B_ext_iInf (h := fun v =>
      B_ext_imp (h₁ := B_ext_const)
        (h₂ := B_ext_inf B_ext_mem_right (graphColor_ext_right color R v)))))
    (B_ext_inf (graphColor_ext_left color R top)
      (B_ext_inf
        (B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
          B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
            B_ext_imp (h₁ := B_ext_inf B_ext_const
              (B_ext_inf B_ext_const (B_ext_pair_right B_ext_pair_mem_left)))
              (h₂ := B_ext_const))))))
        (B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ => B_ext_iInf
          (h := fun _ => B_ext_imp
            (h₁ := B_ext_inf B_ext_const
              (B_ext_inf B_ext_const (B_ext_pair_right B_ext_pair_mem_left)))
            (h₂ := B_ext_const)))))))

theorem futureRequirements_ext_current (color : Bool) (δ R S Y X top y : bSet 𝔹) :
    B_ext (fun Z => futureRequirements color δ R S Y X Z top y) :=
  B_ext_inf B_ext_const (B_ext_inf B_ext_const
    (B_ext_inf B_ext_const
      (B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ => B_ext_iInf
        (h := fun _ => B_ext_imp
          (h₁ := B_ext_inf B_ext_const (B_ext_inf B_ext_mem_right B_ext_const))
          (h₂ := B_ext_const)))))))

def futureCandidates (color : Bool) (δ R S Y X Z top : bSet 𝔹) : bSet 𝔹 :=
  comprehend (futureRequirements color δ R S Y X Z top) top

theorem mem_futureCandidates_iff
    {color : Bool} {δ R S Y X Z top y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ y ∈ᴮ futureCandidates color δ R S Y X Z top ↔
      (Γ ≤ y ∈ᴮ top) ∧ Γ ≤ futureRequirements color δ R S Y X Z top y :=
  mem_comprehend_and (futureRequirements_ext_value color δ R S Y X Z top)

theorem mem_futureCandidates (color : Bool) (δ R S Y X Z top y : bSet 𝔹) :
    y ∈ᴮ futureCandidates color δ R S Y X Z top =
      y ∈ᴮ top ⊓ futureRequirements color δ R S Y X Z top y := by
  apply le_antisymm
  · have H := mem_futureCandidates_iff.mp
      (le_refl (y ∈ᴮ futureCandidates color δ R S Y X Z top))
    exact le_inf H.1 H.2
  · exact mem_futureCandidates_iff.mpr ⟨inf_le_left, inf_le_right⟩

theorem futureCandidates_subset_top
    {color : Bool} {δ R S Y X Z top : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ futureCandidates color δ R S Y X Z top ⊆ᴮ top :=
  comprehend_subset (ϕ := futureRequirements color δ R S Y X Z top) top

theorem futureCandidates_subset_omegaTwo
    {color : Bool} {δ R S Y X Z top : bSet 𝔹} {Γ : 𝔹}
    (Htop : Γ ≤ top ∈ᴮ omegaTwo) :
    Γ ≤ futureCandidates color δ R S Y X Z top ⊆ᴮ omegaTwo :=
  subset_trans' futureCandidates_subset_top (subset_of_mem_Ord Htop omegaTwo_Ord)

/-- Local equality of the current row graph gives equality of the actual
candidate sets, without graph functionality or totality hypotheses. -/
theorem futureCandidates_congr_current (color : Bool) (δ R S Y X top : bSet 𝔹) :
    B_congr (fun Z => futureCandidates color δ R S Y X Z top) := by
  intro Z W Γ H
  apply mem_ext
  · apply le_iInf
    intro y
    rw [← deduction]
    have Hy := mem_futureCandidates_iff.mp
      (show Γ ⊓ y ∈ᴮ futureCandidates color δ R S Y X Z top ≤
        y ∈ᴮ futureCandidates color δ R S Y X Z top from inf_le_right)
    exact mem_futureCandidates_iff.mpr ⟨Hy.1,
      bv_rw'' (ϕ := fun U => futureRequirements color δ R S Y X U top y)
        (inf_le_left.trans H) Hy.2 (futureRequirements_ext_current color δ R S Y X top y)⟩
  · apply le_iInf
    intro y
    rw [← deduction]
    have Hy := mem_futureCandidates_iff.mp
      (show Γ ⊓ y ∈ᴮ futureCandidates color δ R S Y X W top ≤
        y ∈ᴮ futureCandidates color δ R S Y X W top from inf_le_right)
    exact mem_futureCandidates_iff.mpr ⟨Hy.1,
      bv_rw'' (ϕ := fun U => futureRequirements color δ R S Y X U top y)
        (inf_le_left.trans (bv_symm H)) Hy.2
        (futureRequirements_ext_current color δ R S Y X top y)⟩

theorem futureCandidate_above_previous
    {color : Bool} {δ R S Y X Z top y j v : bSet 𝔹} {Γ : 𝔹}
    (Hy : Γ ≤ y ∈ᴮ futureCandidates color δ R S Y X Z top)
    (Hj : Γ ≤ j ∈ᴮ δ) (Hjv : Γ ≤ pair j v ∈ᴮ Y) :
    Γ ≤ v ∈ᴮ y ⊓ graphColor color R v y :=
  (le_inf (((mem_futureCandidates_iff.mp Hy).2.trans inf_le_left).trans
    ((iInf_le _ j).trans (iInf_le _ v))) (le_inf Hj Hjv)).trans bv_imp_elim

theorem futureCandidate_color_top
    {color : Bool} {δ R S Y X Z top y : bSet 𝔹} {Γ : 𝔹}
    (Hy : Γ ≤ y ∈ᴮ futureCandidates color δ R S Y X Z top) :
    Γ ≤ graphColor color R y top :=
  (mem_futureCandidates_iff.mp Hy).2.trans (inf_le_right.trans inf_le_left)

theorem futureCandidate_old_active_section
    {color : Bool} {δ R S Y X Z top y j σ w A : bSet 𝔹} {Γ : 𝔹}
    (Hy : Γ ≤ y ∈ᴮ futureCandidates color δ R S Y X Z top)
    (Hj : Γ ≤ j ∈ᴮ δ) (Hσ : Γ ≤ σ ∈ᴮ j)
    (HX : Γ ≤ pair (pair j σ) w ∈ᴮ X) (HS : Γ ≤ pair (pair σ y) A ∈ᴮ S) :
    Γ ≤ w ∈ᴮ A :=
  (le_inf (((mem_futureCandidates_iff.mp Hy).2.trans
    (inf_le_right.trans (inf_le_right.trans inf_le_left))).trans
      ((iInf_le _ j).trans ((iInf_le _ σ).trans ((iInf_le _ w).trans (iInf_le _ A)))))
    (le_inf (le_inf Hj Hσ) (le_inf HX HS))).trans bv_imp_elim

theorem futureCandidate_current_active_section
    {color : Bool} {δ R S Y X Z top y σ w A : bSet 𝔹} {Γ : 𝔹}
    (Hy : Γ ≤ y ∈ᴮ futureCandidates color δ R S Y X Z top)
    (Hσ : Γ ≤ σ ∈ᴮ δ) (HZ : Γ ≤ pair σ w ∈ᴮ Z)
    (HS : Γ ≤ pair (pair σ y) A ∈ᴮ S) : Γ ≤ w ∈ᴮ A :=
  (le_inf (((mem_futureCandidates_iff.mp Hy).2.trans
    (inf_le_right.trans (inf_le_right.trans inf_le_right))).trans
      ((iInf_le _ σ).trans ((iInf_le _ w).trans (iInf_le _ A))))
    (le_inf Hσ (le_inf HZ HS))).trans bv_imp_elim

/-- Construct the next actual vertex name, allowing an empty candidate set
on arbitrary Boolean pieces. Nonemptiness is not a premise. -/
theorem exists_next_vertex
    {color : Bool} {δ R S Y X Z top : bSet 𝔹} {Γ : 𝔹}
    (Htop : Γ ≤ top ∈ᴮ omegaTwo) :
    ∃ y : bSet 𝔹, Γ ≤ y ∈ᴮ omegaTwo ⊓
      leastOrTop (futureCandidates color δ R S Y X Z top) top y :=
  exists_bounded_leastOrTop omegaTwo_Ord (futureCandidates_subset_omegaTwo Htop) Htop

theorem next_vertex_eq_top_empty
    {color : Bool} {δ R S Y X Z top y : bSet 𝔹} {Γ : 𝔹}
    (Hchoice : Γ ≤ leastOrTop (futureCandidates color δ R S Y X Z top) top y)
    (Heq : Γ ≤ y =ᴮ top) :
    Γ ≤ futureCandidates color δ R S Y X Z top =ᴮ (∅ : bSet 𝔹) :=
  empty_of_leastOrTop_eq futureCandidates_subset_top Hchoice Heq

theorem next_vertex_ne_top_least
    {color : Bool} {δ R S Y X Z top y : bSet 𝔹} {Γ : 𝔹}
    (Hchoice : Γ ≤ leastOrTop (futureCandidates color δ R S Y X Z top) top y)
    (Hne : Γ ≤ (y =ᴮ top)ᶜ) :
    Γ ≤ leastIn (futureCandidates color δ R S Y X Z top) y :=
  leastIn_of_leastOrTop_ne Hchoice Hne

end bSet.ErdosSimultaneousVertex
