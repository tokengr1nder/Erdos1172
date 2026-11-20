/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionHistories

@[expose] public section

/-!
# Unconditional congruence of the actual fusion histories

These equalities hold even for malformed input graphs. Thus the bounded
recursion can use the actual whole-object/current-point history terms,
without assuming its future invariant in order to define its step.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionHistoryCongruence

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosCanonicalBlocks ErdosBoundedFunctionValue
open ErdosRelationGraph ErdosFusionHistories

theorem comprehend_parameter_congr (K : bSet 𝔹)
    (P : bSet 𝔹 → bSet 𝔹 → 𝔹)
    (Hvalue : ∀ a, B_ext (P a))
    (Hparameter : ∀ v, B_ext (fun a => P a v)) :
    B_congr (fun a => comprehend (P a) K) := by
  intro a b Γ Hab
  apply mem_ext
  · apply le_iInf
    intro v
    rw [← deduction]
    have Hv := (mem_comprehend_and (Hvalue a)).mp
      (show Γ ⊓ v ∈ᴮ comprehend (P a) K ≤ v ∈ᴮ comprehend (P a) K from inf_le_right)
    exact (mem_comprehend_and (Hvalue b)).mpr ⟨Hv.1,
      bv_rw'' (ϕ := fun z => P z v) (inf_le_left.trans Hab) Hv.2 (Hparameter v)⟩
  · apply le_iInf
    intro v
    rw [← deduction]
    have Hv := (mem_comprehend_and (Hvalue b)).mp
      (show Γ ⊓ v ∈ᴮ comprehend (P b) K ≤ v ∈ᴮ comprehend (P b) K from inf_le_right)
    exact (mem_comprehend_and (Hvalue a)).mpr ⟨Hv.1,
      bv_rw'' (ϕ := fun z => P z v) (inf_le_left.trans (bv_symm Hab)) Hv.2
        (Hparameter v)⟩

theorem relationGraph_parameter_congr (A B : bSet 𝔹)
    (P : bSet 𝔹 → bSet 𝔹 → bSet 𝔹 → 𝔹)
    (HP : ∀ a b, B_ext (fun t => P t a b)) :
    B_congr (fun t => relationGraph A B (P t)) :=
  comprehend_parameter_congr (prod A B)
    (fun t z => ⨆ a, ⨆ b, z =ᴮ pair a b ⊓ P t a b)
    (fun _ => B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
      B_ext_inf B_ext_bv_eq_left B_ext_const)))
    (fun _ => B_ext_iSup (h := fun a => B_ext_iSup (h := fun b =>
      B_ext_inf B_ext_const (HP a b))))

theorem relationGraph_domain_congr (B : bSet 𝔹)
    (P : bSet 𝔹 → bSet 𝔹 → 𝔹) : B_congr (fun A => relationGraph A B P) := by
  intro A C Γ H
  exact B_congr_comprehend
    (ϕ := fun z => ⨆ a, ⨆ b, z =ᴮ pair a b ⊓ P a b)
    (H_congr := B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
      B_ext_inf B_ext_bv_eq_left B_ext_const))) (prod_congr H bv_refl)

theorem blockValue_congr_graph (ν : bSet 𝔹) : B_congr (fun Blocks => blockValue Blocks ν) :=
  graphValue_congr_graph _ _

theorem rowValue_congr_blocks (E ν : bSet 𝔹) :
    B_congr (fun Blocks => rowValue E Blocks ν) := by
  intro Blocks Other Γ H
  exact graphValue_congr_input _ _ (blockValue_congr_graph ν H)

theorem currentPoint_congr_blocks (E Z ν : bSet 𝔹) :
    B_congr (fun Blocks => currentPoint E Blocks Z ν) := by
  intro Blocks Other Γ H
  exact graphValue_congr_graph _ _ (rowValue_congr_blocks E ν H)

theorem currentPoint_congr_indices (E Blocks ν : bSet 𝔹) :
    B_congr (fun Z => currentPoint E Blocks Z ν) := by
  intro Z W Γ H
  exact graphValue_congr_input _ _ (graphValue_congr_graph _ _ H)

theorem successfulRows_congr_stage (color : Bool) (R Blocks : bSet 𝔹) :
    B_congr (fun ξ => successfulRows color R ξ Blocks) :=
  B_congr_comprehend (H_congr :=
    B_ext_term _ _ B_ext_mem_left (blockValue_congr Blocks))

theorem successfulRows_congr_blocks (color : Bool) (R ξ : bSet 𝔹) :
    B_congr (successfulRows color R ξ) :=
  comprehend_parameter_congr ξ
    (fun Blocks ν => blockValue Blocks ν ∈ᴮ blockObjects color R)
    (fun Blocks => B_ext_term _ _ B_ext_mem_left (blockValue_congr Blocks))
    (fun ν => B_ext_term _ _ B_ext_mem_left (blockValue_congr_graph ν))

theorem currentPointGraph_congr_stage (color : Bool) (R E Blocks Z : bSet 𝔹) :
    B_congr (fun ξ => currentPointGraph color R E ξ Blocks Z) := by
  intro ξ η Γ H
  exact relationGraph_domain_congr _ _ (successfulRows_congr_stage color R Blocks H)

theorem currentPointGraph_congr_blocks (color : Bool) (R E ξ Z : bSet 𝔹) :
    B_congr (fun Blocks => currentPointGraph color R E ξ Blocks Z) := by
  intro Blocks Other Γ H
  exact bv_trans
    (relationGraph_domain_congr omegaTwo (fun ν x => x =ᴮ currentPoint E Blocks Z ν)
      (successfulRows_congr_blocks color R ξ H))
    (relationGraph_parameter_congr (successfulRows color R ξ Other) omegaTwo
      (fun B ν x => x =ᴮ currentPoint E B Z ν)
      (fun ν _ => B_ext_term _ _ B_ext_bv_eq_right (currentPoint_congr_blocks E Z ν)) H)

theorem currentPointGraph_congr_indices (color : Bool) (R E ξ Blocks : bSet 𝔹) :
    B_congr (currentPointGraph color R E ξ Blocks) :=
  relationGraph_parameter_congr (successfulRows color R ξ Blocks) omegaTwo
    (fun Z ν x => x =ᴮ currentPoint E Blocks Z ν)
    (fun ν _ => B_ext_term _ _ B_ext_bv_eq_right (currentPoint_congr_indices E Blocks ν))

theorem currentPoints_congr_stage (color : Bool) (R E Blocks Z : bSet 𝔹) :
    B_congr (fun ξ => currentPoints color R E ξ Blocks Z) := by
  intro ξ η Γ H
  exact bv_trans (B_congr_image_left (successfulRows_congr_stage color R Blocks H))
    (B_congr_image_right (currentPointGraph_congr_stage color R E Blocks Z H))

theorem currentPoints_congr_blocks (color : Bool) (R E ξ Z : bSet 𝔹) :
    B_congr (fun Blocks => currentPoints color R E ξ Blocks Z) := by
  intro Blocks Other Γ H
  exact bv_trans (B_congr_image_left (successfulRows_congr_blocks color R ξ H))
    (B_congr_image_right (currentPointGraph_congr_blocks color R E ξ Z H))

theorem currentPoints_congr_indices (color : Bool) (R E ξ Blocks : bSet 𝔹) :
    B_congr (currentPoints color R E ξ Blocks) := by
  intro Z W Γ H
  exact B_congr_image_right (currentPointGraph_congr_indices color R E ξ Blocks H)

theorem earlierHistory_congr_stage (color : Bool) (R Blocks : bSet 𝔹) :
    B_congr (fun ξ => earlierHistory color R ξ Blocks) := by
  intro ξ η Γ H
  exact B_congr_comprehend (ϕ := fun A => A ∈ᴮ blockObjects color R)
    (H_congr := B_ext_mem_left) (B_congr_image_left H)

theorem earlierHistory_congr_blocks (color : Bool) (R ξ : bSet 𝔹) :
    B_congr (earlierHistory color R ξ) := by
  intro Blocks Other Γ H
  exact B_congr_comprehend (ϕ := fun A => A ∈ᴮ blockObjects color R)
    (H_congr := B_ext_mem_left) (B_congr_image_right H)

end bSet.ErdosFusionHistoryCongruence
