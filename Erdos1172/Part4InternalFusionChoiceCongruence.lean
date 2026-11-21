/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionRowChoice
public import Erdos1172.Part4InternalFusionActiveHistory

@[expose] public section

/-!
# Unconditional congruence of fusion choices and complete active histories

The success mask and the evaluated old block change together with the
raw candidate term. Consequently the total least-or-zero choice graph
is congruent even when rows fail or input histories are malformed.
The active history retains both the previous active sets and the points
chosen now, with no dependence on the upcoming block's success.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionChoiceCongruence

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosFusionHistories ErdosFusionHistoryCongruence
open ErdosFusionRowCandidates ErdosFusionRowChoice ErdosFusionActiveHistory
open ErdosOrdinalFallback ErdosSmallPoolOperations

theorem rowCandidatesAt_congr_stage (color : Bool) (R E top Blocks X ν : bSet 𝔹) :
    B_congr (fun ξ => rowCandidatesAt color R E top ξ Blocks X ν) :=
  fusionRowCandidates_congr_stage (!color) R E (blockValue Blocks ν) top ν Blocks X

theorem rowCandidatesAt_congr_blocks (color : Bool) (R E top ξ X ν : bSet 𝔹) :
    B_congr (fun Blocks => rowCandidatesAt color R E top ξ Blocks X ν) :=
  fusionRowCandidates_of_history_congr_blocks (!color) R E top ξ ν X

theorem rowCandidatesAt_congr_coordinates (color : Bool) (R E top ξ Blocks ν : bSet 𝔹) :
    B_congr (fun X => rowCandidatesAt color R E top ξ Blocks X ν) :=
  fusionRowCandidates_congr_coordinates (!color) R E (blockValue Blocks ν) top ξ ν Blocks

theorem rowCandidatesAt_congr_top (color : Bool) (R E ξ Blocks X ν : bSet 𝔹) :
    B_congr (fun top => rowCandidatesAt color R E top ξ Blocks X ν) :=
  fusionRowCandidates_congr_top (!color) R E (blockValue Blocks ν) ξ ν Blocks X

theorem maskedCandidates_congr_stage (color : Bool) (R E top Blocks X ν : bSet 𝔹) :
    B_congr (fun ξ => maskedCandidates color R E top ξ Blocks X ν) :=
  comprehend_parameter_congr omegaOne
    (fun ξ v => ν ∈ᴮ successfulRows color R ξ Blocks ⊓
      v ∈ᴮ rowCandidatesAt color R E top ξ Blocks X ν)
    (fun _ => B_ext_inf B_ext_const B_ext_mem_left)
    (fun v => B_ext_inf
      (B_ext_term (ϕ := fun S => ν ∈ᴮ S) (t := fun ξ => successfulRows color R ξ Blocks)
        B_ext_mem_right (successfulRows_congr_stage color R Blocks))
      (B_ext_term (ϕ := fun C => v ∈ᴮ C)
        (t := fun ξ => rowCandidatesAt color R E top ξ Blocks X ν)
        B_ext_mem_right (rowCandidatesAt_congr_stage color R E top Blocks X ν)))

theorem maskedCandidates_congr_blocks (color : Bool) (R E top ξ X ν : bSet 𝔹) :
    B_congr (fun Blocks => maskedCandidates color R E top ξ Blocks X ν) :=
  comprehend_parameter_congr omegaOne
    (fun Blocks v => ν ∈ᴮ successfulRows color R ξ Blocks ⊓
      v ∈ᴮ rowCandidatesAt color R E top ξ Blocks X ν)
    (fun _ => B_ext_inf B_ext_const B_ext_mem_left)
    (fun v => B_ext_inf
      (B_ext_term (ϕ := fun S => ν ∈ᴮ S) (t := successfulRows color R ξ)
        B_ext_mem_right (successfulRows_congr_blocks color R ξ))
      (B_ext_term (ϕ := fun C => v ∈ᴮ C)
        (t := fun Blocks => rowCandidatesAt color R E top ξ Blocks X ν)
        B_ext_mem_right (rowCandidatesAt_congr_blocks color R E top ξ X ν)))

theorem maskedCandidates_congr_coordinates (color : Bool) (R E top ξ Blocks ν : bSet 𝔹) :
    B_congr (fun X => maskedCandidates color R E top ξ Blocks X ν) :=
  comprehend_parameter_congr omegaOne
    (fun X v => ν ∈ᴮ successfulRows color R ξ Blocks ⊓
      v ∈ᴮ rowCandidatesAt color R E top ξ Blocks X ν)
    (fun _ => B_ext_inf B_ext_const B_ext_mem_left)
    (fun v => B_ext_inf B_ext_const
      (B_ext_term (ϕ := fun C => v ∈ᴮ C)
        (t := fun X => rowCandidatesAt color R E top ξ Blocks X ν)
        B_ext_mem_right (rowCandidatesAt_congr_coordinates color R E top ξ Blocks ν)))

theorem maskedCandidates_congr_top (color : Bool) (R E ξ Blocks X ν : bSet 𝔹) :
    B_congr (fun top => maskedCandidates color R E top ξ Blocks X ν) :=
  comprehend_parameter_congr omegaOne
    (fun top v => ν ∈ᴮ successfulRows color R ξ Blocks ⊓
      v ∈ᴮ rowCandidatesAt color R E top ξ Blocks X ν)
    (fun _ => B_ext_inf B_ext_const B_ext_mem_left)
    (fun v => B_ext_inf B_ext_const
      (B_ext_term (ϕ := fun C => v ∈ᴮ C)
        (t := fun top => rowCandidatesAt color R E top ξ Blocks X ν)
        B_ext_mem_right (rowCandidatesAt_congr_top color R E ξ Blocks X ν)))

theorem currentChoices_congr_stage (color : Bool) (R E top Blocks X : bSet 𝔹) :
    B_congr (fun ξ => currentChoices color R E top ξ Blocks X) :=
  relationGraph_parameter_congr omegaOne omegaOne
    (fun ξ ν v => leastOrTop (maskedCandidates color R E top ξ Blocks X ν) 0 v)
    (fun ν v => B_ext_term
      (ϕ := fun C => leastOrTop C 0 v)
      (t := fun ξ => maskedCandidates color R E top ξ Blocks X ν)
      (leastOrTop_ext_set 0 v) (maskedCandidates_congr_stage color R E top Blocks X ν))

theorem currentChoices_congr_blocks (color : Bool) (R E top ξ X : bSet 𝔹) :
    B_congr (fun Blocks => currentChoices color R E top ξ Blocks X) :=
  relationGraph_parameter_congr omegaOne omegaOne
    (fun Blocks ν v => leastOrTop (maskedCandidates color R E top ξ Blocks X ν) 0 v)
    (fun ν v => B_ext_term
      (ϕ := fun C => leastOrTop C 0 v)
      (t := fun Blocks => maskedCandidates color R E top ξ Blocks X ν)
      (leastOrTop_ext_set 0 v) (maskedCandidates_congr_blocks color R E top ξ X ν))

theorem currentChoices_congr_coordinates (color : Bool) (R E top ξ Blocks : bSet 𝔹) :
    B_congr (currentChoices color R E top ξ Blocks) :=
  relationGraph_parameter_congr omegaOne omegaOne
    (fun X ν v => leastOrTop (maskedCandidates color R E top ξ Blocks X ν) 0 v)
    (fun ν v => B_ext_term
      (ϕ := fun C => leastOrTop C 0 v)
      (t := fun X => maskedCandidates color R E top ξ Blocks X ν)
      (leastOrTop_ext_set 0 v) (maskedCandidates_congr_coordinates color R E top ξ Blocks ν))

theorem currentChoices_congr_top (color : Bool) (R E ξ Blocks X : bSet 𝔹) :
    B_congr (fun top => currentChoices color R E top ξ Blocks X) :=
  relationGraph_parameter_congr omegaOne omegaOne
    (fun top ν v => leastOrTop (maskedCandidates color R E top ξ Blocks X ν) 0 v)
    (fun ν v => B_ext_term
      (ϕ := fun C => leastOrTop C 0 v)
      (t := fun top => maskedCandidates color R E top ξ Blocks X ν)
      (leastOrTop_ext_set 0 v) (maskedCandidates_congr_top color R E ξ Blocks X ν))

theorem currentChoices_congr
    {color : Bool} {R E top other ξ η Blocks Other X Y : bSet 𝔹} {Γ : 𝔹}
    (Htop : Γ ≤ top =ᴮ other) (Hξη : Γ ≤ ξ =ᴮ η)
    (HBlocks : Γ ≤ Blocks =ᴮ Other) (HXY : Γ ≤ X =ᴮ Y) :
    Γ ≤ currentChoices color R E top ξ Blocks X =ᴮ currentChoices color R E other η Other Y :=
  bv_trans (currentChoices_congr_top color R E ξ Blocks X Htop)
    (bv_trans (currentChoices_congr_stage color R E other Blocks X Hξη)
      (bv_trans (currentChoices_congr_blocks color R E other η X HBlocks)
        (currentChoices_congr_coordinates color R E other η Other HXY)))

theorem previousActive_congr_stage (Acts : bSet 𝔹) : B_congr (fun ξ => previousActive ξ Acts) := by
  intro ξ η Γ H
  exact B_congr_bv_union (B_congr_image_left H)

theorem previousActive_congr_acts (ξ : bSet 𝔹) : B_congr (previousActive ξ) := by
  intro Acts Other Γ H
  exact B_congr_bv_union (B_congr_image_right H)

theorem activeHistory_congr_stage (color : Bool) (R E Blocks Z Acts : bSet 𝔹) :
    B_congr (fun ξ => activeHistory color R E ξ Blocks Z Acts) := by
  intro ξ η Γ H
  exact binary_union_congr (previousActive_congr_stage Acts H)
    (currentPoints_congr_stage color R E Blocks Z H)

theorem activeHistory_congr_blocks (color : Bool) (R E ξ Z Acts : bSet 𝔹) :
    B_congr (fun Blocks => activeHistory color R E ξ Blocks Z Acts) := by
  intro Blocks Other Γ H
  exact binary_union_congr bv_refl (currentPoints_congr_blocks color R E ξ Z H)

theorem activeHistory_congr_indices (color : Bool) (R E ξ Blocks Acts : bSet 𝔹) :
    B_congr (fun Z => activeHistory color R E ξ Blocks Z Acts) := by
  intro Z W Γ H
  exact binary_union_congr bv_refl (currentPoints_congr_indices color R E ξ Blocks H)

theorem activeHistory_congr_acts (color : Bool) (R E ξ Blocks Z : bSet 𝔹) :
    B_congr (activeHistory color R E ξ Blocks Z) := by
  intro Acts Other Γ H
  exact binary_union_congr (previousActive_congr_acts ξ H) bv_refl

theorem activeHistory_congr
    {color : Bool} {R E ξ η Blocks Other Z W Acts OtherActs : bSet 𝔹} {Γ : 𝔹}
    (Hξη : Γ ≤ ξ =ᴮ η) (HBlocks : Γ ≤ Blocks =ᴮ Other)
    (HZW : Γ ≤ Z =ᴮ W) (HActs : Γ ≤ Acts =ᴮ OtherActs) :
    Γ ≤ activeHistory color R E ξ Blocks Z Acts =ᴮ activeHistory color R E η Other W OtherActs :=
  bv_trans (activeHistory_congr_stage color R E Blocks Z Acts Hξη)
    (bv_trans (activeHistory_congr_blocks color R E η Z Acts HBlocks)
      (bv_trans (activeHistory_congr_indices color R E η Other Acts HZW)
        (activeHistory_congr_acts color R E η Other W HActs)))

/-- The composed active-history term used before selecting the next block
is congruent, with the actual total current-choice graph substituted. -/
theorem activeHistory_currentChoices_congr
    {color : Bool} {R E top other ξ η Blocks Other X Y Acts OtherActs : bSet 𝔹} {Γ : 𝔹}
    (Htop : Γ ≤ top =ᴮ other) (Hξη : Γ ≤ ξ =ᴮ η)
    (HBlocks : Γ ≤ Blocks =ᴮ Other) (HXY : Γ ≤ X =ᴮ Y) (HActs : Γ ≤ Acts =ᴮ OtherActs) :
    Γ ≤ activeHistory color R E ξ Blocks (currentChoices color R E top ξ Blocks X) Acts =ᴮ
      activeHistory color R E η Other (currentChoices color R E other η Other Y) OtherActs :=
  activeHistory_congr Hξη HBlocks (currentChoices_congr Htop Hξη HBlocks HXY) HActs

end bSet.ErdosFusionChoiceCongruence
