/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSmallPoolOperations
public import Erdos1172.Part4InternalBlockPoolCongruence

@[expose] public section

/-!
# A concrete inflationary update for the fixed whole-block selector

The new object pool retains old objects and adds only successful values.
The point pool includes every point of both old and newly selected blocks,
then takes the clipped successor of the full downward closure. Support is
independent of success and cardinal assumptions; smallness is proved from
the actual selector law and the two input cardinal bounds under CH.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosBlockPoolUpdate

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosCanonicalBlocks ErdosBlockSelector ErdosBlockSelectorPool
open ErdosCountableChoicePoolStep ErdosSmallFamilyUnion ErdosInitialSegments
open ErdosSmallPoolOperations ErdosBlockPoolCongruence ErdosOrdinalPointHull
open ErdosCountablePast ErdosIdeal

def nextObjects (color : Bool) (R B P F : bSet 𝔹) : bSet 𝔹 :=
  binary_union B (successfulObjects color R B P F)

def pointInput (B P F : bSet 𝔹) : bSet 𝔹 :=
  binary_union P (binary_union (bv_union B) (selectedPoints omegaTwo B P F))

def nextPoints (B P F : bSet 𝔹) : bSet 𝔹 := ordinalGrow (pointInput B P F)

theorem nextObjects_congr {color : Bool} {R F B₁ B₂ P₁ P₂ : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ B₁ =ᴮ B₂) (HP : Γ ≤ P₁ =ᴮ P₂) :
    Γ ≤ nextObjects color R B₁ P₁ F =ᴮ nextObjects color R B₂ P₂ F :=
  binary_union_congr HB (successfulObjects_congr HB HP)

theorem pointInput_congr {F B₁ B₂ P₁ P₂ : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ B₁ =ᴮ B₂) (HP : Γ ≤ P₁ =ᴮ P₂) :
    Γ ≤ pointInput B₁ P₁ F =ᴮ pointInput B₂ P₂ F :=
  binary_union_congr HP (binary_union_congr (B_congr_bv_union HB)
    (selectedPoints_congr HB HP))

theorem nextPoints_congr {F B₁ B₂ P₁ P₂ : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ B₁ =ᴮ B₂) (HP : Γ ≤ P₁ =ᴮ P₂) :
    Γ ≤ nextPoints B₁ P₁ F =ᴮ nextPoints B₂ P₂ F :=
  ordinalGrow_congr (pointInput_congr HB HP)

theorem oldObjects_subset_nextObjects {color : Bool} {R B P F : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ B ⊆ᴮ nextObjects color R B P F := subset_binary_union_left

theorem successfulObjects_subset_nextObjects
    {color : Bool} {R B P F : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ successfulObjects color R B P F ⊆ᴮ nextObjects color R B P F :=
  subset_binary_union_right

theorem blockPool_union_subset {color : Bool} {R B : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ B ⊆ᴮ blockObjects color R) : Γ ≤ bv_union B ⊆ᴮ omegaTwo := by
  apply union_subset_of_members_subset
  apply le_iInf
  intro A
  rw [← deduction]
  exact (mem_blockObjects_iff.mp
    (mem_of_mem_subset (inf_le_left.trans HB) inf_le_right)).1

theorem pointInput_subset {color : Bool} {R B P F : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ B ⊆ᴮ blockObjects color R) (HP : Γ ≤ P ⊆ᴮ omegaTwo) :
    Γ ≤ pointInput B P F ⊆ᴮ omegaTwo :=
  binary_union_subset HP (binary_union_subset (blockPool_union_subset HB)
    selectedPoints_subset)

theorem nextObjects_subset {color : Bool} {R B P F : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ B ⊆ᴮ blockObjects color R) :
    Γ ≤ nextObjects color R B P F ⊆ᴮ blockObjects color R :=
  binary_union_subset HB successfulObjects_subset_blocks

theorem nextPoints_subset {B P F : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ nextPoints B P F ⊆ᴮ omegaTwo := ordinalGrow_subset

theorem pointInput_subset_nextPoints {color : Bool} {R B P F : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ B ⊆ᴮ blockObjects color R) (HP : Γ ≤ P ⊆ᴮ omegaTwo) :
    Γ ≤ pointInput B P F ⊆ᴮ nextPoints B P F :=
  subset_ordinalGrow (pointInput_subset HB HP)

theorem oldPoints_subset_nextPoints {color : Bool} {R B P F : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ B ⊆ᴮ blockObjects color R) (HP : Γ ≤ P ⊆ᴮ omegaTwo) :
    Γ ≤ P ⊆ᴮ nextPoints B P F :=
  subset_trans' subset_binary_union_left (pointInput_subset_nextPoints HB HP)

theorem oldBlockPoints_subset_nextPoints {color : Bool} {R B P F : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ B ⊆ᴮ blockObjects color R) (HP : Γ ≤ P ⊆ᴮ omegaTwo) :
    Γ ≤ bv_union B ⊆ᴮ nextPoints B P F :=
  subset_trans' (subset_trans' subset_binary_union_left subset_binary_union_right)
    (pointInput_subset_nextPoints HB HP)

theorem selectedPoints_subset_nextPoints {color : Bool} {R B P F : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ B ⊆ᴮ blockObjects color R) (HP : Γ ≤ P ⊆ᴮ omegaTwo) :
    Γ ≤ selectedPoints omegaTwo B P F ⊆ᴮ nextPoints B P F :=
  subset_trans' (subset_trans' subset_binary_union_right subset_binary_union_right)
    (pointInput_subset_nextPoints HB HP)

/-- A small pool of whole block objects has a small physical point union. -/
theorem blockPool_union_small {color : Bool} {R B : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HB : Γ ≤ B ⊆ᴮ blockObjects color R)
    (Hsmall : Γ ≤ injects_into B omegaOne) : Γ ≤ injects_into (bv_union B) omegaOne := by
  apply union_injects_omegaOne HCH Hsmall
  apply le_iInf
  intro A
  rw [← deduction]
  exact blockObject_injects_omegaOne (mem_of_mem_subset (inf_le_left.trans HB) inf_le_right)

theorem update_small {color : Bool} {R J E S F B P : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HBsmall : Γ ≤ injects_into B omegaOne)
    (HPsmall : Γ ≤ injects_into P omegaOne)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HB : Γ ≤ B ⊆ᴮ blockObjects color R) (HP : Γ ≤ P ⊆ᴮ omegaTwo) :
    Γ ≤ injects_into (nextObjects color R B P F) omegaOne ⊓
      (injects_into (pointInput B P F) omegaOne ⊓
        injects_into (nextPoints B P F) omegaOne) := by
  have Hselected := successful_pool_step_small HCH HBsmall HPsmall HF Hlaw HB HP
  have Hinput : Γ ≤ injects_into (pointInput B P F) omegaOne :=
    binary_union_injects_omegaOne HCH HPsmall
      (binary_union_injects_omegaOne HCH (blockPool_union_small HCH HB HBsmall)
        (Hselected.trans inf_le_right))
  exact le_inf (binary_union_injects_omegaOne HCH HBsmall (Hselected.trans inf_le_left))
    (le_inf Hinput (ordinalGrow_injects_omegaOne HCH (pointInput_subset HB HP) Hinput))

theorem update_ordinal_and_growth {color : Bool} {R B P F : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HB : Γ ≤ B ⊆ᴮ blockObjects color R)
    (HP : Γ ≤ P ⊆ᴮ omegaTwo)
    (Hsmall : Γ ≤ injects_into (pointInput B P F) omegaOne) :
    Γ ≤ Ord (nextPoints B P F) ⊓ past (pointInput B P F) ∈ᴮ nextPoints B P F :=
  le_inf (ordinalGrow_Ord HCH (pointInput_subset HB HP) Hsmall)
    (past_mem_ordinalGrow HCH (pointInput_subset HB HP) Hsmall)

/-- All old and newly selected whole-block points lie in the new point pool. -/
theorem nextBlockPoints_subset_nextPoints {color : Bool} {R B P F : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ B ⊆ᴮ blockObjects color R) (HP : Γ ≤ P ⊆ᴮ omegaTwo) :
    Γ ≤ bv_union (nextObjects color R B P F) ⊆ᴮ nextPoints B P F := by
  apply union_subset_of_members_subset
  apply le_iInf
  intro A
  rw [← deduction]
  change Γ ⊓ A ∈ᴮ binary_union B (successfulObjects color R B P F) ≤ _
  rw [mem_binary_union, inf_sup_left]
  apply sup_le
  · exact subset_trans' (ErdosIdeal.loss_subset_union inf_le_right)
      (oldBlockPoints_subset_nextPoints (inf_le_left.trans HB) (inf_le_left.trans HP))
  · exact subset_trans' (selectedObject_subset_selectedPoints
      (mem_of_mem_subset successfulObjects_subset_selected inf_le_right))
      (selectedPoints_subset_nextPoints (inf_le_left.trans HB) (inf_le_left.trans HP))

end bSet.ErdosBlockPoolUpdate
