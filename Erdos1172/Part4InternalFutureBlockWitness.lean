/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFutureBlockDichotomy
public import Erdos1172.Part4InternalPositiveSectionsEndpoint

@[expose] public section

/-!
# Actual future-block witnesses at the original Boolean condition

Both the vertex graph and the coherent common-row family are unconditional
extensional parameters of the successful-block predicate. Boolean fullness
therefore selects actual names for both without shrinking the condition.
Absence of the opposite exact target eliminates only the opposite branch
of the proved future dichotomy; it does not supply a successful run as a
new premise. All original future-restricted row-ideal laws are retained.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFutureBlockWitness

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosIncreasingPartial
open ErdosSuccessfulRunBlock ErdosSectionPullback ErdosFutureBlockDichotomy

theorem homogeneousUnion_self_ext_graph (color : Bool) (R A : bSet 𝔹) :
    B_ext (fun f => homogeneousUnion color R A A f f) := by
  simp only [homogeneousUnion, sup_self]
  exact B_ext_iInf (h := fun x => B_ext_iInf (h := fun y =>
    B_ext_imp (h₁ := B_ext_inf
      (B_ext_inf (rangeMem_ext_graph A x) (rangeMem_ext_graph A y)) B_ext_const)
      (h₂ := B_ext_const)))

theorem blockRowContainment_ext_graph (S C : bSet 𝔹) :
    B_ext (fun f => blockRowContainment S f C) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_iInf (h := fun y => B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_inf
        (B_ext_inf B_ext_const (rangeMem_ext_graph omegaOne y)) B_ext_const)
        (h₂ := B_ext_const)))))

theorem blockRowContainment_ext_common (S f : bSet 𝔹) :
    B_ext (blockRowContainment S f) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_inf
        (B_ext_inf B_ext_mem_right B_ext_const) B_ext_const)
        (h₂ := B_ext_const)))))

theorem futureCommonBlockRows_ext_graph (S L C : bSet 𝔹) :
    B_ext (fun f => futureCommonBlockRows S L f C) :=
  B_ext_inf B_ext_const (B_ext_inf B_ext_const
    (B_ext_inf B_ext_const (blockRowContainment_ext_graph S C)))

theorem futureCommonBlockRows_ext_common (S L f : bSet 𝔹) :
    B_ext (futureCommonBlockRows S L f) :=
  B_ext_inf B_ext_is_function_right (B_ext_inf B_ext_const
    (B_ext_inf (B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
        B_ext_imp (h₁ := B_ext_inf B_ext_const B_ext_mem_right) (h₂ := B_ext_const)))))
      (blockRowContainment_ext_common S f)))

/-- No assumptions about the graph, sections, or ideals are needed for
extensionality, as required by the Boolean maximum principle. -/
theorem futureSuccessfulBlockData_ext_graph
    (color : Bool) (R S L C : bSet 𝔹) :
    B_ext (fun f => futureSuccessfulBlockData color R S L f C) :=
  B_ext_inf ErdosSmallFiberBound.B_ext_injective_code
    (B_ext_inf (increasingOn_ext_graph omegaOne)
      (B_ext_inf (homogeneousUnion_self_ext_graph color R omegaOne)
        (futureCommonBlockRows_ext_graph S L C)))

theorem futureSuccessfulBlockData_ext_common
    (color : Bool) (R S L f : bSet 𝔹) :
    B_ext (futureSuccessfulBlockData color R S L f) :=
  B_ext_inf B_ext_const (B_ext_inf B_ext_const
    (B_ext_inf B_ext_const (futureCommonBlockRows_ext_common S L f)))

/-- The same actual names jointly witness all successful-block and
common-row laws at the original condition, not merely on a dense part. -/
theorem exists_futureSuccessfulBlock
    {color : Bool} {R S L : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ hasFutureSuccessfulBlock color R S L) :
    ∃ f C : bSet 𝔹, Γ ≤ futureSuccessfulBlockData color R S L f C := by
  obtain ⟨f, Hf⟩ := exists_convert H
    (B_ext_iSup (h := fun C => futureSuccessfulBlockData_ext_graph color R S L C))
  obtain ⟨C, HC⟩ := exists_convert Hf (futureSuccessfulBlockData_ext_common color R S L f)
  exact ⟨f, C, HC⟩

/-- Ambient nonexistence of the opposite target also excludes that target
inside L. The successful Boolean value follows without an external case
choice between the two branches. -/
theorem hasFutureSuccessfulBlock_of_no_opposite
    {color : Bool} {R S L : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HL : Γ ≤ L ⊆ᴮ omegaTwo)
    (Hlarge : Γ ≤ injects_into omegaTwo L)
    (HS : Γ ≤ is_func' (prod omegaOne L) (bv_powerset omegaOne) S)
    (Hrows : Γ ≤ normalRowAvailabilityOn S L)
    (HnoOpp : Γ ≤ (hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo)ᶜ) :
    Γ ≤ hasFutureSuccessfulBlock color R S L := by
  have Hdich := successful_block_in_future_or_opposite_twoBlock
    (color := color) (R := R) HCH HL Hlarge HS Hrows
  apply (le_inf le_rfl Hdich).trans
  rw [inf_sup_left]
  apply sup_le
  · exact inf_le_right
  · have Htarget := ErdosPositiveSectionsEndpoint.hasTwoBlock_codomain_mono
      (inf_le_left.trans HL)
      (show Γ ⊓ hasTwoBlock (!color) R omegaOne bSet.omega L ≤
        hasTwoBlock (!color) R omegaOne bSet.omega L from inf_le_right)
    exact (bv_absurd _ Htarget (inf_le_left.trans HnoOpp)).trans bot_le

/-- Actual successful future block and its original coherent row family.
Only future-restricted section/ideal data and ambient failure of the
opposite target are assumed; no run or successful block is supplied. -/
theorem exists_futureSuccessfulBlock_of_no_opposite
    {color : Bool} {R S L : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HL : Γ ≤ L ⊆ᴮ omegaTwo)
    (Hlarge : Γ ≤ injects_into omegaTwo L)
    (HS : Γ ≤ is_func' (prod omegaOne L) (bv_powerset omegaOne) S)
    (Hrows : Γ ≤ normalRowAvailabilityOn S L)
    (HnoOpp : Γ ≤ (hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo)ᶜ) :
    ∃ f C : bSet 𝔹, Γ ≤ futureSuccessfulBlockData color R S L f C :=
  exists_futureSuccessfulBlock
    (hasFutureSuccessfulBlock_of_no_opposite HCH HL Hlarge HS Hrows HnoOpp)

end bSet.ErdosFutureBlockWitness
