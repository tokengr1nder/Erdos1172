/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFutureBlockWitness

@[expose] public section

/-!
# An actual seed block in a large future

Constant full-base sections satisfy the future-restricted row laws for the
same supplied normal ideal. The proved future-block dichotomy therefore
supplies an increasing homogeneous omega-one graph when the opposite
exact two-block target is absent. There is no dense-basis premise, no
absence premise for the chosen color, and no supplied block or successful
run. The future and all witnesses are arbitrary internal names.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSeedBlock

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosColargeIntersection ErdosPartition
open ErdosRelationGraph ErdosSectionPullback ErdosFutureBlockWitness

/-- The whole base has empty relative complement in every internal ideal. -/
theorem colarge_self_of_isIdeal {κ J : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal κ J) : Γ ≤ colarge κ J κ := by
  refine le_inf subset_self (small_of_subset (downwardClosed_of_isIdeal HJ)
    (empty_small_of_isIdeal HJ) ?_)
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction, mem_difference]
  exact (bv_absurd _ (inf_le_right.trans inf_le_left)
    (inf_le_right.trans inf_le_right)).trans bot_le

/-- An actual constant graph, bounded on the supplied future only. -/
def constantSections (L : bSet 𝔹) : bSet 𝔹 :=
  relationGraph (prod omegaOne L) (bv_powerset omegaOne)
    (fun _ A => A =ᴮ omegaOne)

theorem constantSections_value {L q A : bSet 𝔹} {Γ : 𝔹}
    (Hpair : Γ ≤ pair q A ∈ᴮ constantSections L) : Γ ≤ A =ᴮ omegaOne :=
  ((mem_relationGraph_iff (P := fun (_ : bSet 𝔹) X => X =ᴮ omegaOne)
    (fun _ => B_ext_const)
    (fun _ => B_ext_bv_eq_left)).mp Hpair).2.2

theorem constantSections_is_function {L : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ is_function (prod omegaOne L) (bv_powerset omegaOne) (constantSections L) := by
  apply relationGraph_is_function (P := fun (_ : bSet 𝔹) X => X =ᴮ omegaOne)
    (fun _ => B_ext_const)
    (fun _ => B_ext_bv_eq_left)
  · apply le_iInf
    intro q
    rw [← deduction]
    exact le_iSup_of_le omegaOne (le_inf (mem_powerset_iff.mpr subset_self) bv_refl)
  · intro q₁ q₂ A₁ A₂ Δ _ _ _ _ _ H₁ H₂ _
    exact bv_trans H₁ (bv_symm H₂)

theorem constantSections_colarge {L J q A : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J)
    (Hpair : Γ ≤ pair q A ∈ᴮ constantSections L) :
    Γ ≤ colarge omegaOne J A := by
  have Heq : Γ ≤ A =ᴮ omegaOne := constantSections_value Hpair
  have Hbase : Γ ≤ colarge omegaOne J omegaOne := colarge_self_of_isIdeal HJ
  exact le_inf
    (bv_rw' (ϕ := fun X => X ⊆ᴮ omegaOne) Heq
      (h_congr := B_ext_subset_left) (H_new := subset_self))
    (mem_congr (bv_symm (difference_congr_right Heq)) bv_refl (Hbase.trans inf_le_right))

theorem constantSections_normal_row {L J σ : bSet 𝔹} {Γ : 𝔹}
    (Hproper : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hdiag : Γ ≤ diagonalClosure omegaOne J) :
    Γ ≤ rowNormalIdealDataOn (constantSections L) L σ J := by
  refine le_inf (le_inf Hproper (le_inf Habsorb (le_inf Hclosure ?_))) Hdiag
  apply le_iInf
  intro y
  apply le_iInf
  intro A
  rw [← deduction]
  exact constantSections_colarge (inf_le_left.trans (Hproper.trans inf_le_left))
    (inf_le_right.trans inf_le_right)

theorem constantSections_normal_availability {L J : bSet 𝔹} {Γ : 𝔹}
    (Hproper : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hdiag : Γ ≤ diagonalClosure omegaOne J) :
    Γ ≤ normalRowAvailabilityOn (constantSections L) L := by
  apply le_iInf
  intro σ
  rw [← deduction]
  exact le_iSup_of_le J (constantSections_normal_row (σ := σ)
    (inf_le_left.trans Hproper) (inf_le_left.trans Habsorb)
    (inf_le_left.trans Hclosure) (inf_le_left.trans Hdiag))

/-- A seed needs only the opposite target to be absent. The fixed ideal
supplies constant row data, not any graph-dependent hypothesis. -/
theorem exists_seed_block {color : Bool} {R J L : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (Hproper : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hdiag : Γ ≤ diagonalClosure omegaOne J)
    (HL : Γ ≤ L ⊆ᴮ omegaTwo) (Hlarge : Γ ≤ injects_into omegaTwo L)
    (HnoOpp : Γ ≤ (hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo)ᶜ) :
    ∃ f : bSet 𝔹, Γ ≤ is_injective_function omegaOne L f ⊓
      (increasingOn omegaOne f ⊓ homogeneousUnion color R omegaOne omegaOne f f) := by
  have HS : Γ ≤ is_func' (prod omegaOne L) (bv_powerset omegaOne)
      (constantSections L) := is_func'_of_is_function constantSections_is_function
  have Hrows : Γ ≤ normalRowAvailabilityOn (constantSections L) L :=
    constantSections_normal_availability Hproper Habsorb Hclosure Hdiag
  obtain ⟨f, C, Hblock⟩ := exists_futureSuccessfulBlock_of_no_opposite
    (color := color) (R := R) HCH HL Hlarge HS Hrows HnoOpp
  exact ⟨f, le_inf (Hblock.trans inf_le_left)
    (le_inf (Hblock.trans (inf_le_right.trans inf_le_left))
      (Hblock.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))))⟩

end bSet.ErdosSeedBlock
