/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalColargeIntersection
public import Erdos1172.Part4InternalIdealNormality

@[expose] public section

/-!
The actual diagonal intersection of an internal co-large section family.
A supported relation records each failed section; its inverse fibers are
small by functionality. The supplied normality law makes its diagonal
union small, so the concrete complement is co-large. No chosen ground
indices or assumed diagonal-intersection witness is used.
-/

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosDiagonalIntersection

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosIdeal ErdosColargeIntersection ErdosRelationGraph ErdosPartition

def sectionLossRelation (κ F : bSet 𝔹) : bSet 𝔹 :=
  relationGraph κ κ (fun x i => ⨆ A, pair i A ∈ᴮ F ⊓ (x ∈ᴮ A)ᶜ)

private theorem loss_ext_left (F i : bSet 𝔹) :
    B_ext (fun x => ⨆ A, pair i A ∈ᴮ F ⊓ (x ∈ᴮ A)ᶜ) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_const (B_ext_neg (h := B_ext_mem_left)))

private theorem loss_ext_right (F x : bSet 𝔹) :
    B_ext (fun i => ⨆ A, pair i A ∈ᴮ F ⊓ (x ∈ᴮ A)ᶜ) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_pair_mem_left B_ext_const)

theorem mem_sectionLossRelation_iff {κ F x i : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair x i ∈ᴮ sectionLossRelation κ F ↔
      (Γ ≤ x ∈ᴮ κ) ∧ (Γ ≤ i ∈ᴮ κ) ∧ Γ ≤ ⨆ A, pair i A ∈ᴮ F ⊓ (x ∈ᴮ A)ᶜ :=
  mem_relationGraph_iff (loss_ext_left F) (loss_ext_right F)

theorem sectionLoss_fiber_subset {κ F i A : bSet 𝔹} {Γ : 𝔹}
    (Hfunc : Γ ≤ is_func F) (HiA : Γ ≤ pair i A ∈ᴮ F) :
    Γ ≤ ErdosIdeal.fiber κ (sectionLossRelation κ F) i ⊆ᴮ difference κ A := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  let Δ := Γ ⊓ x ∈ᴮ ErdosIdeal.fiber κ (sectionLossRelation κ F) i
  have Hx : Δ ≤ x ∈ᴮ κ ⊓ pair x i ∈ᴮ sectionLossRelation κ F := by
    rw [← ErdosIdeal.mem_fiber]
    exact inf_le_right
  obtain ⟨B, HB⟩ := exists_convert
    (mem_sectionLossRelation_iff.mp (Hx.trans inf_le_right)).2.2
    (B_ext_inf B_ext_pair_mem_right (B_ext_neg (h := B_ext_mem_right)))
  have HAB : Δ ≤ A =ᴮ B := eq_of_is_func_of_eq (inf_le_left.trans Hfunc) bv_refl
    (inf_le_left.trans HiA) (HB.trans inf_le_left)
  change Δ ≤ x ∈ᴮ difference κ A
  rw [mem_difference]
  exact le_inf (Hx.trans inf_le_left)
    (bv_rw' (ϕ := fun C => (x ∈ᴮ C)ᶜ) HAB
      (h_congr := B_ext_neg (h := B_ext_mem_right)) (H_new := HB.trans inf_le_right))

theorem sectionLoss_fibers_small {κ J F : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal κ J) (HF : Γ ≤ is_func' κ (bv_powerset κ) F)
    (Hvalues : Γ ≤ ⨅ i, ⨅ A, _root_.imp (i ∈ᴮ κ ⊓ pair i A ∈ᴮ F) (difference κ A ∈ᴮ J)) :
    Γ ≤ ⨅ i, _root_.imp (i ∈ᴮ κ) (ErdosIdeal.fiber κ (sectionLossRelation κ F) i ∈ᴮ J) := by
  apply le_iInf
  intro i
  rw [← deduction]
  let Δ := Γ ⊓ i ∈ᴮ κ
  have Hex : Δ ≤ ⨆ A, A ∈ᴮ bv_powerset κ ⊓ pair i A ∈ᴮ F :=
    (le_inf (inf_le_left.trans ((HF.trans inf_le_right).trans (iInf_le _ i)))
      inf_le_right).trans bv_imp_elim
  obtain ⟨A, HA⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hsmall : Δ ≤ difference κ A ∈ᴮ J :=
    (le_inf (inf_le_left.trans (Hvalues.trans ((iInf_le _ i).trans (iInf_le _ A))))
      (le_inf inf_le_right (HA.trans inf_le_right))).trans bv_imp_elim
  exact small_of_subset (downwardClosed_of_isIdeal (inf_le_left.trans HJ)) Hsmall
    (sectionLoss_fiber_subset (inf_le_left.trans (HF.trans inf_le_left)) (HA.trans inf_le_right))

def diagonalCommon (κ F : bSet 𝔹) : bSet 𝔹 :=
  difference κ (diagonalUnion κ (sectionLossRelation κ F))

theorem diagonalCommon_colarge {κ J F : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal κ J) (Hnormal : Γ ≤ diagonalClosure κ J)
    (HF : Γ ≤ is_func' κ (bv_powerset κ) F)
    (Hvalues : Γ ≤ ⨅ i, ⨅ A, _root_.imp (i ∈ᴮ κ ⊓ pair i A ∈ᴮ F)
      (difference κ A ∈ᴮ J)) : Γ ≤ colarge κ J (diagonalCommon κ F) := by
  have Hsmall : Γ ≤ diagonalUnion κ (sectionLossRelation κ F) ∈ᴮ J :=
    (le_inf (Hnormal.trans (iInf_le _ (sectionLossRelation κ F)))
      (sectionLoss_fibers_small HJ HF Hvalues)).trans bv_imp_elim
  exact le_inf difference_subset
    (small_of_subset (downwardClosed_of_isIdeal HJ) Hsmall
      (complement_subset_of_remainder_subset subset_self))

/-- Every point of the actual diagonal common set satisfies all sections
whose internal indices precede it. No function hypotheses are needed for
this direction of the membership law. -/
theorem diagonalCommon_mem_value {κ F x i A : bSet 𝔹} {Γ : 𝔹}
    (Hx : Γ ≤ x ∈ᴮ diagonalCommon κ F) (Hi : Γ ≤ i ∈ᴮ κ)
    (Hix : Γ ≤ i ∈ᴮ x) (HiA : Γ ≤ pair i A ∈ᴮ F) : Γ ≤ x ∈ᴮ A := by
  have Hdata : Γ ≤ x ∈ᴮ κ ⊓ (x ∈ᴮ diagonalUnion κ (sectionLossRelation κ F))ᶜ := by
    simpa only [diagonalCommon, mem_difference] using Hx
  rw [← compl_compl (x ∈ᴮ A), ← imp_bot, ← deduction]
  let Δ := Γ ⊓ (x ∈ᴮ A)ᶜ
  have Hpair : Δ ≤ pair x i ∈ᴮ sectionLossRelation κ F :=
    mem_sectionLossRelation_iff.mpr ⟨inf_le_left.trans (Hdata.trans inf_le_left),
      inf_le_left.trans Hi, le_iSup_of_le A (le_inf (inf_le_left.trans HiA) inf_le_right)⟩
  have Hbad : Δ ≤ x ∈ᴮ diagonalUnion κ (sectionLossRelation κ F) := by
    rw [mem_diagonalUnion]
    exact le_inf (inf_le_left.trans (Hdata.trans inf_le_left))
      (le_iSup_of_le i (le_inf (le_inf (inf_le_left.trans Hi) (inf_le_left.trans Hix)) Hpair))
  exact bv_absurd _ Hbad (inf_le_left.trans (Hdata.trans inf_le_right))

end bSet.ErdosDiagonalIntersection
