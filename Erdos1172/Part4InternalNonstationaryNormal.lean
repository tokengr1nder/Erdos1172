/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalNonstationaryIdeal
public import Erdos1172.Part4InternalDiagonalClubUnbounded
public import Erdos1172.Part4InternalIdealNormality

@[expose] public section

/-!
# Diagonal closure of the constructed nonstationary ideal

For an arbitrary internal relation whose inverse fibers are nonstationary,
bounded internal choice constructs one club-valued function avoiding all
fibers. Its actual diagonal club avoids the relation's diagonal union.
Thus CH proves diagonal closure of the defined nonstationary ideal; neither
normality nor properness of that ideal is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosNonstationary

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosClubs

/-- The two pre-existing fiber APIs use exactly the same comprehension.
No representation or equality hypothesis is being introduced. -/
private theorem ideal_fiber_congr (κ R : bSet 𝔹) : B_congr (ErdosIdeal.fiber κ R) := by
  change B_congr (ErdosFiberInjection.fiber κ R)
  exact ErdosSmallFiberBound.fiber_congr κ R

private theorem avoidingFiberClub_ext_index (R C : bSet 𝔹) :
    B_ext (fun i => club omegaTwo C ⊓
      ErdosIdeal.fiber omegaTwo R i ⊆ᴮ difference omegaTwo C) :=
  B_ext_inf B_ext_const
    (B_ext_term (ϕ := fun A => A ⊆ᴮ difference omegaTwo C)
      (t := ErdosIdeal.fiber omegaTwo R) B_ext_subset_left (ideal_fiber_congr omegaTwo R))

/-- The avoiding clubs form an actual supported internal function,
rather than a separately supplied family of external witnesses. -/
theorem exists_avoiding_fiber_club_family {R : bSet 𝔹} {Γ : 𝔹}
    (Hfibers : Γ ≤ ⨅ i, _root_.imp (i ∈ᴮ omegaTwo)
      (ErdosIdeal.fiber omegaTwo R i ∈ᴮ nonstationaryIdeal)) :
    ∃ F : bSet 𝔹, Γ ≤ is_function omegaTwo (bv_powerset omegaTwo) F ⊓
      (⨅ i, ⨅ C, _root_.imp (i ∈ᴮ omegaTwo ⊓ pair i C ∈ᴮ F)
        (club omegaTwo C ⊓ ErdosIdeal.fiber omegaTwo R i ⊆ᴮ difference omegaTwo C)) := by
  apply ErdosSmallFiberBound.exists_selector_of_pointwise
    (P := fun i C => club omegaTwo C ⊓
      ErdosIdeal.fiber omegaTwo R i ⊆ᴮ difference omegaTwo C)
    (avoidingFiberClub_ext_index R)
    (fun i => avoidingClub_ext (ErdosIdeal.fiber omegaTwo R i))
  apply le_iInf
  intro i
  rw [← deduction]
  have HiSmall : Γ ⊓ i ∈ᴮ omegaTwo ≤
      ErdosIdeal.fiber omegaTwo R i ∈ᴮ nonstationaryIdeal :=
    (le_inf (inf_le_left.trans (Hfibers.trans (iInf_le _ i))) inf_le_right).trans bv_imp_elim
  obtain ⟨C, HC⟩ := exists_avoiding_club HiSmall
  exact le_iSup_of_le C (le_inf (mem_powerset_iff.mpr (club_subset (HC.trans inf_le_left))) HC)

/-- Any coherent avoiding family has a diagonal intersection disjoint
from the diagonal union. Only totality of the family is needed here;
the club property is used separately to witness nonstationarity. -/
theorem diagonalUnion_avoids_diagonalClub {R F : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_func' omegaTwo (bv_powerset omegaTwo) F)
    (Havoid : Γ ≤ ⨅ i, ⨅ C, _root_.imp (i ∈ᴮ omegaTwo ⊓ pair i C ∈ᴮ F)
      (ErdosIdeal.fiber omegaTwo R i ⊆ᴮ difference omegaTwo C)) :
    Γ ≤ diagonalUnion omegaTwo R ⊆ᴮ difference omegaTwo (diagonalClub F) := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  let Δ := Γ ⊓ x ∈ᴮ diagonalUnion omegaTwo R
  have Hx : Δ ≤ x ∈ᴮ omegaTwo ⊓ ⨆ i, (i ∈ᴮ omegaTwo ⊓ i ∈ᴮ x) ⊓ pair x i ∈ᴮ R := by
    rw [← mem_diagonalUnion]
    exact inf_le_right
  obtain ⟨i, Hi⟩ := exists_convert (Hx.trans inf_le_right)
    (B_ext_inf (B_ext_inf B_ext_mem_left B_ext_mem_left) B_ext_pair_mem_right)
  have Htotal : Δ ≤ ⨆ C, C ∈ᴮ bv_powerset omegaTwo ⊓ pair i C ∈ᴮ F :=
    (le_inf (inf_le_left.trans ((HF.trans inf_le_right).trans (iInf_le _ i)))
      (Hi.trans (inf_le_left.trans inf_le_left))).trans bv_imp_elim
  obtain ⟨C, HC⟩ := exists_convert Htotal (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have HavoidC : Δ ≤ ErdosIdeal.fiber omegaTwo R i ⊆ᴮ difference omegaTwo C :=
    (le_inf (inf_le_left.trans (Havoid.trans ((iInf_le _ i).trans (iInf_le _ C))))
      (le_inf (Hi.trans (inf_le_left.trans inf_le_left)) (HC.trans inf_le_right))).trans
      bv_imp_elim
  have Hxfiber : Δ ≤ x ∈ᴮ ErdosIdeal.fiber omegaTwo R i := by
    rw [ErdosIdeal.mem_fiber]
    exact le_inf (Hx.trans inf_le_left) (Hi.trans inf_le_right)
  have HxnotC : Δ ≤ (x ∈ᴮ C)ᶜ := by
    have Hdifference := mem_of_mem_subset HavoidC Hxfiber
    rw [mem_difference] at Hdifference
    exact Hdifference.trans inf_le_right
  rw [mem_difference]
  refine le_inf (Hx.trans inf_le_left) ?_
  rw [← imp_bot, ← deduction]
  have HxC : Δ ⊓ x ∈ᴮ diagonalClub F ≤ x ∈ᴮ C := diagonalClub_apply
    inf_le_right (inf_le_left.trans (Hi.trans (inf_le_left.trans inf_le_right)))
    (inf_le_left.trans (HC.trans inf_le_right))
  exact bv_absurd _ HxC (inf_le_left.trans HxnotC)

/-- The actual diagonal club witnesses nonstationarity of the diagonal
union of any internally indexed family of nonstationary inverse fibers. -/
theorem diagonalUnion_mem_nonstationaryIdeal {R : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (Hfibers : Γ ≤ ⨅ i, _root_.imp (i ∈ᴮ omegaTwo)
      (ErdosIdeal.fiber omegaTwo R i ∈ᴮ nonstationaryIdeal)) :
    Γ ≤ diagonalUnion omegaTwo R ∈ᴮ nonstationaryIdeal := by
  obtain ⟨F, HF⟩ := exists_avoiding_fiber_club_family Hfibers
  have Hfunction := is_func'_of_is_function (HF.trans inf_le_left)
  have Hclubs : Γ ≤ ⨅ i, ⨅ C, _root_.imp (i ∈ᴮ omegaTwo ⊓ pair i C ∈ᴮ F) (club omegaTwo C) := by
    apply le_iInf
    intro i
    apply le_iInf
    intro C
    rw [← deduction]
    exact ((le_inf (inf_le_left.trans ((HF.trans inf_le_right).trans
      ((iInf_le _ i).trans (iInf_le _ C)))) inf_le_right).trans bv_imp_elim).trans
      inf_le_left
  have Havoid : Γ ≤ ⨅ i, ⨅ C, _root_.imp (i ∈ᴮ omegaTwo ⊓ pair i C ∈ᴮ F)
      (ErdosIdeal.fiber omegaTwo R i ⊆ᴮ difference omegaTwo C) := by
    apply le_iInf
    intro i
    apply le_iInf
    intro C
    rw [← deduction]
    exact ((le_inf (inf_le_left.trans ((HF.trans inf_le_right).trans
      ((iInf_le _ i).trans (iInf_le _ C)))) inf_le_right).trans bv_imp_elim).trans
      inf_le_right
  exact mem_nonstationaryIdeal_of_club (club_diagonalClub HCH Hfunction Hclubs)
    (diagonalUnion_avoids_diagonalClub Hfunction Havoid)

/-- Normality is proved for the explicitly defined ideal name. -/
theorem nonstationaryIdeal_diagonalClosure {Γ : 𝔹} (HCH : Γ ≤ (CH : 𝔹)) :
    Γ ≤ diagonalClosure omegaTwo (nonstationaryIdeal : bSet 𝔹) := by
  apply le_iInf
  intro R
  rw [← deduction]
  exact diagonalUnion_mem_nonstationaryIdeal (inf_le_left.trans HCH) inf_le_right

end bSet.ErdosNonstationary
