/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalDiagonalIntersection
public import Erdos1172.Part4InternalCountablePast
public import Erdos1172.Part4InternalLargeDifference

@[expose] public section

/-!
Normality supplies a concrete co-large set of closure points for any actual
omega-one selfmap: every earlier index has an earlier value. The failure
relation has small inverse fibers, each contained in the past of one
ordinal. No club, closure-point, or successful-run premise is assumed.
-/

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosClosurePoints

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosRelationGraph ErdosCountablePast
open ErdosColargeIntersection

def closureRelation (h : bSet 𝔹) : bSet 𝔹 :=
  relationGraph omegaOne omegaOne (fun x i => ⨆ v, pair i v ∈ᴮ h ⊓ (v ∈ᴮ x)ᶜ)

private theorem closure_ext_left (h i : bSet 𝔹) :
    B_ext (fun x => ⨆ v, pair i v ∈ᴮ h ⊓ (v ∈ᴮ x)ᶜ) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_const (B_ext_neg (h := B_ext_mem_right)))

private theorem closure_ext_right (h x : bSet 𝔹) :
    B_ext (fun i => ⨆ v, pair i v ∈ᴮ h ⊓ (v ∈ᴮ x)ᶜ) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_pair_mem_left B_ext_const)

theorem mem_closureRelation_iff {h x i : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair x i ∈ᴮ closureRelation h ↔
      (Γ ≤ x ∈ᴮ omegaOne) ∧ (Γ ≤ i ∈ᴮ omegaOne) ∧
        Γ ≤ ⨆ v, pair i v ∈ᴮ h ⊓ (v ∈ᴮ x)ᶜ :=
  mem_relationGraph_iff (closure_ext_left h) (closure_ext_right h)

theorem singleton_past_small {J v : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J) (Hv : Γ ≤ v ∈ᴮ omegaOne) :
    Γ ≤ past ({v} : bSet 𝔹) ∈ᴮ J := by
  have Hsub : Γ ≤ ({v} : bSet 𝔹) ⊆ᴮ omegaOne := by
    rw [subset_unfold']
    apply le_iInf
    intro x
    rw [← deduction]
    exact mem_congr (eq_of_mem_singleton inf_le_right) bv_refl (inf_le_left.trans Hv)
  exact past_small HJ Habsorb Hclosure Hsub
    (ErdosLargeDifference.singleton_injects_of_mem (b := bSet.of_nat 0) of_nat_mem_omega)

theorem mem_singleton_past_of_not_after {v x : bSet 𝔹} {Γ : 𝔹}
    (Hv : Γ ≤ v ∈ᴮ omegaOne) (Hx : Γ ≤ x ∈ᴮ omegaOne)
    (Hnot : Γ ≤ (v ∈ᴮ x)ᶜ) : Γ ≤ x ∈ᴮ past ({v} : bSet 𝔹) := by
  have Hcases := epsilon_trichotomy_of_Ord Hx Hv omegaOne_Ord
  apply (le_inf (le_refl Γ) Hcases).trans
  rw [inf_sup_left, inf_sup_left]
  apply sup_le
  · apply sup_le
    · change Γ ⊓ x =ᴮ v ≤ x ∈ᴮ binary_union ({v} : bSet 𝔹) (bv_union ({v} : bSet 𝔹))
      rw [mem_binary_union]
      exact (mem_singleton_of_eq (bv_symm inf_le_right)).trans le_sup_left
    · change Γ ⊓ x ∈ᴮ v ≤ x ∈ᴮ binary_union ({v} : bSet 𝔹) (bv_union ({v} : bSet 𝔹))
      rw [mem_binary_union]
      exact (mem_bv_union_iff.mpr (le_iSup_of_le v
        (le_inf (le_top.trans mem_singleton) inf_le_right))).trans le_sup_right
  · exact (bv_absurd _ inf_le_right (inf_le_left.trans Hnot)).trans bot_le

theorem closure_fiber_subset {h i v : bSet 𝔹} {Γ : 𝔹}
    (Hfunc : Γ ≤ is_func h) (Hiv : Γ ≤ pair i v ∈ᴮ h)
    (Hv : Γ ≤ v ∈ᴮ omegaOne) :
    Γ ≤ ErdosIdeal.fiber omegaOne (closureRelation h) i ⊆ᴮ past ({v} : bSet 𝔹) := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  let Δ := Γ ⊓ x ∈ᴮ ErdosIdeal.fiber omegaOne (closureRelation h) i
  have Hx : Δ ≤ x ∈ᴮ omegaOne ⊓ pair x i ∈ᴮ closureRelation h := by
    rw [← ErdosIdeal.mem_fiber]
    exact inf_le_right
  obtain ⟨w, Hw⟩ := exists_convert
    (mem_closureRelation_iff.mp (Hx.trans inf_le_right)).2.2
    (B_ext_inf B_ext_pair_mem_right (B_ext_neg (h := B_ext_mem_left)))
  have Hvw : Δ ≤ v =ᴮ w := eq_of_is_func_of_eq (inf_le_left.trans Hfunc) bv_refl
    (inf_le_left.trans Hiv) (Hw.trans inf_le_left)
  exact mem_singleton_past_of_not_after (inf_le_left.trans Hv) (Hx.trans inf_le_left)
    (bv_rw' (ϕ := fun a => (a ∈ᴮ x)ᶜ) Hvw
      (h_congr := B_ext_neg (h := B_ext_mem_left)) (H_new := Hw.trans inf_le_right))

def closurePoints (h : bSet 𝔹) : bSet 𝔹 :=
  difference omegaOne (diagonalUnion omegaOne (closureRelation h))

theorem closurePoints_colarge {J h : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hnormal : Γ ≤ diagonalClosure omegaOne J)
    (Hh : Γ ≤ is_func' omegaOne omegaOne h) :
    Γ ≤ colarge omegaOne J (closurePoints h) := by
  have Hfibers : Γ ≤ ⨅ i, _root_.imp (i ∈ᴮ omegaOne)
      (ErdosIdeal.fiber omegaOne (closureRelation h) i ∈ᴮ J) := by
    apply le_iInf
    intro i
    rw [← deduction]
    let Δ := Γ ⊓ i ∈ᴮ omegaOne
    have Hex : Δ ≤ ⨆ v, v ∈ᴮ omegaOne ⊓ pair i v ∈ᴮ h :=
      (le_inf (inf_le_left.trans ((Hh.trans inf_le_right).trans (iInf_le _ i)))
        inf_le_right).trans bv_imp_elim
    obtain ⟨v, Hv⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
    exact small_of_subset (downwardClosed_of_isIdeal (inf_le_left.trans HJ))
      (singleton_past_small (inf_le_left.trans HJ) (inf_le_left.trans Habsorb)
        (inf_le_left.trans Hclosure) (Hv.trans inf_le_left))
      (closure_fiber_subset (inf_le_left.trans (Hh.trans inf_le_left))
        (Hv.trans inf_le_right) (Hv.trans inf_le_left))
  have Hsmall : Γ ≤ diagonalUnion omegaOne (closureRelation h) ∈ᴮ J :=
    (le_inf (Hnormal.trans (iInf_le _ (closureRelation h))) Hfibers).trans bv_imp_elim
  exact le_inf difference_subset
    (small_of_subset (downwardClosed_of_isIdeal HJ) Hsmall
      (complement_subset_of_remainder_subset subset_self))

theorem closurePoints_apply {h x i v : bSet 𝔹} {Γ : 𝔹}
    (Hx : Γ ≤ x ∈ᴮ closurePoints h) (Hi : Γ ≤ i ∈ᴮ omegaOne)
    (Hix : Γ ≤ i ∈ᴮ x) (Hiv : Γ ≤ pair i v ∈ᴮ h) : Γ ≤ v ∈ᴮ x := by
  have Hdata : Γ ≤ x ∈ᴮ omegaOne ⊓
      (x ∈ᴮ diagonalUnion omegaOne (closureRelation h))ᶜ := by
    simpa only [closurePoints, mem_difference] using Hx
  rw [← compl_compl (v ∈ᴮ x), ← imp_bot, ← deduction]
  let Δ := Γ ⊓ (v ∈ᴮ x)ᶜ
  have Hpair : Δ ≤ pair x i ∈ᴮ closureRelation h :=
    mem_closureRelation_iff.mpr ⟨inf_le_left.trans (Hdata.trans inf_le_left),
      inf_le_left.trans Hi, le_iSup_of_le v (le_inf (inf_le_left.trans Hiv) inf_le_right)⟩
  have Hbad : Δ ≤ x ∈ᴮ diagonalUnion omegaOne (closureRelation h) := by
    rw [mem_diagonalUnion]
    exact le_inf (inf_le_left.trans (Hdata.trans inf_le_left))
      (le_iSup_of_le i (le_inf (le_inf (inf_le_left.trans Hi)
        (inf_le_left.trans Hix)) Hpair))
  exact bv_absurd _ Hbad (inf_le_left.trans (Hdata.trans inf_le_right))

end bSet.ErdosClosurePoints
