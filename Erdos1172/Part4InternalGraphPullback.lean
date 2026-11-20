/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalGraphNeighborhood
public import Erdos1172.Part4InternalPartitionOrder

@[expose] public section

/-!
# Pulling an internal coloring back along an increasing graph

The pulled-back relation is a genuine subset of the source square. Its
membership and complementary membership both agree with the original
relation at corresponding graph values. Increasingness reflects the
orientation on an ordinal source, so both symmetric graph colors agree,
including on Boolean pieces where the vertices coincide. All statements
are local to the original Boolean condition and quantify over arbitrary
names. No preservation or external enumeration premise is supplied.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosGraphPullback

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosPartition ErdosRelationGraph

def pullbackEdge (R e i j : bSet 𝔹) : 𝔹 :=
  ⨆ x, ⨆ y, (pair i x ∈ᴮ e ⊓ pair j y ∈ᴮ e) ⊓ pair x y ∈ᴮ R

private theorem pullbackEdge_ext_left (R e j : bSet 𝔹) :
    B_ext (fun i => pullbackEdge R e i j) :=
  B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
    B_ext_inf (B_ext_inf B_ext_pair_mem_left B_ext_const) B_ext_const))

private theorem pullbackEdge_ext_right (R e i : bSet 𝔹) :
    B_ext (pullbackEdge R e i) :=
  B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
    B_ext_inf (B_ext_inf B_ext_const B_ext_pair_mem_left) B_ext_const))

def pullbackRelation (κ R e : bSet 𝔹) : bSet 𝔹 :=
  relationGraph κ κ (pullbackEdge R e)

theorem mem_pullbackRelation {κ R e i j : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair i j ∈ᴮ pullbackRelation κ R e ↔
      Γ ≤ i ∈ᴮ κ ∧ Γ ≤ j ∈ᴮ κ ∧ Γ ≤ pullbackEdge R e i j :=
  mem_relationGraph_iff (pullbackEdge_ext_left R e) (pullbackEdge_ext_right R e)

/-- Functionality identifies all possible internal output witnesses. -/
theorem mem_pullbackRelation_iff {κ R e i j x y : bSet 𝔹} {Γ : 𝔹}
    (Hfunc : Γ ≤ is_func e) (Hi : Γ ≤ i ∈ᴮ κ) (Hj : Γ ≤ j ∈ᴮ κ)
    (Hix : Γ ≤ pair i x ∈ᴮ e) (Hjy : Γ ≤ pair j y ∈ᴮ e) :
    Γ ≤ pair i j ∈ᴮ pullbackRelation κ R e ↔ Γ ≤ pair x y ∈ᴮ R := by
  constructor
  · intro H
    have Hedges := (mem_pullbackRelation.mp H).2.2
    apply (le_inf le_rfl Hedges).trans
    change Γ ⊓ (⨆ x', ⨆ y',
      (pair i x' ∈ᴮ e ⊓ pair j y' ∈ᴮ e) ⊓ pair x' y' ∈ᴮ R) ≤ _
    rw [inf_iSup_eq]
    apply iSup_le
    intro x'
    rw [inf_iSup_eq]
    apply iSup_le
    intro y'
    let Δ := Γ ⊓ ((pair i x' ∈ᴮ e ⊓ pair j y' ∈ᴮ e) ⊓ pair x' y' ∈ᴮ R)
    have Hxx : Δ ≤ x =ᴮ x' := eq_of_is_func_of_eq (inf_le_left.trans Hfunc)
      bv_refl (inf_le_left.trans Hix)
      (inf_le_right.trans (inf_le_left.trans inf_le_left))
    have Hyy : Δ ≤ y =ᴮ y' := eq_of_is_func_of_eq (inf_le_left.trans Hfunc)
      bv_refl (inf_le_left.trans Hjy)
      (inf_le_right.trans (inf_le_left.trans inf_le_right))
    exact bv_rw' (ϕ := fun z => pair z y ∈ᴮ R) Hxx
      (h_congr := B_ext_pair_mem_left)
      (H_new := bv_rw' (ϕ := fun z => pair x' z ∈ᴮ R) Hyy
        (h_congr := B_ext_pair_mem_right) (H_new := inf_le_right.trans inf_le_right))
  · intro H
    exact mem_pullbackRelation.mpr ⟨Hi, Hj,
      le_iSup_of_le x (le_iSup_of_le y (le_inf (le_inf Hix Hjy) H))⟩

/-- The complement color is transported locally as well as membership. -/
theorem orientedColor_pullback_iff (color : Bool)
    {κ R e i j x y : bSet 𝔹} {Γ : 𝔹}
    (Hfunc : Γ ≤ is_func e) (Hi : Γ ≤ i ∈ᴮ κ) (Hj : Γ ≤ j ∈ᴮ κ)
    (Hix : Γ ≤ pair i x ∈ᴮ e) (Hjy : Γ ≤ pair j y ∈ᴮ e) :
    Γ ≤ (if color then pair i j ∈ᴮ pullbackRelation κ R e
      else (pair i j ∈ᴮ pullbackRelation κ R e)ᶜ) ↔
    Γ ≤ (if color then pair x y ∈ᴮ R else (pair x y ∈ᴮ R)ᶜ) := by
  cases color with
  | true => exact mem_pullbackRelation_iff Hfunc Hi Hj Hix Hjy
  | false =>
      change Γ ≤ (pair i j ∈ᴮ pullbackRelation κ R e)ᶜ ↔
        Γ ≤ (pair x y ∈ᴮ R)ᶜ
      constructor
      · intro H
        rw [← imp_bot, ← deduction]
        have Hmem := (mem_pullbackRelation_iff
          (inf_le_left.trans Hfunc) (inf_le_left.trans Hi) (inf_le_left.trans Hj)
          (inf_le_left.trans Hix) (inf_le_left.trans Hjy)).mpr
            (show Γ ⊓ pair x y ∈ᴮ R ≤ pair x y ∈ᴮ R from inf_le_right)
        exact bv_absurd _ Hmem (inf_le_left.trans H)
      · intro H
        rw [← imp_bot, ← deduction]
        have Hmem := (mem_pullbackRelation_iff
          (inf_le_left.trans Hfunc) (inf_le_left.trans Hi) (inf_le_left.trans Hj)
          (inf_le_left.trans Hix) (inf_le_left.trans Hjy)).mp
            (show Γ ⊓ pair i j ∈ᴮ pullbackRelation κ R e ≤
              pair i j ∈ᴮ pullbackRelation κ R e from inf_le_right)
        exact bv_absurd _ Hmem (inf_le_left.trans H)

/-- An increasing functional graph reflects strict membership on its
ordinal source. No ordinal or support condition on the outputs is needed. -/
theorem increasingOn_mem_iff {κ e i j x y : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ) (Hfunc : Γ ≤ is_func e)
    (Hinc : Γ ≤ increasingOn κ e) (Hi : Γ ≤ i ∈ᴮ κ) (Hj : Γ ≤ j ∈ᴮ κ)
    (Hix : Γ ≤ pair i x ∈ᴮ e) (Hjy : Γ ≤ pair j y ∈ᴮ e) :
    Γ ≤ i ∈ᴮ j ↔ Γ ≤ x ∈ᴮ y := by
  constructor
  · intro Hij
    exact increasingOn_apply Hinc Hi Hj Hij Hix Hjy
  · intro Hxy
    have Htri := epsilon_trichotomy_of_Ord Hi Hj Hκ
    apply (le_inf le_rfl Htri).trans
    rw [inf_sup_left, inf_sup_left]
    apply sup_le
    · apply sup_le
      · have Heq : Γ ⊓ i =ᴮ j ≤ x =ᴮ y := eq_of_is_func_of_eq
          (inf_le_left.trans Hfunc) inf_le_right
          (inf_le_left.trans Hix) (inf_le_left.trans Hjy)
        exact (bot_of_mem_self' (mem_congr Heq bv_refl
          (inf_le_left.trans Hxy))).trans bot_le
      · exact inf_le_right
    · have Hyx : Γ ⊓ j ∈ᴮ i ≤ y ∈ᴮ x := increasingOn_apply
        (inf_le_left.trans Hinc) (inf_le_left.trans Hj) (inf_le_left.trans Hi)
        inf_le_right (inf_le_left.trans Hjy) (inf_le_left.trans Hix)
      exact (bot_of_mem_mem' x y (inf_le_left.trans Hxy) Hyx).trans bot_le

end bSet.ErdosGraphPullback
