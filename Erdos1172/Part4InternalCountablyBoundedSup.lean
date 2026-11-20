/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalOmegaOneIdealBounded
public import Erdos1172.Part4InternalSmallFamilyUnion
public import Erdos1172.Part4InternalClubs

@[expose] public section

/-!
# Countable boundedness of increasing omega-one suprema

The supremum is the actual union of the internal image of a supported
increasing function. Given an arbitrary internally countable subset of
this supremum, bounded choice selects one witnessing domain index for
each element. The selected image is countable and hence bounded in
omega-one. A later function value bounds the original subset strictly.
No set of all witnessing indices is asserted countable, and no external
enumeration or regularity assumption replaces the explicit premise.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCountablyBoundedSup

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosOmegaOneIdealBounded ErdosPartition ErdosClubs
open ErdosCountableImage ErdosSmallFamilyUnion ErdosLargeDifference

theorem countablyBounded_ext : B_ext (countablyBounded : bSet 𝔹 → 𝔹) :=
  B_ext_iInf (h := fun _ => B_ext_imp
    (h₁ := B_ext_inf B_ext_subset_right B_ext_const)
    (h₂ := B_ext_iSup (h := fun _ => B_ext_inf B_ext_mem_right B_ext_const)))

/-- The countable-boundedness value supplies a single actual bound at
the original condition, including when the countable subset is empty. -/
theorem exists_bound_of_countablyBounded {κ T : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ countablyBounded κ) (HT : Γ ≤ T ⊆ᴮ κ)
    (Hcount : Γ ≤ injects_into T bSet.omega) :
    ∃ b : bSet 𝔹, Γ ≤ b ∈ᴮ κ ⊓ T ⊆ᴮ b :=
  exists_convert
    ((le_inf (HB.trans (iInf_le _ T)) (le_inf HT Hcount)).trans bv_imp_elim)
    (B_ext_inf B_ext_mem_left B_ext_subset_right)

/-- Singleton countability makes a countably bounded ordinal have a
strictly later member above each of its members. -/
theorem exists_above_of_countablyBounded {κ i : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ countablyBounded κ) (Hi : Γ ≤ i ∈ᴮ κ) :
    ∃ j : bSet 𝔹, Γ ≤ j ∈ᴮ κ ⊓ i ∈ᴮ j := by
  have Hsub : Γ ≤ ({i} : bSet 𝔹) ⊆ᴮ κ := by
    rw [subset_unfold']
    apply le_iInf
    intro x
    rw [← deduction]
    exact mem_congr (bv_symm (eq_mem_singleton inf_le_right)) bv_refl
      (inf_le_left.trans Hi)
  have Hcount : Γ ≤ injects_into ({i} : bSet 𝔹) bSet.omega :=
    singleton_injects_of_mem (b := of_nat 0) of_nat_mem_omega
  obtain ⟨j, Hj⟩ := exists_bound_of_countablyBounded HB Hsub Hcount
  exact ⟨j, le_inf (Hj.trans inf_le_left)
    (mem_of_mem_subset (Hj.trans inf_le_right) (mem_singleton_of_eq bv_refl))⟩

def increasingSup (C f : bSet 𝔹) : bSet 𝔹 :=
  bv_union (image omegaOne C f)

/-- Every value lies strictly below the actual supremum. A later domain
index is constructed from countable boundedness, not assumed to exist. -/
theorem increasing_value_mem_sup {C f i y : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ countablyBounded omegaOne)
    (Hf : Γ ≤ is_function omegaOne C f)
    (Hinc : Γ ≤ increasingOn omegaOne f)
    (Hi : Γ ≤ i ∈ᴮ omegaOne) (Hiy : Γ ≤ pair i y ∈ᴮ f) :
    Γ ≤ y ∈ᴮ increasingSup C f := by
  obtain ⟨j, Hj⟩ := exists_above_of_countablyBounded HB Hi
  have Hex : Γ ≤ ⨆ z, z ∈ᴮ C ⊓ pair j z ∈ᴮ f :=
    (le_inf ((is_total_of_is_function Hf).trans (iInf_le _ j))
      (Hj.trans inf_le_left)).trans bv_imp_elim
  obtain ⟨z, Hz⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  exact mem_indexed_union_of_value Hf (Hj.trans inf_le_left) (Hz.trans inf_le_right)
    (increasingOn_apply Hinc Hi (Hj.trans inf_le_left) (Hj.trans inf_le_right)
      Hiy (Hz.trans inf_le_right))

theorem increasingSup_nonempty {C f : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ countablyBounded omegaOne)
    (Hf : Γ ≤ is_function omegaOne C f)
    (Hinc : Γ ≤ increasingOn omegaOne f) :
    Γ ≤ (increasingSup C f =ᴮ (∅ : bSet 𝔹))ᶜ := by
  have Hex : Γ ≤ ⨆ y, y ∈ᴮ C ⊓ pair (0 : bSet 𝔹) y ∈ᴮ f :=
    (le_inf ((is_total_of_is_function Hf).trans (iInf_le _ (0 : bSet 𝔹)))
      zero_mem_omegaOne).trans bv_imp_elim
  obtain ⟨y, Hy⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  exact nonempty_of_exists_mem (increasingSup C f) (le_iSup_of_le y
    (increasing_value_mem_sup HB Hf Hinc zero_mem_omegaOne (Hy.trans inf_le_right)))

/-- The range is strictly cofinal in the union, with arbitrary internal
points and graph indices, not just ground representatives. -/
theorem increasingSup_cofinal {C f : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ countablyBounded omegaOne)
    (Hf : Γ ≤ is_function omegaOne C f)
    (Hinc : Γ ≤ increasingOn omegaOne f) :
    Γ ≤ unboundedIn (increasingSup C f) C := by
  apply le_iInf
  intro x
  rw [← deduction]
  let Δ := Γ ⊓ x ∈ᴮ increasingSup C f
  obtain ⟨i, y, Hiy⟩ := exists_indexed_union_witness
    (show Δ ≤ x ∈ᴮ bv_union (image omegaOne C f) from inf_le_right)
  have Hi : Δ ≤ i ∈ᴮ omegaOne := Hiy.trans (inf_le_left.trans inf_le_left)
  have Hpair : Δ ≤ pair i y ∈ᴮ f := Hiy.trans (inf_le_left.trans inf_le_right)
  exact le_iSup_of_le y (le_inf
    (le_inf (mem_codomain_of_is_function Hpair (inf_le_left.trans Hf))
      (increasing_value_mem_sup (inf_le_left.trans HB) (inf_le_left.trans Hf)
        (inf_le_left.trans Hinc) Hi Hpair)) (Hiy.trans inf_le_right))

/-- Select exactly one index witnessing that a given element lies below
a function value. No countability claim about all such indices is made. -/
theorem exists_sup_index_selector {T C f : bSet 𝔹} {Γ : 𝔹}
    (HT : Γ ≤ T ⊆ᴮ increasingSup C f) :
    ∃ h : bSet 𝔹, Γ ≤ is_function T omegaOne h ⊓
      ⨅ x, ⨅ i, _root_.imp (x ∈ᴮ T ⊓ pair x i ∈ᴮ h)
        (⨆ y, pair i y ∈ᴮ f ⊓ x ∈ᴮ y) := by
  apply ErdosSmallFiberBound.exists_selector_of_pointwise
    (P := fun x i => ⨆ y, pair i y ∈ᴮ f ⊓ x ∈ᴮ y)
    (fun _ => B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_mem_left))
    (fun _ => B_ext_iSup (h := fun _ => B_ext_inf B_ext_pair_mem_left B_ext_const))
  apply le_iInf
  intro x
  rw [← deduction]
  obtain ⟨i, y, Hiy⟩ := exists_indexed_union_witness
    (mem_of_mem_subset (inf_le_left.trans HT)
      (show Γ ⊓ x ∈ᴮ T ≤ x ∈ᴮ T from inf_le_right))
  exact le_iSup_of_le i (le_inf (Hiy.trans (inf_le_left.trans inf_le_left))
    (le_iSup_of_le y (le_inf (Hiy.trans (inf_le_left.trans inf_le_right))
      (Hiy.trans inf_le_right))))

/-- Countable boundedness transfers to the supremum of an actual
increasing omega-one function into an ordinal. The countable subset may
be empty or have no externally countable presentation. -/
theorem countablyBounded_increasingSup {C f : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ countablyBounded omegaOne)
    (HC : Γ ≤ C ⊆ᴮ omegaTwo)
    (Hf : Γ ≤ is_function omegaOne C f)
    (Hinc : Γ ≤ increasingOn omegaOne f) :
    Γ ≤ countablyBounded (increasingSup C f) := by
  apply le_iInf
  intro T
  rw [← deduction]
  let Δ := Γ ⊓ (T ⊆ᴮ increasingSup C f ⊓ injects_into T bSet.omega)
  have HfΔ : Δ ≤ is_function omegaOne C f := inf_le_left.trans Hf
  have HincΔ : Δ ≤ increasingOn omegaOne f := inf_le_left.trans Hinc
  obtain ⟨h, Hh⟩ := exists_sup_index_selector
    (show Δ ≤ T ⊆ᴮ increasingSup C f from inf_le_right.trans inf_le_left)
  have Hcount : Δ ≤ injects_into (image T omegaOne h) bSet.omega :=
    image_countable_of_function (Hh.trans inf_le_left) (inf_le_right.trans inf_le_right)
  obtain ⟨j, Hj⟩ := exists_bound_of_countablyBounded (inf_le_left.trans HB)
    (show Δ ≤ image T omegaOne h ⊆ᴮ omegaOne from image_subset) Hcount
  have Hex : Δ ≤ ⨆ y, y ∈ᴮ C ⊓ pair j y ∈ᴮ f :=
    (le_inf ((is_total_of_is_function HfΔ).trans (iInf_le _ j))
      (Hj.trans inf_le_left)).trans bv_imp_elim
  obtain ⟨y, Hy⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have HyOrd : Δ ≤ Ord y := Ord_of_mem_Ord
    (mem_of_mem_subset (inf_le_left.trans HC) (Hy.trans inf_le_left)) omegaTwo_Ord
  apply le_iSup_of_le y
  refine le_inf (increasing_value_mem_sup (inf_le_left.trans HB) HfΔ HincΔ
    (Hj.trans inf_le_left) (Hy.trans inf_le_right)) ?_
  conv_rhs => rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  let Θ := Δ ⊓ x ∈ᴮ T
  have Hiex : Θ ≤ ⨆ i, i ∈ᴮ omegaOne ⊓ pair x i ∈ᴮ h :=
    (le_inf (inf_le_left.trans
      ((is_total_of_is_function (Hh.trans inf_le_left)).trans (iInf_le _ x)))
      (show Θ ≤ x ∈ᴮ T from inf_le_right)).trans bv_imp_elim
  obtain ⟨i, Hi⟩ := exists_convert Hiex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hselected : Θ ≤ ⨆ z, pair i z ∈ᴮ f ⊓ x ∈ᴮ z :=
    (le_inf (inf_le_left.trans ((Hh.trans inf_le_right).trans
      ((iInf_le _ x).trans (iInf_le _ i))))
      (le_inf inf_le_right (Hi.trans inf_le_right))).trans bv_imp_elim
  obtain ⟨z, Hz⟩ := exists_convert Hselected
    (B_ext_inf B_ext_pair_mem_right B_ext_mem_right)
  have Hij : Θ ≤ i ∈ᴮ j := mem_of_mem_subset
    (inf_le_left.trans (Hj.trans inf_le_right))
    (mem_image (Hi.trans inf_le_right) inf_le_right (Hi.trans inf_le_left))
  have Hzy : Θ ≤ z ∈ᴮ y := increasingOn_apply (inf_le_left.trans HincΔ)
    (Hi.trans inf_le_left) (inf_le_left.trans (Hj.trans inf_le_left)) Hij
    (Hz.trans inf_le_left) (inf_le_left.trans (Hy.trans inf_le_right))
  exact mem_of_mem_Ord (Hz.trans inf_le_right) Hzy (inf_le_left.trans HyOrd)

end bSet.ErdosCountablyBoundedSup
