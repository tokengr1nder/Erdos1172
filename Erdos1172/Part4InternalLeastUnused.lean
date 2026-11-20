/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalIncreasingPartial
public import Erdos1172.Part4InternalIdealSemantics

@[expose] public section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosIncreasingPartial

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosPartition ErdosPartialInjection ErdosIdeal

theorem partial_not_rangeMem_iff_image {θ A f x : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ partialGraph θ A f) :
    Γ ≤ (rangeMem θ f x)ᶜ ↔
      Γ ≤ (x ∈ᴮ image (graphDomain θ A f) A f)ᶜ := by
  constructor
  · intro H
    rw [← imp_bot, ← deduction]
    exact bv_absurd _
      ((partial_rangeMem_iff_image (inf_le_left.trans Hf)).mpr inf_le_right)
      (inf_le_left.trans H)
  · intro H
    rw [← imp_bot, ← deduction]
    exact bv_absurd _
      ((partial_rangeMem_iff_image (inf_le_left.trans Hf)).mp inf_le_right)
      (inf_le_left.trans H)

/-- Regularity supplies a membership-minimal unused point, at the original
Boolean context. Neither ordinal structure nor initiality is assumed here. -/
theorem exists_least_unused {θ A f u : bSet 𝔹} {Γ : 𝔹}
    (Hpartial : Γ ≤ partialGraph θ A f) (Hu : Γ ≤ u ∈ᴮ A)
    (Hnotu : Γ ≤ (rangeMem θ f u)ᶜ) :
    ∃ y : bSet 𝔹, (Γ ≤ y ∈ᴮ A) ∧ (Γ ≤ (rangeMem θ f y)ᶜ) ∧
      Γ ≤ ⨅ z, _root_.imp (z ∈ᴮ A ⊓ z ∈ᴮ y) (rangeMem θ f z) := by
  let U := difference A (image (graphDomain θ A f) A f)
  have HuU : Γ ≤ u ∈ᴮ U := by
    change Γ ≤ u ∈ᴮ difference A (image (graphDomain θ A f) A f)
    rw [mem_difference]
    exact le_inf Hu ((partial_not_rangeMem_iff_image Hpartial).mp Hnotu)
  have Hnonempty : Γ ≤ (U =ᴮ ∅)ᶜ :=
    nonempty_of_exists_mem U (le_iSup_of_le u HuU)
  have Hext : B_ext (fun y : bSet 𝔹 => y ∈ᴮ U ⊓
      (⨅ z, _root_.imp (z ∈ᴮ U) (z ∈ᴮ y)ᶜ)) :=
    B_ext_inf B_ext_mem_left (B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_neg (h := B_ext_mem_right))))
  obtain ⟨y, Hy⟩ := exists_convert (bSet_axiom_of_regularity U Hnonempty) Hext
  have HyU : Γ ≤ y ∈ᴮ A ⊓ (y ∈ᴮ image (graphDomain θ A f) A f)ᶜ := by
    rw [← mem_difference]
    exact Hy.trans inf_le_left
  refine ⟨y, HyU.trans inf_le_left,
    (partial_not_rangeMem_iff_image Hpartial).mpr (HyU.trans inf_le_right), ?_⟩
  apply le_iInf
  intro z
  rw [← deduction]
  let Δ := Γ ⊓ (z ∈ᴮ A ⊓ z ∈ᴮ y)
  have Hnotnot : Δ ≤ ((rangeMem θ f z)ᶜ)ᶜ := by
    rw [← imp_bot, ← deduction]
    let Ξ := Δ ⊓ (rangeMem θ f z)ᶜ
    have HΞΓ : Ξ ≤ Γ := inf_le_left.trans inf_le_left
    have HzU : Ξ ≤ z ∈ᴮ U := by
      change Ξ ≤ z ∈ᴮ difference A (image (graphDomain θ A f) A f)
      rw [mem_difference]
      exact le_inf (inf_le_left.trans (inf_le_right.trans inf_le_left))
        ((partial_not_rangeMem_iff_image (HΞΓ.trans Hpartial)).mp inf_le_right)
    have Hnotzy : Ξ ≤ (z ∈ᴮ y)ᶜ :=
      (le_inf (HΞΓ.trans (Hy.trans (inf_le_right.trans (iInf_le _ z))))
        HzU).trans bv_imp_elim
    exact bv_absurd _ (inf_le_left.trans (inf_le_right.trans inf_le_right)) Hnotzy
  simpa only [compl_compl] using Hnotnot

/-- An unused point lies strictly above an initial used range inside an
ordinal. This is a Boolean theorem about all internal range members. -/
theorem range_below_unused {κ θ A f y : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ) (HA : Γ ≤ A ⊆ᴮ κ)
    (Hpartial : Γ ≤ partialGraph θ A f)
    (Hrange : Γ ≤ rangeInitial θ A f) (Hy : Γ ≤ y ∈ᴮ A)
    (Hnoty : Γ ≤ (rangeMem θ f y)ᶜ) :
    Γ ≤ ⨅ x, _root_.imp (rangeMem θ f x) (x ∈ᴮ y) := by
  apply le_iInf
  intro x
  rw [← deduction]
  let Δ := Γ ⊓ rangeMem θ f x
  have HxImage : Δ ≤ x ∈ᴮ image (graphDomain θ A f) A f :=
    (partial_rangeMem_iff_image (inf_le_left.trans Hpartial)).mp inf_le_right
  have HxA : Δ ≤ x ∈ᴮ A := mem_of_mem_subset image_subset HxImage
  have Hxκ : Δ ≤ x ∈ᴮ κ := mem_of_mem_subset (inf_le_left.trans HA) HxA
  have Hyκ : Δ ≤ y ∈ᴮ κ := inf_le_left.trans (mem_of_mem_subset HA Hy)
  have Htri := epsilon_trichotomy_of_Ord Hxκ Hyκ (inf_le_left.trans Hκ)
  change Δ ≤ x ∈ᴮ y
  apply (le_inf (le_refl Δ) Htri).trans
  rw [inf_sup_left, inf_sup_left]
  apply sup_le
  · apply sup_le
    · have Hyrange : Δ ⊓ x =ᴮ y ≤ rangeMem θ f y :=
        bv_rw'' (ϕ := rangeMem θ f) inf_le_right
          (inf_le_left.trans inf_le_right) (rangeMem_ext_value θ f)
      exact (bv_absurd _ Hyrange
        (inf_le_left.trans (inf_le_left.trans Hnoty))).trans bot_le
    · exact inf_le_right
  · have Hyrange : Δ ⊓ y ∈ᴮ x ≤ rangeMem θ f y :=
      rangeInitial_apply (inf_le_left.trans (inf_le_left.trans Hrange))
        (inf_le_left.trans inf_le_right)
        (inf_le_left.trans (inf_le_left.trans Hy)) inf_le_right
    exact (bv_absurd _ Hyrange
      (inf_le_left.trans (inf_le_left.trans Hnoty))).trans bot_le

end bSet.ErdosIncreasingPartial
