/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalLargeTwoBlock
public import Erdos1172.Part4InternalOrderedDushnikMiller

@[expose] public section

/-!
# Exact two-block targets from large homogeneous injections

The actual image of a homogeneous injection is independent in the opposite
color. Its full internal cardinal size is witnessed by the original graph,
factored through that image. The existing large-independent-set theorem
then constructs the separated omega-one and omega blocks in the same
codomain. No order type is inferred merely from cardinality.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosLargeCliqueTwoBlock

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosIndependentMaximal ErdosOrderedDushnikMiller

theorem not_opposite_of_homogeneous_range
    {color : Bool} {R K f x y : bSet 𝔹} {Γ : 𝔹}
    (Hhom : Γ ≤ homogeneousUnion color R K K f f)
    (Hx : Γ ≤ rangeMem K f x) (Hy : Γ ≤ rangeMem K f y)
    (Hxy : Γ ≤ x ∈ᴮ y) : Γ ≤ (graphColor (!color) R x y)ᶜ := by
  have Hedge : Γ ≤ graphColor color R x y :=
    (le_graphColor_iff_oriented color R Hxy).mpr
      (homogeneousUnion_apply Hhom (Hx.trans le_sup_left) (Hy.trans le_sup_left) Hxy)
  rw [← imp_bot, ← deduction]
  cases color with
  | false => exact (le_inf (inf_le_left.trans Hedge) inf_le_right).trans (graphColor_inf R x y).le
  | true => exact (le_inf inf_le_right (inf_le_left.trans Hedge)).trans (graphColor_inf R x y).le

/-- This statement uses exact guarded image membership and works even for
arbitrary nonordinal input names and nonfunctional graph names. -/
theorem independent_image_of_homogeneous
    {color : Bool} {R K S f : bSet 𝔹} {Γ : 𝔹}
    (Hhom : Γ ≤ homogeneousUnion color R K K f f) :
    Γ ≤ independent (!color) R (image K S f) := by
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction, ← imp_bot, ← deduction]
  let Δ := (Γ ⊓ (x ∈ᴮ image K S f ⊓ y ∈ᴮ image K S f)) ⊓ graphColor (!color) R x y
  have HΔ : Δ ≤ Γ := inf_le_left.trans inf_le_left
  have Hx : Δ ≤ rangeMem K f x := (mem_image_iff.mp (show Δ ≤ x ∈ᴮ image K S f from
      inf_le_left.trans (inf_le_right.trans inf_le_left))).2
  have Hy : Δ ≤ rangeMem K f y := (mem_image_iff.mp (show Δ ≤ y ∈ᴮ image K S f from
      inf_le_left.trans (inf_le_right.trans inf_le_right))).2
  have Horder : Δ ≤ x ∈ᴮ y ⊔ y ∈ᴮ x :=
    (show Δ ≤ graphColor (!color) R x y from inf_le_right).trans
      (sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right))
  apply (le_inf (le_refl Δ) Horder).trans
  rw [inf_sup_left]
  apply sup_le
  · have Hnot := not_opposite_of_homogeneous_range
      (inf_le_left.trans (HΔ.trans Hhom)) (inf_le_left.trans Hx)
      (inf_le_left.trans Hy) (show Δ ⊓ x ∈ᴮ y ≤ x ∈ᴮ y from inf_le_right)
    exact bv_absurd _ (inf_le_left.trans (show Δ ≤ graphColor (!color) R x y from inf_le_right)) Hnot
  · have Hnot := not_opposite_of_homogeneous_range
      (inf_le_left.trans (HΔ.trans Hhom)) (inf_le_left.trans Hy)
      (inf_le_left.trans Hx) (show Δ ⊓ y ∈ᴮ x ≤ y ∈ᴮ x from inf_le_right)
    have Hedge : Δ ⊓ y ∈ᴮ x ≤ graphColor (!color) R y x := by
      rw [graphColor_symm (!color) R y x]
      exact inf_le_left.trans (show Δ ≤ graphColor (!color) R x y from inf_le_right)
    exact bv_absurd _ Hedge Hnot

/-- The original injection witnesses the size of its actual homogeneous
image; existing increasing enumeration constructs the exact target. -/
theorem twoBlock_of_large_homogeneous_injection
    {color : Bool} {R S f : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HS : Γ ≤ S ⊆ᴮ omegaTwo)
    (Hf : Γ ≤ is_injective_function omegaTwo S f)
    (Hhom : Γ ≤ homogeneousUnion color R omegaTwo omegaTwo f f) :
    Γ ≤ hasTwoBlock color R omegaOne bSet.omega S := by
  have Hlarge : Γ ≤ injects_into omegaTwo (image omegaTwo S f) :=
    injects_into_of_injection_into (le_iSup_of_le f (factor_image_is_injective_function Hf))
  simpa only [Bool.not_not] using
    (ErdosLargeTwoBlock.hasTwoBlock_of_large_independent HCH
      (subset_trans' image_subset HS) image_subset Hlarge
      (independent_image_of_homogeneous Hhom))

theorem twoBlock_of_orderedLargeClique
    {color : Bool} {R S : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HS : Γ ≤ S ⊆ᴮ omegaTwo)
    (Hclique : Γ ≤ orderedLargeClique color R S) :
    Γ ≤ hasTwoBlock color R omegaOne bSet.omega S := by
  apply (le_inf le_rfl Hclique).trans
  change Γ ⊓ (⨆ f, is_injective_function omegaTwo S f ⊓
    (increasingOn omegaTwo f ⊓ homogeneousUnion color R omegaTwo omegaTwo f f)) ≤ _
  rw [inf_iSup_eq]
  apply iSup_le
  intro f
  exact twoBlock_of_large_homogeneous_injection (inf_le_left.trans HCH)
    (inf_le_left.trans HS) (inf_le_right.trans inf_le_left)
    (inf_le_right.trans (inf_le_right.trans inf_le_right))

end bSet.ErdosLargeCliqueTwoBlock
