/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCanonicalBlockEnumeration
public import Erdos1172.Part4InternalIndependentHomogeneous

@[expose] public section

/-!
# Exact whole-image transport for constructed blocks

An increasing homogeneous graph into a future is retained unchanged when
its codomain is widened to omega-two. Its exact global image is a block
object still contained in that future. The membership/range equivalences
also apply to every previously selected canonical enumeration, so neither
new nor old whole block objects are replaced by arbitrary subsets.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosBlockImageTransfer

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosCanonicalBlocks
open ErdosIndependentHomogeneous

/-- The same graph has global supported injection, order, homogeneity,
and exact-image data. There is no change of its coordinates. -/
theorem block_image_data {color : Bool} {R L f : bSet 𝔹} {Γ : 𝔹}
    (HL : Γ ≤ L ⊆ᴮ omegaTwo)
    (Hf : Γ ≤ is_injective_function omegaOne L f)
    (Hinc : Γ ≤ increasingOn omegaOne f)
    (Hhom : Γ ≤ homogeneousUnion color R omegaOne omegaOne f f) :
    Γ ≤ blockEnumerationData color R (image omegaOne omegaTwo f) f :=
  le_inf (is_injective_function_codomain_mono HL Hf)
    (le_inf Hinc (le_inf Hhom bv_refl))

theorem block_image_mem_objects {color : Bool} {R L f : bSet 𝔹} {Γ : 𝔹}
    (HL : Γ ≤ L ⊆ᴮ omegaTwo)
    (Hf : Γ ≤ is_injective_function omegaOne L f)
    (Hinc : Γ ≤ increasingOn omegaOne f)
    (Hhom : Γ ≤ homogeneousUnion color R omegaOne omegaOne f f) :
    Γ ≤ image omegaOne omegaTwo f ∈ᴮ blockObjects color R :=
  blockEnumerationData_mem_object (block_image_data HL Hf Hinc Hhom)

/-- Even weak total functionality forces every vertex of the global
bounded image to remain in the original future. -/
theorem block_image_subset_future {L f : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' omegaOne L f) :
    Γ ≤ image omegaOne omegaTwo f ⊆ᴮ L := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  exact rangeMem_le_codomain (inf_le_left.trans Hf)
    ((mem_image_iff.mp (show Γ ⊓ x ∈ᴮ image omegaOne omegaTwo f ≤
      x ∈ᴮ image omegaOne omegaTwo f from inf_le_right)).2)

/-- Used-range membership is exactly membership in the global whole
image, at the same Boolean condition. -/
theorem rangeMem_iff_block_image {L f x : bSet 𝔹} {Γ : 𝔹}
    (HL : Γ ≤ L ⊆ᴮ omegaTwo)
    (Hf : Γ ≤ is_injective_function omegaOne L f) :
    Γ ≤ rangeMem omegaOne f x ↔ Γ ≤ x ∈ᴮ image omegaOne omegaTwo f := by
  have Hweak : Γ ≤ is_func' omegaOne omegaTwo f :=
    is_func'_of_is_function ((is_injective_function_codomain_mono HL Hf).trans inf_le_left)
  constructor
  · intro Hx
    exact mem_image_iff.mpr ⟨rangeMem_le_codomain Hweak Hx, Hx⟩
  · intro Hx
    exact (mem_image_iff.mp Hx).2

/-- The object of any actual selected enumeration is its entire guarded
range, not only a set containing that range. -/
theorem blockObject_mem_iff_range
    {color : Bool} {R B r x : bSet 𝔹} {Γ : 𝔹}
    (Hdata : Γ ≤ blockEnumerationData color R B r) :
    Γ ≤ x ∈ᴮ B ↔ Γ ≤ rangeMem omegaOne r x := by
  have Heq : Γ ≤ image omegaOne omegaTwo r =ᴮ B :=
    Hdata.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  have Hweak : Γ ≤ is_func' omegaOne omegaTwo r :=
    Hdata.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
  constructor
  · intro Hx
    exact (mem_image_iff.mp (mem_congr bv_refl (bv_symm Heq) Hx)).2
  · intro Hx
    exact mem_congr bv_refl Heq
      (mem_image_iff.mpr ⟨rangeMem_le_codomain Hweak Hx, Hx⟩)

theorem rangeMem_of_blockObject_mem
    {color : Bool} {R B r x : bSet 𝔹} {Γ : 𝔹}
    (Hdata : Γ ≤ blockEnumerationData color R B r) (Hx : Γ ≤ x ∈ᴮ B) :
    Γ ≤ rangeMem omegaOne r x :=
  (blockObject_mem_iff_range Hdata).mp Hx

theorem blockObject_mem_of_rangeMem
    {color : Bool} {R B r x : bSet 𝔹} {Γ : 𝔹}
    (Hdata : Γ ≤ blockEnumerationData color R B r)
    (Hx : Γ ≤ rangeMem omegaOne r x) : Γ ≤ x ∈ᴮ B :=
  (blockObject_mem_iff_range Hdata).mpr Hx

end bSet.ErdosBlockImageTransfer
