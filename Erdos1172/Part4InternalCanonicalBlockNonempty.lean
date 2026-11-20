/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCanonicalBlockEnumeration

@[expose] public section

/-!
# The empty set is not a whole homogeneous block object

A guarded block enumeration has an actual value at zero. Its exact image
is the block object, so this value witnesses nonemptiness at the original
Boolean condition. Thus empty can be used as a failure marker, without
asserting that the family of block objects is itself nonempty.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCanonicalBlocks

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo

/-- The zero-th value of an actual enumeration lies in its whole image. -/
theorem exists_mem_of_blockEnumerationData
    {color : Bool} {R A f : bSet 𝔹} {Γ : 𝔹}
    (Hdata : Γ ≤ blockEnumerationData color R A f) :
    ∃ x : bSet 𝔹, Γ ≤ x ∈ᴮ A := by
  have Hf : Γ ≤ is_function omegaOne omegaTwo f :=
    Hdata.trans (inf_le_left.trans inf_le_left)
  have Hex : Γ ≤ ⨆ x, x ∈ᴮ omegaTwo ⊓ pair (0 : bSet 𝔹) x ∈ᴮ f :=
    (le_inf ((is_total_of_is_function Hf).trans (iInf_le _ (0 : bSet 𝔹)))
      ErdosLargeDifference.zero_mem_omegaOne).trans bv_imp_elim
  obtain ⟨x, Hx⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Him : Γ ≤ x ∈ᴮ image omegaOne omegaTwo f :=
    mem_image (Hx.trans inf_le_right) ErdosLargeDifference.zero_mem_omegaOne
      (Hx.trans inf_le_left)
  exact ⟨x, mem_congr bv_refl
    (Hdata.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))) Him⟩

/-- A member of the block family has a same-condition actual member. -/
theorem exists_mem_of_mem_blockObjects
    {color : Bool} {R A : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ A ∈ᴮ blockObjects color R) :
    ∃ x : bSet 𝔹, Γ ≤ x ∈ᴮ A := by
  obtain ⟨f, Hf⟩ := exists_block_enumeration HA
  exact exists_mem_of_blockEnumerationData Hf

theorem blockObject_nonempty {color : Bool} {R A : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ A ∈ᴮ blockObjects color R) :
    Γ ≤ (A =ᴮ (∅ : bSet 𝔹))ᶜ := by
  obtain ⟨x, Hx⟩ := exists_mem_of_mem_blockObjects HA
  exact nonempty_of_exists_mem A (le_iSup_of_le x Hx)

end bSet.ErdosCanonicalBlocks
