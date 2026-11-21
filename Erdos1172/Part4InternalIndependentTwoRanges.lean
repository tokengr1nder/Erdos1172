/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalIndependentHomogeneous

@[expose] public section

/-!
# Joint homogeneity of two ranges in an independent internal set

Two arbitrary internally total single-valued relations into the same
independent set have a jointly homogeneous domain-guarded union of ranges.
No agreement of their domains, increasingness, injectivity, or separation
is assumed here; those are distinct requirements of the two-block target.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosIndependentHomogeneous

open ErdosPartition ErdosIndependentMaximal

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- Weak maps suffice because the partition semantics only uses pairs
whose arguments belong to the indicated domains. -/
theorem homogeneousUnion_of_independent_func'
    {color : Bool} {R A K L f g : bSet 𝔹} {Γ : 𝔹}
    (Hind : Γ ≤ independent color R A)
    (Hf : Γ ≤ is_func' K A f) (Hg : Γ ≤ is_func' L A g) :
    Γ ≤ homogeneousUnion (!color) R K L f g := by
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ (((rangeMem K f x ⊔ rangeMem L g x) ⊓ (rangeMem K f y ⊔ rangeMem L g y)) ⊓ x ∈ᴮ y)
  have HΔ : Δ ≤ Γ := inf_le_left
  have Hrx : Δ ≤ rangeMem K f x ⊔ rangeMem L g x :=
    inf_le_right.trans (inf_le_left.trans inf_le_left)
  have Hry : Δ ≤ rangeMem K f y ⊔ rangeMem L g y :=
    inf_le_right.trans (inf_le_left.trans inf_le_right)
  have HxA : Δ ≤ x ∈ᴮ A := (le_inf HΔ Hrx).trans (unionRange_le_codomain Hf Hg)
  have HyA : Δ ≤ y ∈ᴮ A := (le_inf HΔ Hry).trans (unionRange_le_codomain Hf Hg)
  exact opposite_oriented_of_not_graphColor (inf_le_right.trans inf_le_right)
    (independent_apply (HΔ.trans Hind) HxA HyA)

/-- Two actual functions into an independent set have a jointly opposite-
color homogeneous range, with arbitrary internal domains and names. -/
theorem homogeneousUnion_of_independent_two_ranges
    {color : Bool} {R A K L f g : bSet 𝔹} {Γ : 𝔹}
    (Hind : Γ ≤ independent color R A)
    (Hf : Γ ≤ is_function K A f) (Hg : Γ ≤ is_function L A g) :
    Γ ≤ homogeneousUnion (!color) R K L f g :=
  homogeneousUnion_of_independent_func' Hind
    (is_func'_of_is_function Hf) (is_func'_of_is_function Hg)

end bSet.ErdosIndependentHomogeneous
