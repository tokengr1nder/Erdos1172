/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalIndependentMaximal
public import Erdos1172.Part4InternalSmallFiberBound

@[expose] public section

/-!
An independent internal set has the opposite oriented color on every used
ordered pair. An arbitrary internal injection into it therefore has a
homogeneous range. This is a cardinal-sized homogeneous-range result; no
increasing enumeration or order-type transfer is asserted.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosIndependentHomogeneous

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosPartition ErdosIndependentMaximal

theorem opposite_oriented_of_not_graphColor {color : Bool} {R x y : bSet 𝔹} {Γ : 𝔹}
    (Hxy : Γ ≤ x ∈ᴮ y) (Hnot : Γ ≤ (graphColor color R x y)ᶜ) :
    Γ ≤ (if !color then pair x y ∈ᴮ R else (pair x y ∈ᴮ R)ᶜ) := by
  cases color with
  | false =>
      change Γ ≤ pair x y ∈ᴮ R
      rw [← compl_compl (pair x y ∈ᴮ R), ← imp_bot, ← deduction]
      have Hbad : Γ ⊓ (pair x y ∈ᴮ R)ᶜ ≤ graphColor false R x y :=
        (le_graphColor_iff_oriented false R (inf_le_left.trans Hxy)).mpr inf_le_right
      exact bv_absurd _ Hbad (inf_le_left.trans Hnot)
  | true =>
      change Γ ≤ (pair x y ∈ᴮ R)ᶜ
      rw [← imp_bot, ← deduction]
      have Hbad : Γ ⊓ (pair x y ∈ᴮ R) ≤ graphColor true R x y :=
        (le_graphColor_iff_oriented true R (inf_le_left.trans Hxy)).mpr inf_le_right
      exact bv_absurd _ Hbad (inf_le_left.trans Hnot)

/-- Every actual function into an independent set has opposite homogeneous
range on the ordered pairs used by the partition semantics. -/
theorem homogeneousUnion_of_independent {color : Bool} {R A K f : bSet 𝔹} {Γ : 𝔹}
    (Hind : Γ ≤ independent color R A) (Hf : Γ ≤ is_function K A f) :
    Γ ≤ homogeneousUnion (!color) R K K f f := by
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ (((rangeMem K f x ⊔ rangeMem K f x) ⊓
    (rangeMem K f y ⊔ rangeMem K f y)) ⊓ x ∈ᴮ y)
  have HΔ : Δ ≤ Γ := inf_le_left
  have Hrx : Δ ≤ rangeMem K f x ⊔ rangeMem K f x :=
    inf_le_right.trans (inf_le_left.trans inf_le_left)
  have Hry : Δ ≤ rangeMem K f y ⊔ rangeMem K f y :=
    inf_le_right.trans (inf_le_left.trans inf_le_right)
  have HxA : Δ ≤ x ∈ᴮ A :=
    (le_inf HΔ Hrx).trans
      (unionRange_le_codomain (is_func'_of_is_function Hf) (is_func'_of_is_function Hf))
  have HyA : Δ ≤ y ∈ᴮ A :=
    (le_inf HΔ Hry).trans
      (unionRange_le_codomain (is_func'_of_is_function Hf) (is_func'_of_is_function Hf))
  exact opposite_oriented_of_not_graphColor (inf_le_right.trans inf_le_right)
    (independent_apply (HΔ.trans Hind) HxA HyA)

theorem prod_codomain_mono {K A S : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ A ⊆ᴮ S) : Γ ≤ prod K A ⊆ᴮ prod K S := by
  rw [subset_unfold']
  apply le_iInf
  intro p
  rw [← deduction]
  obtain ⟨x, Hx, y, Hy, Hp⟩ := mem_prod_iff₂.mp
    (show Γ ⊓ p ∈ᴮ prod K A ≤ p ∈ᴮ prod K A from inf_le_right)
  exact mem_prod_iff₂.mpr
    ⟨x, Hx, y, mem_of_mem_subset (inf_le_left.trans Hsub) Hy, Hp⟩

/-- Codomain enlargement preserves the same actual supported function graph. -/
theorem is_function_codomain_mono {K A S f : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ A ⊆ᴮ S) (Hf : Γ ≤ is_function K A f) :
    Γ ≤ is_function K S f := by
  refine le_inf (le_inf (Hf.trans (inf_le_left.trans inf_le_left)) ?_)
    (subset_trans' (subset_prod_of_is_function Hf) (prod_codomain_mono Hsub))
  apply le_iInf
  intro x
  rw [← deduction]
  have Htotal : Γ ⊓ x ∈ᴮ K ≤ ⨆ y, y ∈ᴮ A ⊓ pair x y ∈ᴮ f :=
    (le_inf (inf_le_left.trans ((is_total_of_is_function Hf).trans (iInf_le _ x)))
      inf_le_right).trans bv_imp_elim
  obtain ⟨y, Hy⟩ := exists_convert Htotal
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  exact le_iSup_of_le y
    (le_inf (mem_of_mem_subset (inf_le_left.trans Hsub) (Hy.trans inf_le_left))
      (Hy.trans inf_le_right))

theorem is_injective_function_codomain_mono {K A S f : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ A ⊆ᴮ S) (Hf : Γ ≤ is_injective_function K A f) :
    Γ ≤ is_injective_function K S f :=
  le_inf (is_function_codomain_mono Hsub (Hf.trans inf_le_left))
    (Hf.trans inf_le_right)

end bSet.ErdosIndependentHomogeneous
