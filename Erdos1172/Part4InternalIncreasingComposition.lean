/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalGraphPullback

@[expose] public section

/-!
# Increasing composition and pullback homogeneity

The graph is the existing bounded internal function composition. Only its
order and color properties are added here; functionality and injectivity
remain the vendor theorems. Intermediate values are arbitrary internal
names selected at the original Boolean context. The homogeneity theorem
allows two different guarded ranges, and therefore includes a repeated
single range without any additional injectivity or nonempty premise.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosIncreasingComposition

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosPartition ErdosGraphPullback

/-- Actual intermediate values of the vendor composition, also at a
condition different from that used to construct the composition graph. -/
theorem comp_pair_witness {A κ L f e i y : bSet 𝔹} {Γ Δ : 𝔹}
    (Hf : Γ ≤ is_func' A κ f) (He : Γ ≤ is_func' κ L e)
    (Hpair : Δ ≤ pair i y ∈ᴮ is_func'_comp Hf He) :
    ∃ x : bSet 𝔹, Δ ≤ x ∈ᴮ κ ⊓ (pair i x ∈ᴮ f ⊓ pair x y ∈ᴮ e) :=
  exists_convert ((mem_is_func'_comp_iff Hf He).mp Hpair).2.2
    (B_ext_inf B_ext_mem_left (B_ext_inf B_ext_pair_mem_right B_ext_pair_mem_left))

/-- Every used value of the composition has an actual used preimage.
The statement concerns the guarded range, not an external graph range. -/
theorem rangeMem_comp_witness {A κ L f e y : bSet 𝔹} {Γ Δ : 𝔹}
    (Hf : Γ ≤ is_func' A κ f) (He : Γ ≤ is_func' κ L e)
    (Hy : Δ ≤ rangeMem A (is_func'_comp Hf He) y) :
    ∃ x : bSet 𝔹, Δ ≤ x ∈ᴮ κ ⊓ (rangeMem A f x ⊓ pair x y ∈ᴮ e) := by
  obtain ⟨i, Hi⟩ := exists_convert Hy (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  obtain ⟨x, Hx⟩ := comp_pair_witness Hf He (Hi.trans inf_le_right)
  exact ⟨x, le_inf (Hx.trans inf_le_left)
    (le_inf (le_iSup_of_le i (le_inf (Hi.trans inf_le_left)
      (Hx.trans (inf_le_right.trans inf_le_left))))
      (Hx.trans (inf_le_right.trans inf_le_right)))⟩

theorem increasingOn_comp {A κ L f e : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' A κ f) (He : Γ ≤ is_func' κ L e)
    (Hincf : Γ ≤ increasingOn A f) (Hince : Γ ≤ increasingOn κ e) :
    Γ ≤ increasingOn A (is_func'_comp Hf He) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro j
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ (((i ∈ᴮ A ⊓ j ∈ᴮ A) ⊓ i ∈ᴮ j) ⊓
    (pair i x ∈ᴮ is_func'_comp Hf He ⊓ pair j y ∈ᴮ is_func'_comp Hf He))
  have Hi : Δ ≤ i ∈ᴮ A := inf_le_right.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
  have Hj : Δ ≤ j ∈ᴮ A := inf_le_right.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
  have Hij : Δ ≤ i ∈ᴮ j := inf_le_right.trans (inf_le_left.trans inf_le_right)
  obtain ⟨u, Hu⟩ := comp_pair_witness Hf He (show Δ ≤ pair i x ∈ᴮ is_func'_comp Hf He from
      inf_le_right.trans (inf_le_right.trans inf_le_left))
  obtain ⟨v, Hv⟩ := comp_pair_witness Hf He (show Δ ≤ pair j y ∈ᴮ is_func'_comp Hf He from
      inf_le_right.trans (inf_le_right.trans inf_le_right))
  have Huv : Δ ≤ u ∈ᴮ v := increasingOn_apply (inf_le_left.trans Hincf) Hi Hj Hij
    (Hu.trans (inf_le_right.trans inf_le_left))
    (Hv.trans (inf_le_right.trans inf_le_left))
  exact increasingOn_apply (inf_le_left.trans Hince)
    (Hu.trans inf_le_left) (Hv.trans inf_le_left) Huv
    (Hu.trans (inf_le_right.trans inf_le_right))
    (Hv.trans (inf_le_right.trans inf_le_right))

theorem increasingOn_injective_function_comp {A κ L f e : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_injective_function A κ f) (He : Γ ≤ is_injective_function κ L e)
    (Hincf : Γ ≤ increasingOn A f) (Hince : Γ ≤ increasingOn κ e) :
    Γ ≤ increasingOn A (injective_function_comp Hf He) :=
  increasingOn_comp (is_func'_of_is_injective_function Hf)
    (is_func'_of_is_injective_function He) Hincf Hince

private theorem rangeMem_ext (A f : bSet 𝔹) : B_ext (rangeMem A f) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_pair_mem_right)

/-- A union of two composed ranges has a preimage in the corresponding
union. The disjunction stays inside the Boolean algebra. -/
theorem unionRange_comp_witness {A B κ L f g e y : bSet 𝔹} {Γ Δ : 𝔹}
    (Hf : Γ ≤ is_func' A κ f) (Hg : Γ ≤ is_func' B κ g)
    (He : Γ ≤ is_func' κ L e)
    (Hy : Δ ≤ rangeMem A (is_func'_comp Hf He) y ⊔ rangeMem B (is_func'_comp Hg He) y) :
    ∃ x : bSet 𝔹, Δ ≤ x ∈ᴮ κ ⊓ ((rangeMem A f x ⊔ rangeMem B g x) ⊓ pair x y ∈ᴮ e) := by
  have Hex : Δ ≤ ⨆ x, x ∈ᴮ κ ⊓ ((rangeMem A f x ⊔ rangeMem B g x) ⊓ pair x y ∈ᴮ e) := by
    apply (le_inf le_rfl Hy).trans
    rw [inf_sup_left]
    apply sup_le
    · obtain ⟨x, Hx⟩ := rangeMem_comp_witness Hf He
        (show Δ ⊓ rangeMem A (is_func'_comp Hf He) y ≤
          rangeMem A (is_func'_comp Hf He) y from inf_le_right)
      exact le_iSup_of_le x (le_inf (Hx.trans inf_le_left)
        (le_inf ((Hx.trans (inf_le_right.trans inf_le_left)).trans le_sup_left)
          (Hx.trans (inf_le_right.trans inf_le_right))))
    · obtain ⟨x, Hx⟩ := rangeMem_comp_witness Hg He
        (show Δ ⊓ rangeMem B (is_func'_comp Hg He) y ≤
          rangeMem B (is_func'_comp Hg He) y from inf_le_right)
      exact le_iSup_of_le x (le_inf (Hx.trans inf_le_left)
        (le_inf ((Hx.trans (inf_le_right.trans inf_le_left)).trans le_sup_right)
          (Hx.trans (inf_le_right.trans inf_le_right))))
  exact exists_convert Hex (B_ext_inf B_ext_mem_left
    (B_ext_inf (B_ext_sup (h₁ := rangeMem_ext A f) (h₂ := rangeMem_ext B g)) B_ext_pair_mem_left))

/-- Two homogeneous source ranges remain jointly homogeneous after
composition. Only the outer graph needs to preserve order. -/
theorem homogeneousUnion_comp_pullback {color : Bool}
    {A B κ L R f g e : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ)
    (Hf : Γ ≤ is_func' A κ f) (Hg : Γ ≤ is_func' B κ g)
    (He : Γ ≤ is_func' κ L e) (Hince : Γ ≤ increasingOn κ e)
    (Hhom : Γ ≤ homogeneousUnion color (pullbackRelation κ R e) A B f g) :
    Γ ≤ homogeneousUnion color R A B (is_func'_comp Hf He) (is_func'_comp Hg He) := by
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ (((rangeMem A (is_func'_comp Hf He) x ⊔
    rangeMem B (is_func'_comp Hg He) x) ⊓
    (rangeMem A (is_func'_comp Hf He) y ⊔ rangeMem B (is_func'_comp Hg He) y)) ⊓ x ∈ᴮ y)
  obtain ⟨u, Hu⟩ := unionRange_comp_witness Hf Hg He
    (show Δ ≤ rangeMem A (is_func'_comp Hf He) x ⊔ rangeMem B (is_func'_comp Hg He) x from
      inf_le_right.trans (inf_le_left.trans inf_le_left))
  obtain ⟨v, Hv⟩ := unionRange_comp_witness Hf Hg He
    (show Δ ≤ rangeMem A (is_func'_comp Hf He) y ⊔ rangeMem B (is_func'_comp Hg He) y from
      inf_le_right.trans (inf_le_left.trans inf_le_right))
  have Huv : Δ ≤ u ∈ᴮ v := (increasingOn_mem_iff
    (inf_le_left.trans Hκ) (inf_le_left.trans (He.trans inf_le_left))
    (inf_le_left.trans Hince) (Hu.trans inf_le_left) (Hv.trans inf_le_left)
    (Hu.trans (inf_le_right.trans inf_le_right))
    (Hv.trans (inf_le_right.trans inf_le_right))).mpr (inf_le_right.trans inf_le_right)
  have Hedge := homogeneousUnion_apply (inf_le_left.trans Hhom)
    (Hu.trans (inf_le_right.trans inf_le_left))
    (Hv.trans (inf_le_right.trans inf_le_left)) Huv
  exact (orientedColor_pullback_iff color (inf_le_left.trans (He.trans inf_le_left))
    (Hu.trans inf_le_left) (Hv.trans inf_le_left)
    (Hu.trans (inf_le_right.trans inf_le_right))
    (Hv.trans (inf_le_right.trans inf_le_right))).mp Hedge

theorem homogeneousUnion_injective_function_comp_pullback {color : Bool}
    {A B κ L R f g e : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ)
    (Hf : Γ ≤ is_injective_function A κ f) (Hg : Γ ≤ is_injective_function B κ g)
    (He : Γ ≤ is_injective_function κ L e) (Hince : Γ ≤ increasingOn κ e)
    (Hhom : Γ ≤ homogeneousUnion color (pullbackRelation κ R e) A B f g) :
    Γ ≤ homogeneousUnion color R A B
      (injective_function_comp Hf He) (injective_function_comp Hg He) :=
  homogeneousUnion_comp_pullback Hκ (is_func'_of_is_injective_function Hf)
    (is_func'_of_is_injective_function Hg) (is_func'_of_is_injective_function He) Hince Hhom

end bSet.ErdosIncreasingComposition
