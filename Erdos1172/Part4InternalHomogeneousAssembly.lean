/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalPartitionGraph

@[expose] public section

/-!
# Guarded-range transfer and two-block homogeneous assembly

Homogeneity transfers along inclusion of the used ranges. Two individually
homogeneous ranges with strictly forward, same-color cross edges give the
joint homogeneous union and strict separation required by the exact
two-block predicate. These are Boolean-local statements about arbitrary
names, independent of ordinal, cardinal, CH, and ideal assumptions.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosHomogeneousAssembly

open ErdosPartition

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- Inclusion concerns all values used at the guarded internal domains. -/
def rangeIncluded (D h K f : bSet 𝔹) : 𝔹 :=
  ⨅ x : bSet 𝔹, _root_.imp (rangeMem D h x) (rangeMem K f x)

theorem rangeIncluded_apply {D h K f x : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ rangeIncluded D h K f) (Hx : Γ ≤ rangeMem D h x) :
    Γ ≤ rangeMem K f x :=
  (le_inf (H.trans (iInf_le _ x)) Hx).trans bv_imp_elim

/-- No graph inclusion or relation between domain names is necessary:
inclusion of the actual guarded ranges suffices. -/
theorem homogeneousUnion_self_mono
    {color : Bool} {R D h K f : bSet 𝔹} {Γ : 𝔹}
    (Hhom : Γ ≤ homogeneousUnion color R K K f f)
    (Hrange : Γ ≤ rangeIncluded D h K f) :
    Γ ≤ homogeneousUnion color R D D h h := by
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ (((rangeMem D h x ⊔ rangeMem D h x) ⊓
    (rangeMem D h y ⊔ rangeMem D h y)) ⊓ x ∈ᴮ y)
  have HΔ : Δ ≤ Γ := inf_le_left
  have Hx : Δ ≤ rangeMem D h x := by
    have H : Δ ≤ rangeMem D h x ⊔ rangeMem D h x :=
      inf_le_right.trans (inf_le_left.trans inf_le_left)
    simpa only [sup_self] using H
  have Hy : Δ ≤ rangeMem D h y := by
    have H : Δ ≤ rangeMem D h y ⊔ rangeMem D h y :=
      inf_le_right.trans (inf_le_left.trans inf_le_right)
    simpa only [sup_self] using H
  exact homogeneousUnion_apply (HΔ.trans Hhom)
    ((rangeIncluded_apply (HΔ.trans Hrange) Hx).trans le_sup_left)
    ((rangeIncluded_apply (HΔ.trans Hrange) Hy).trans le_sup_left)
    (inf_le_right.trans inf_le_right)

/-- Every first-range value strictly precedes and has the specified graph
color to every second-range value. -/
def forwardCross (color : Bool) (R A B f g : bSet 𝔹) : 𝔹 :=
  ⨅ x : bSet 𝔹, ⨅ y : bSet 𝔹,
    _root_.imp (rangeMem A f x ⊓ rangeMem B g y)
      (x ∈ᴮ y ⊓ graphColor color R x y)

theorem forwardCross_apply {color : Bool} {R A B f g x y : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ forwardCross color R A B f g)
    (Hx : Γ ≤ rangeMem A f x) (Hy : Γ ≤ rangeMem B g y) :
    Γ ≤ x ∈ᴮ y ⊓ graphColor color R x y :=
  (le_inf (H.trans ((iInf_le _ x).trans (iInf_le _ y))) (le_inf Hx Hy)).trans
    bv_imp_elim

theorem separatedRanges_of_forwardCross
    {color : Bool} {R A B f g : bSet 𝔹} {Γ : 𝔹}
    (Hcross : Γ ≤ forwardCross color R A B f g) :
    Γ ≤ separatedRanges A B f g := by
  apply le_iInf
  intro i
  apply le_iInf
  intro j
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ ((i ∈ᴮ A ⊓ j ∈ᴮ B) ⊓ (pair i x ∈ᴮ f ⊓ pair j y ∈ᴮ g))
  have Hx : Δ ≤ rangeMem A f x :=
    le_iSup_of_le i (le_inf
      (inf_le_right.trans (inf_le_left.trans inf_le_left))
      (inf_le_right.trans (inf_le_right.trans inf_le_left)))
  have Hy : Δ ≤ rangeMem B g y :=
    le_iSup_of_le j (le_inf
      (inf_le_right.trans (inf_le_left.trans inf_le_right))
      (inf_le_right.trans (inf_le_right.trans inf_le_right)))
  exact (forwardCross_apply (inf_le_left.trans Hcross) Hx Hy).trans inf_le_left

private theorem or_cases {Γ a b v : 𝔹}
    (H : Γ ≤ a ⊔ b)
    (Hleft : ∀ {Δ : 𝔹}, Δ ≤ Γ → Δ ≤ a → Δ ≤ v)
    (Hright : ∀ {Δ : 𝔹}, Δ ≤ Γ → Δ ≤ b → Δ ≤ v) : Γ ≤ v :=
  (le_inf le_rfl H).trans
    (bv_or_elim_right (Hleft inf_le_left inf_le_right) (Hright inf_le_left inf_le_right))

/-- Joint homogeneity includes both cross directions. The backwards
ordered direction is impossible by strict forward separation. -/
theorem homogeneousUnion_of_forwardCross
    {color : Bool} {R A B f g : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ homogeneousUnion color R A A f f)
    (Hg : Γ ≤ homogeneousUnion color R B B g g)
    (Hcross : Γ ≤ forwardCross color R A B f g) :
    Γ ≤ homogeneousUnion color R A B f g := by
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ (((rangeMem A f x ⊔ rangeMem B g x) ⊓
    (rangeMem A f y ⊔ rangeMem B g y)) ⊓ x ∈ᴮ y)
  have HΔ : Δ ≤ Γ := inf_le_left
  have Hrx : Δ ≤ rangeMem A f x ⊔ rangeMem B g x :=
    inf_le_right.trans (inf_le_left.trans inf_le_left)
  have Hry : Δ ≤ rangeMem A f y ⊔ rangeMem B g y :=
    inf_le_right.trans (inf_le_left.trans inf_le_right)
  have Hxy : Δ ≤ x ∈ᴮ y := inf_le_right.trans inf_le_right
  apply or_cases Hrx
  · intro Λ HΛ Hx
    apply or_cases (HΛ.trans Hry)
    · intro Θ HΘ Hy
      exact homogeneousUnion_apply (((HΘ.trans HΛ).trans HΔ).trans Hf)
        ((HΘ.trans Hx).trans le_sup_left) (Hy.trans le_sup_left)
        ((HΘ.trans HΛ).trans Hxy)
    · intro Θ HΘ Hy
      have Hforward := forwardCross_apply (((HΘ.trans HΛ).trans HΔ).trans Hcross)
        (HΘ.trans Hx) Hy
      exact (le_graphColor_iff_oriented color R (Hforward.trans inf_le_left)).mp
        (Hforward.trans inf_le_right)
  · intro Λ HΛ Hx
    apply or_cases (HΛ.trans Hry)
    · intro Θ HΘ Hy
      have Hback := forwardCross_apply (((HΘ.trans HΛ).trans HΔ).trans Hcross)
        Hy (HΘ.trans Hx)
      exact (bot_of_mem_mem' x y ((HΘ.trans HΛ).trans Hxy)
        (Hback.trans inf_le_left)).trans bot_le
    · intro Θ HΘ Hy
      exact homogeneousUnion_apply (((HΘ.trans HΛ).trans HΔ).trans Hg)
        ((HΘ.trans Hx).trans le_sup_left) (Hy.trans le_sup_left)
        ((HΘ.trans HΛ).trans Hxy)

/-- Assemble the exact two-block witness from actual function graphs,
their increasingness, their self-homogeneity, and forward cross edges. -/
theorem twoBlockWitness_of_forwardCross
    {color : Bool} {R A B κ f g : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_function A κ f) (Hg : Γ ≤ is_function B κ g)
    (Hincf : Γ ≤ increasingOn A f) (Hincg : Γ ≤ increasingOn B g)
    (Hhomf : Γ ≤ homogeneousUnion color R A A f f)
    (Hhomg : Γ ≤ homogeneousUnion color R B B g g)
    (Hcross : Γ ≤ forwardCross color R A B f g) :
    Γ ≤ twoBlockWitness color R A B κ f g :=
  le_inf (le_inf (is_func'_of_is_function Hf) (is_func'_of_is_function Hg))
    (le_inf (le_inf Hincf Hincg)
      (le_inf (separatedRanges_of_forwardCross Hcross)
        (homogeneousUnion_of_forwardCross Hhomf Hhomg Hcross)))

theorem hasTwoBlock_of_forwardCross
    {color : Bool} {R A B κ f g : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_function A κ f) (Hg : Γ ≤ is_function B κ g)
    (Hincf : Γ ≤ increasingOn A f) (Hincg : Γ ≤ increasingOn B g)
    (Hhomf : Γ ≤ homogeneousUnion color R A A f f)
    (Hhomg : Γ ≤ homogeneousUnion color R B B g g)
    (Hcross : Γ ≤ forwardCross color R A B f g) :
    Γ ≤ hasTwoBlock color R A B κ :=
  le_iSup_of_le f (le_iSup_of_le g
    (twoBlockWitness_of_forwardCross Hf Hg Hincf Hincg Hhomf Hhomg Hcross))

end bSet.ErdosHomogeneousAssembly
