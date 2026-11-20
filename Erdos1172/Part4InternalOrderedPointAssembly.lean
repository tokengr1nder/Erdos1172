/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalGraphPullback
public import Erdos1172.Part4InternalHomogeneousAssembly

@[expose] public section

/-!
# Ordered stored-pair laws assemble actual homogeneous point maps

On an ordinal source an increasing functional graph reflects strict
membership. Thus an ordered index-color law gives homogeneity of its
actual guarded range. A second stored-pair law supplies the forward
order and color between two such ranges. All indices are arbitrary
internal names, obtained from range membership at the same condition.

These are generic assembly lemmas. No coloring theorem, successful
fusion, co-large mask, or existence of an ideal is assumed or asserted.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosOrderedPointAssembly

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosPartition ErdosGraphPullback ErdosHomogeneousAssembly

/-- Only ordered pairs of domain members constrain the used graph.
Extraneous pairs outside the domain play no role. -/
def orderedPairColorLaw (color : Bool) (R K f : bSet 𝔹) : 𝔹 :=
  ⨅ i, ⨅ j, ⨅ x, ⨅ y, _root_.imp
    (((i ∈ᴮ K ⊓ j ∈ᴮ K) ⊓ i ∈ᴮ j) ⊓
      (pair i x ∈ᴮ f ⊓ pair j y ∈ᴮ f))
    (graphColor color R x y)

theorem orderedPairColorLaw_apply
    {color : Bool} {R K f i j x y : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ orderedPairColorLaw color R K f)
    (Hi : Γ ≤ i ∈ᴮ K) (Hj : Γ ≤ j ∈ᴮ K) (Hij : Γ ≤ i ∈ᴮ j)
    (Hix : Γ ≤ pair i x ∈ᴮ f) (Hjy : Γ ≤ pair j y ∈ᴮ f) :
    Γ ≤ graphColor color R x y :=
  (le_inf (H.trans ((iInf_le _ i).trans ((iInf_le _ j).trans
    ((iInf_le _ x).trans (iInf_le _ y)))))
    (le_inf (le_inf (le_inf Hi Hj) Hij) (le_inf Hix Hjy))).trans bv_imp_elim

/-- This is a law on stored graph pairs, before existentially passing
to their guarded ranges. Both domain guards are retained. -/
def storedForwardCross (color : Bool) (R A B f g : bSet 𝔹) : 𝔹 :=
  ⨅ i, ⨅ j, ⨅ x, ⨅ y, _root_.imp
    ((i ∈ᴮ A ⊓ j ∈ᴮ B) ⊓ (pair i x ∈ᴮ f ⊓ pair j y ∈ᴮ g))
    (x ∈ᴮ y ⊓ graphColor color R x y)

theorem storedForwardCross_apply
    {color : Bool} {R A B f g i j x y : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ storedForwardCross color R A B f g)
    (Hi : Γ ≤ i ∈ᴮ A) (Hj : Γ ≤ j ∈ᴮ B)
    (Hix : Γ ≤ pair i x ∈ᴮ f) (Hjy : Γ ≤ pair j y ∈ᴮ g) :
    Γ ≤ x ∈ᴮ y ⊓ graphColor color R x y :=
  (le_inf (H.trans ((iInf_le _ i).trans ((iInf_le _ j).trans
    ((iInf_le _ x).trans (iInf_le _ y)))))
    (le_inf (le_inf Hi Hj) (le_inf Hix Hjy))).trans bv_imp_elim

/-- Strict membership of used values reflects to their original ordinal
indices. Fullness extracts both arbitrary range witnesses without
strengthening the local Boolean condition. -/
theorem homogeneousUnion_of_orderedPairColorLaw
    {color : Bool} {R K κ f : bSet 𝔹} {Γ : 𝔹}
    (HK : Γ ≤ Ord K) (Hf : Γ ≤ is_function K κ f)
    (Hinc : Γ ≤ increasingOn K f)
    (Hcolors : Γ ≤ orderedPairColorLaw color R K f) :
    Γ ≤ homogeneousUnion color R K K f f := by
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ (((rangeMem K f x ⊔ rangeMem K f x) ⊓
    (rangeMem K f y ⊔ rangeMem K f y)) ⊓ x ∈ᴮ y)
  have HΔ : Δ ≤ Γ := inf_le_left
  have Hx : Δ ≤ rangeMem K f x := by
    have H : Δ ≤ rangeMem K f x ⊔ rangeMem K f x :=
      inf_le_right.trans (inf_le_left.trans inf_le_left)
    simpa only [sup_self] using H
  have Hy : Δ ≤ rangeMem K f y := by
    have H : Δ ≤ rangeMem K f y ⊔ rangeMem K f y :=
      inf_le_right.trans (inf_le_left.trans inf_le_right)
    simpa only [sup_self] using H
  have Hxy : Δ ≤ x ∈ᴮ y := inf_le_right.trans inf_le_right
  obtain ⟨i, Hi⟩ := exists_convert Hx (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  obtain ⟨j, Hj⟩ := exists_convert Hy (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  have Hij : Δ ≤ i ∈ᴮ j :=
    (increasingOn_mem_iff (HΔ.trans HK)
      (HΔ.trans (Hf.trans (inf_le_left.trans inf_le_left))) (HΔ.trans Hinc)
      (Hi.trans inf_le_left) (Hj.trans inf_le_left)
      (Hi.trans inf_le_right) (Hj.trans inf_le_right)).mpr Hxy
  exact (le_graphColor_iff_oriented color R Hxy).mp
    (orderedPairColorLaw_apply (HΔ.trans Hcolors)
      (Hi.trans inf_le_left) (Hj.trans inf_le_left) Hij
      (Hi.trans inf_le_right) (Hj.trans inf_le_right))

/-- No function or ordinal assumption is needed to pass the explicitly
guarded stored cross law to the actual used ranges. -/
theorem forwardCross_of_storedForwardCross
    {color : Bool} {R A B f g : bSet 𝔹} {Γ : 𝔹}
    (Hcross : Γ ≤ storedForwardCross color R A B f g) :
    Γ ≤ forwardCross color R A B f g := by
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ (rangeMem A f x ⊓ rangeMem B g y)
  have Hx : Δ ≤ rangeMem A f x := inf_le_right.trans inf_le_left
  have Hy : Δ ≤ rangeMem B g y := inf_le_right.trans inf_le_right
  obtain ⟨i, Hi⟩ := exists_convert Hx (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  obtain ⟨j, Hj⟩ := exists_convert Hy (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  exact storedForwardCross_apply (inf_le_left.trans Hcross)
    (Hi.trans inf_le_left) (Hj.trans inf_le_left)
    (Hi.trans inf_le_right) (Hj.trans inf_le_right)

/-- Exact two-block assembly from supported increasing maps and their
ordered stored-pair color laws. The common codomain may be omega-two or
any other name; no extra cardinal assumptions enter this bridge. -/
theorem twoBlockWitness_of_stored_laws
    {color : Bool} {R A B κ f g : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ Ord A) (HB : Γ ≤ Ord B)
    (Hf : Γ ≤ is_function A κ f) (Hg : Γ ≤ is_function B κ g)
    (Hincf : Γ ≤ increasingOn A f) (Hincg : Γ ≤ increasingOn B g)
    (Hcolorsf : Γ ≤ orderedPairColorLaw color R A f)
    (Hcolorsg : Γ ≤ orderedPairColorLaw color R B g)
    (Hcross : Γ ≤ storedForwardCross color R A B f g) :
    Γ ≤ twoBlockWitness color R A B κ f g :=
  twoBlockWitness_of_forwardCross Hf Hg Hincf Hincg
    (homogeneousUnion_of_orderedPairColorLaw HA Hf Hincf Hcolorsf)
    (homogeneousUnion_of_orderedPairColorLaw HB Hg Hincg Hcolorsg)
    (forwardCross_of_storedForwardCross Hcross)

theorem hasTwoBlock_of_stored_laws
    {color : Bool} {R A B κ f g : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ Ord A) (HB : Γ ≤ Ord B)
    (Hf : Γ ≤ is_function A κ f) (Hg : Γ ≤ is_function B κ g)
    (Hincf : Γ ≤ increasingOn A f) (Hincg : Γ ≤ increasingOn B g)
    (Hcolorsf : Γ ≤ orderedPairColorLaw color R A f)
    (Hcolorsg : Γ ≤ orderedPairColorLaw color R B g)
    (Hcross : Γ ≤ storedForwardCross color R A B f g) :
    Γ ≤ hasTwoBlock color R A B κ :=
  le_iSup_of_le f (le_iSup_of_le g
    (twoBlockWitness_of_stored_laws HA HB Hf Hg Hincf Hincg Hcolorsf Hcolorsg Hcross))

end bSet.ErdosOrderedPointAssembly
