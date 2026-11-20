/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalTailSurvivorSelection
public import Erdos1172.Part4InternalSelectedBlockPoints
public import Erdos1172.Part4InternalCountableTailOrder
public import Erdos1172.Part4InternalOrderedPointAssembly

@[expose] public section

/-!
# The exact omega-one plus omega witness from actual masks and tail blocks

Properness and countable closure produce coherent survivor coordinates
in the old active masks and in the later tail sections. Physical points
are then evaluated in the same fixed canonical enumeration. Whole-block
order gives increasingness and strict separation. The actual candidate
and inclusive laws give old-old edges; survivor laws give old-tail and
tail-tail edges. No final point maps or homogeneous edges are premises.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosMaskedTailWitness

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosCanonicalBlocks ErdosPartition
open ErdosFusionRowCandidates ErdosFusionMaskedTail ErdosColargeIntersection
open ErdosCountableTailRun ErdosCountableTailOrder ErdosTailSurvivorSelection
open ErdosSelectedBlockPoints ErdosOrderedPointAssembly

variable {color : Bool} {R J E S top Blocks X Tail u v : bSet 𝔹} {Γ : 𝔹}
variable (HJ : Γ ≤ properIdeal omegaOne J)
  (Hclosure : Γ ≤ countableClosure J)
  (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
  (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
  (HBlocks : Γ ≤ is_function omegaOne (bv_powerset omegaTwo) Blocks)
  (HB : Γ ≤ image omegaOne (bv_powerset omegaTwo) Blocks ⊆ᴮ blockObjects color R)
  (HX : Γ ≤ is_func' (prod omegaOne omegaOne) omegaOne X)
  (Hcandidate : Γ ≤ coordinateCandidateLaw (!color) R E top Blocks X)
  (Hactive : Γ ≤ inclusiveActiveLaw (!color) R E Blocks X)
  (Horder : Γ ≤ ⨅ i, ⨅ j, ⨅ b, ⨅ c, ⨅ x, ⨅ y, _root_.imp
    ((i ∈ᴮ j ⊓ (pair i b ∈ᴮ Blocks ⊓ pair j c ∈ᴮ Blocks)) ⊓
      (x ∈ᴮ b ⊓ y ∈ᴮ c)) (x ∈ᴮ y))
  (HTail : Γ ≤ is_function bSet.omega (bv_powerset omegaTwo) Tail)
  (Htail : Γ ≤ tailCandidatesLaw color R J E S
    (image omegaOne (bv_powerset omegaTwo) Blocks) Tail)
  (Hmasks : Γ ≤ ⨅ ν, _root_.imp (ν ∈ᴮ omegaOne)
    (colarge omegaOne J (activeMask X ν)))
  (Hu : Γ ≤ is_function omegaOne omegaOne u)
  (Hv : Γ ≤ is_function bSet.omega omegaOne v)
  (Hold : Γ ≤ oldCoordinateLaw color R E Tail Blocks X u)
  (Hnew : Γ ≤ tailCoordinateLaw color R E Tail v)

include HE HElaw HBlocks HB HX Hcandidate Hactive Horder HTail Htail Hu Hv Hold Hnew in
/-- The two actual evaluated graphs witness the full ordered target.
Their support and all three classes of edges are proved here. -/
theorem twoBlockWitness_selectedPoints :
    Γ ≤ twoBlockWitness (!color) R omegaOne bSet.omega omegaTwo
      (selectedPoints omegaOne E Blocks u) (selectedPoints bSet.omega E Tail v) := by
  have Hobjects : Γ ≤ ⨅ i, ⨅ b, _root_.imp
      (i ∈ᴮ omegaOne ⊓ pair i b ∈ᴮ Blocks) (b ∈ᴮ blockObjects color R) := by
    apply le_iInf
    intro i
    apply le_iInf
    intro b
    rw [← deduction]
    exact mem_of_mem_subset (inf_le_left.trans HB)
      (mem_image (inf_le_right.trans inf_le_right) (inf_le_right.trans inf_le_left)
        (mem_codomain_of_is_function (inf_le_right.trans inf_le_right)
          (inf_le_left.trans HBlocks)))
  have HtailObjects : Γ ≤ ⨅ i, ⨅ b, _root_.imp
      (i ∈ᴮ bSet.omega ⊓ pair i b ∈ᴮ Tail) (b ∈ᴮ blockObjects color R) := by
    apply le_iInf
    intro i
    apply le_iInf
    intro b
    rw [← deduction]
    exact tailObject_of_pair (inf_le_left.trans Htail) (inf_le_right.trans inf_le_right)
  have Hf := selectedPoints_is_function HE HElaw HBlocks Hobjects Hu
  have Hg := selectedPoints_is_function HE HElaw HTail HtailObjects Hv
  have Hincf := selectedPoints_increasingOn HE HElaw HBlocks Hobjects Hu Horder
  have HtailOrder : Γ ≤ ⨅ i, ⨅ j, ⨅ b, ⨅ c, ⨅ x, ⨅ y, _root_.imp
      ((i ∈ᴮ j ⊓ (pair i b ∈ᴮ Tail ⊓ pair j c ∈ᴮ Tail)) ⊓
        (x ∈ᴮ b ⊓ y ∈ᴮ c)) (x ∈ᴮ y) := by
    apply le_iInf
    intro i
    apply le_iInf
    intro j
    apply le_iInf
    intro b
    apply le_iInf
    intro c
    apply le_iInf
    intro x
    apply le_iInf
    intro y
    rw [← deduction]
    exact tail_tail_before (inf_le_left.trans HTail) (inf_le_left.trans Htail)
      (inf_le_right.trans (inf_le_left.trans (inf_le_right.trans inf_le_left)))
      (inf_le_right.trans (inf_le_left.trans (inf_le_right.trans inf_le_right)))
      (inf_le_right.trans (inf_le_left.trans inf_le_left))
      (inf_le_right.trans (inf_le_right.trans inf_le_left))
      (inf_le_right.trans (inf_le_right.trans inf_le_right))
  have Hincg := selectedPoints_increasingOn HE HElaw HTail HtailObjects Hv HtailOrder
  have Hcolorsf : Γ ≤ orderedPairColorLaw (!color) R omegaOne
      (selectedPoints omegaOne E Blocks u) := by
    apply le_iInf
    intro i
    apply le_iInf
    intro j
    apply le_iInf
    intro x
    apply le_iInf
    intro y
    rw [← deduction]
    let Δ := Γ ⊓ (((i ∈ᴮ omegaOne ⊓ j ∈ᴮ omegaOne) ⊓ i ∈ᴮ j) ⊓
      (pair i x ∈ᴮ selectedPoints omegaOne E Blocks u ⊓
        pair j y ∈ᴮ selectedPoints omegaOne E Blocks u))
    have HΔ : Δ ≤ Γ := inf_le_left
    have Hix : Δ ≤ pair i x ∈ᴮ selectedPoints omegaOne E Blocks u :=
      inf_le_right.trans (inf_le_right.trans inf_le_left)
    have Hjy : Δ ≤ pair j y ∈ᴮ selectedPoints omegaOne E Blocks u :=
      inf_le_right.trans (inf_le_right.trans inf_le_right)
    obtain ⟨b, k, Hib, Hik, Hkx⟩ := selectedPoints_witness
      (HΔ.trans HE) (HΔ.trans HElaw) (HΔ.trans HBlocks) (HΔ.trans Hobjects) (HΔ.trans Hu) Hix
    obtain ⟨c, _, Hjc, _, _⟩ := selectedPoints_witness
      (HΔ.trans HE) (HΔ.trans HElaw) (HΔ.trans HBlocks) (HΔ.trans Hobjects) (HΔ.trans Hu) Hjy
    have Hyc := selectedPoints_mem_block (HΔ.trans HE) (HΔ.trans HElaw)
      (HΔ.trans HBlocks) (HΔ.trans Hobjects) (HΔ.trans Hu) Hjy Hjc
    exact activeMask_cross_whole_block (HΔ.trans HX) (HΔ.trans Hcandidate) (HΔ.trans Hactive)
      (inf_le_right.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))
      (inf_le_right.trans (inf_le_left.trans inf_le_right)) Hib Hjc
      (oldCoordinateLaw_mask (HΔ.trans Hold) Hib Hik) Hkx Hyc
  have Hcolorsg : Γ ≤ orderedPairColorLaw (!color) R bSet.omega
      (selectedPoints bSet.omega E Tail v) := by
    apply le_iInf
    intro i
    apply le_iInf
    intro j
    apply le_iInf
    intro x
    apply le_iInf
    intro y
    rw [← deduction]
    let Δ := Γ ⊓ (((i ∈ᴮ bSet.omega ⊓ j ∈ᴮ bSet.omega) ⊓ i ∈ᴮ j) ⊓
      (pair i x ∈ᴮ selectedPoints bSet.omega E Tail v ⊓
        pair j y ∈ᴮ selectedPoints bSet.omega E Tail v))
    have HΔ : Δ ≤ Γ := inf_le_left
    have Hix : Δ ≤ pair i x ∈ᴮ selectedPoints bSet.omega E Tail v :=
      inf_le_right.trans (inf_le_right.trans inf_le_left)
    have Hjy : Δ ≤ pair j y ∈ᴮ selectedPoints bSet.omega E Tail v :=
      inf_le_right.trans (inf_le_right.trans inf_le_right)
    obtain ⟨b, k, Hib, Hik, Hkx⟩ := selectedPoints_witness
      (HΔ.trans HE) (HΔ.trans HElaw) (HΔ.trans HTail) (HΔ.trans HtailObjects) (HΔ.trans Hv) Hix
    obtain ⟨c, _, Hjc, _, _⟩ := selectedPoints_witness
      (HΔ.trans HE) (HΔ.trans HElaw) (HΔ.trans HTail) (HΔ.trans HtailObjects) (HΔ.trans Hv) Hjy
    have Hyc := selectedPoints_mem_block (HΔ.trans HE) (HΔ.trans HElaw)
      (HΔ.trans HTail) (HΔ.trans HtailObjects) (HΔ.trans Hv) Hjy Hjc
    exact tailCoordinateLaw_cross_tail (HΔ.trans HTail) (HΔ.trans Hnew) Hib Hik
      (inf_le_right.trans (inf_le_left.trans inf_le_right)) Hjc Hkx Hyc
  have Hcross : Γ ≤ storedForwardCross (!color) R omegaOne bSet.omega
      (selectedPoints omegaOne E Blocks u) (selectedPoints bSet.omega E Tail v) := by
    apply le_iInf
    intro i
    apply le_iInf
    intro j
    apply le_iInf
    intro x
    apply le_iInf
    intro y
    rw [← deduction]
    let Δ := Γ ⊓ ((i ∈ᴮ omegaOne ⊓ j ∈ᴮ bSet.omega) ⊓
      (pair i x ∈ᴮ selectedPoints omegaOne E Blocks u ⊓
        pair j y ∈ᴮ selectedPoints bSet.omega E Tail v))
    have HΔ : Δ ≤ Γ := inf_le_left
    have Hix : Δ ≤ pair i x ∈ᴮ selectedPoints omegaOne E Blocks u :=
      inf_le_right.trans (inf_le_right.trans inf_le_left)
    have Hjy : Δ ≤ pair j y ∈ᴮ selectedPoints bSet.omega E Tail v :=
      inf_le_right.trans (inf_le_right.trans inf_le_right)
    obtain ⟨b, k, Hib, Hik, Hkx⟩ := selectedPoints_witness
      (HΔ.trans HE) (HΔ.trans HElaw) (HΔ.trans HBlocks) (HΔ.trans Hobjects) (HΔ.trans Hu) Hix
    obtain ⟨c, _, Hjc, _, _⟩ := selectedPoints_witness
      (HΔ.trans HE) (HΔ.trans HElaw) (HΔ.trans HTail) (HΔ.trans HtailObjects) (HΔ.trans Hv) Hjy
    have Hxb := selectedPoints_mem_block (HΔ.trans HE) (HΔ.trans HElaw)
      (HΔ.trans HBlocks) (HΔ.trans Hobjects) (HΔ.trans Hu) Hix Hib
    have Hyc := selectedPoints_mem_block (HΔ.trans HE) (HΔ.trans HElaw)
      (HΔ.trans HTail) (HΔ.trans HtailObjects) (HΔ.trans Hv) Hjy Hjc
    have Hb : Δ ≤ b ∈ᴮ image omegaOne (bv_powerset omegaTwo) Blocks :=
      mem_image Hib (mem_domain_of_is_function Hib (HΔ.trans HBlocks))
        (mem_codomain_of_is_function Hib (HΔ.trans HBlocks))
    exact le_inf (tail_initial_before (HΔ.trans Htail) Hjc Hb Hxb Hyc)
      (oldCoordinateLaw_cross_tail (HΔ.trans HTail) (HΔ.trans Hold) Hib Hik Hjc Hkx Hyc)
  exact twoBlockWitness_of_stored_laws omegaOne_Ord Ord_omega Hf Hg Hincf Hincg
    Hcolorsf Hcolorsg Hcross

include HJ Hclosure HE HElaw HBlocks HB HX Hcandidate Hactive Horder HTail Htail Hmasks in
/-- Coherent survivor coordinate graphs are constructed, not assumed.
The conclusion is the full opposite-color omega-one plus omega target. -/
theorem hasTwoBlock_of_masked_tail :
    Γ ≤ hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo := by
  obtain ⟨u, v, Hselection⟩ := exists_survivor_coordinates
    HJ Hclosure HE HBlocks HB HTail Htail Hmasks
  have Hwitness := twoBlockWitness_selectedPoints HE HElaw HBlocks HB HX Hcandidate
    Hactive Horder HTail Htail (Hselection.trans inf_le_left)
    (Hselection.trans (inf_le_right.trans inf_le_left))
    (Hselection.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))
    (Hselection.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))
  exact le_iSup_of_le (selectedPoints omegaOne E Blocks u)
    (le_iSup_of_le (selectedPoints bSet.omega E Tail v) Hwitness)

end bSet.ErdosMaskedTailWitness
