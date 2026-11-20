/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalForwardSections
public import Erdos1172.Part4InternalPositiveRowImage
public import Erdos1172.Part4InternalHomogeneousAssembly
public import Erdos1172.Part4InternalIndexedIntersection
public import Erdos1172.Part4InternalCountableImage
public import Erdos1172.Part4InternalIndependentHomogeneous

@[expose] public section

/-!
Attach an actual countable clique to a positive common forward-coordinate
set. The countable set used in the intersection is the actual internal
image of the tail graph. Reenumerating the restricted row image constructs
the increasing omega-one core; no supplied compatible mask is assumed.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCenteredAttachment

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosIdeal ErdosIndexedIntersection
open ErdosForwardSections ErdosHomogeneousAssembly

/-- Every coordinate in the actual indexed intersection is forward-linked
to every tail index, and functionality identifies its actual row value. -/
theorem indexedIntersection_forward_of_row_pair
    {color : Bool} {R r S F T i x y : bSet 𝔹} {Γ : 𝔹}
    (Hr : Γ ≤ is_func r)
    (HF : Γ ≤ is_function S (bv_powerset omegaOne) F)
    (Hsections : Γ ≤ sectionFamily color R r S F)
    (HTS : Γ ≤ T ⊆ᴮ S) (Hi : Γ ≤ i ∈ᴮ indexedIntersection omegaOne F T)
    (Hix : Γ ≤ pair i x ∈ᴮ r) (Hy : Γ ≤ y ∈ᴮ T) :
    Γ ≤ x ∈ᴮ y ⊓ graphColor color R x y := by
  have HyS := mem_of_mem_subset HTS Hy
  have Hex : Γ ≤ ⨆ V, V ∈ᴮ bv_powerset omegaOne ⊓ pair y V ∈ᴮ F :=
    (le_inf ((is_total_of_is_function HF).trans (iInf_le _ y)) HyS).trans bv_imp_elim
  obtain ⟨V, HV⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have HiV : Γ ≤ i ∈ᴮ V :=
    (le_inf (((mem_indexedIntersection_iff.mp Hi).2).trans
      ((iInf_le _ y).trans (iInf_le _ V))) (le_inf Hy (HV.trans inf_le_right))).trans bv_imp_elim
  have HiSection : Γ ≤ i ∈ᴮ forwardSection color R r y :=
    mem_congr bv_refl (sectionFamily_apply Hsections HyS (HV.trans inf_le_right)) HiV
  exact forwardSection_value_of_pair Hr HiSection Hix

/-- A centered section family and an actual same-color omega clique supply
the full two-block witness. CH and normality are not needed for this assembly. -/
theorem hasTwoBlock_of_centered_sections_and_clique
    {color : Bool} {R J r S F U g : bSet 𝔹} {Γ : 𝔹}
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hr : Γ ≤ is_injective_function omegaOne omegaTwo r)
    (Hrow : Γ ≤ homogeneousUnion color R omegaOne omegaOne r r)
    (HS : Γ ≤ S ⊆ᴮ omegaTwo) (HF : Γ ≤ is_function S (bv_powerset omegaOne) F)
    (Hsections : Γ ≤ sectionFamily color R r S F)
    (HUS : Γ ≤ U ⊆ᴮ S)
    (Hcenter : Γ ≤ positiveCountableIntersections omegaOne J F U)
    (Hg : Γ ≤ is_injective_function bSet.omega U g)
    (Hginc : Γ ≤ increasingOn bSet.omega g)
    (Htail : Γ ≤ homogeneousUnion color R bSet.omega bSet.omega g g) :
    Γ ≤ hasTwoBlock color R omegaOne bSet.omega omegaTwo := by
  let T := image bSet.omega U g
  have HTU : Γ ≤ T ⊆ᴮ U := image_subset
  have HTcount : Γ ≤ injects_into T bSet.omega :=
    ErdosCountableImage.image_countable_of_function (Hg.trans inf_le_left) injects_into_refl
  let C := indexedIntersection omegaOne F T
  have HC : Γ ≤ positive omegaOne J C :=
    (le_inf (Hcenter.trans (iInf_le _ T)) (le_inf HTU HTcount)).trans bv_imp_elim
  obtain ⟨h, f, Hhf⟩ := ErdosPositiveRowImage.exists_positive_row_image Habsorb HC Hr
  have Hhr : Γ ≤ h ⊆ᴮ r := Hhf.trans (inf_le_right.trans inf_le_left)
  let B := image C omegaTwo h
  have Hf : Γ ≤ is_injective_function omegaOne B f :=
    Hhf.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have Hfinc : Γ ≤ increasingOn omegaOne f :=
    Hhf.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  have HfTwo : Γ ≤ is_function omegaOne omegaTwo f :=
    ErdosIndependentHomogeneous.is_function_codomain_mono image_subset (Hf.trans inf_le_left)
  have HgTwo : Γ ≤ is_function bSet.omega omegaTwo g :=
    ErdosIndependentHomogeneous.is_function_codomain_mono (subset_trans' HUS HS)
      (Hg.trans inf_le_left)
  have Hinclude : Γ ≤ rangeIncluded omegaOne f omegaOne r := by
    apply le_iInf
    intro x
    rw [← deduction]
    let Δ := Γ ⊓ rangeMem omegaOne f x
    have HxB : Δ ≤ x ∈ᴮ B :=
      rangeMem_le_codomain (is_func'_of_is_function (inf_le_left.trans (Hf.trans inf_le_left)))
        inf_le_right
    obtain ⟨i, Hi⟩ := exists_convert (mem_image_iff.mp HxB).2
      (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    exact le_iSup_of_le i (le_inf
      (mem_of_mem_subset (inf_le_left.trans (HC.trans inf_le_left)) (Hi.trans inf_le_left))
      (mem_of_mem_subset (inf_le_left.trans Hhr) (Hi.trans inf_le_right)))
  have Hcross : Γ ≤ forwardCross color R omegaOne bSet.omega f g := by
    apply le_iInf
    intro x
    apply le_iInf
    intro y
    rw [← deduction]
    let Δ := Γ ⊓ (rangeMem omegaOne f x ⊓ rangeMem bSet.omega g y)
    have HxB : Δ ≤ x ∈ᴮ B :=
      rangeMem_le_codomain (is_func'_of_is_function (inf_le_left.trans (Hf.trans inf_le_left)))
        (inf_le_right.trans inf_le_left)
    obtain ⟨i, Hi⟩ := exists_convert (mem_image_iff.mp HxB).2
      (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    have HyT : Δ ≤ y ∈ᴮ T :=
      mem_image_iff.mpr ⟨rangeMem_le_codomain
        (is_func'_of_is_function (inf_le_left.trans (Hg.trans inf_le_left)))
        (inf_le_right.trans inf_le_right), inf_le_right.trans inf_le_right⟩
    exact indexedIntersection_forward_of_row_pair
      (inf_le_left.trans (Hr.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))))
      (inf_le_left.trans HF) (inf_le_left.trans Hsections)
      (inf_le_left.trans (subset_trans' HTU HUS)) (Hi.trans inf_le_left)
      (mem_of_mem_subset (inf_le_left.trans Hhr) (Hi.trans inf_le_right)) HyT
  exact le_iSup_of_le f (le_iSup_of_le g
    (twoBlockWitness_of_forwardCross HfTwo HgTwo Hfinc Hginc
      (homogeneousUnion_self_mono Hrow Hinclude) Htail Hcross))

end bSet.ErdosCenteredAttachment
