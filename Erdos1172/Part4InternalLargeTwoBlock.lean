/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalIncreasingEnumeration
public import Erdos1172.Part4InternalFunctionRestriction
public import Erdos1172.Part4InternalIndependentTwoRanges
public import Erdos1172.Part4InternalDushnikMiller

@[expose] public section

/-!
A full-sized independent subset of internal omega-two supplies the exact
opposite-color omega-one-plus-omega two-block witness. The first range is
initial; removing its small image leaves a large set strictly above it.
Both maps, their strict separation, and their joint homogeneity are proved.
This handles the large-clique branch, not the whole balanced partition.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosLargeTwoBlock

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosIncreasingPartial ErdosIndependentMaximal
open ErdosPartialInjection ErdosIdeal

theorem omegaOne_injects_omegaTwo {Γ : 𝔹} : Γ ≤ injects_into omegaOne omegaTwo :=
  injects_into_of_subset (subset_of_mem_Ord omegaOne_mem_omegaTwo omegaTwo_Ord)

theorem injective_image_small {K A f : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_injective_function K A f) :
    Γ ≤ injects_into (image K A f) K :=
  injects_into_of_injection_into
    (le_iSup_of_le (injective_function_inverse Hf)
      (injective_function_inverse_is_injective_function (H_inj := Hf)))

/-- The core and tail are constructed inside the same independent set;
the tail is chosen outside the actual core image, not merely outside its
displayed representatives. -/
theorem hasTwoBlock_of_large_independent
    {color : Bool} {R A S : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HAκ : Γ ≤ A ⊆ᴮ omegaTwo) (HAS : Γ ≤ A ⊆ᴮ S)
    (Hlarge : Γ ≤ injects_into omegaTwo A) (Hind : Γ ≤ independent color R A) :
    Γ ≤ hasTwoBlock (!color) R omegaOne bSet.omega S := by
  obtain ⟨f, Hf⟩ := exists_increasing_injection omegaTwo_Ord HAκ omegaOne_initial
    (injects_into_trans omegaOne_injects_omegaTwo Hlarge)
  have Hfinj : Γ ≤ is_injective_function omegaOne A f := Hf.trans inf_le_left
  have Hffunc : Γ ≤ is_function omegaOne A f := Hfinj.trans inf_le_left
  have Hfpart : Γ ≤ partialGraph omegaOne A f :=
    partialGraph_of_ordinal_function omegaOne_Ord subset_self Hfinj
  let L := difference A (image omegaOne A f)
  have HLlarge : Γ ≤ injects_into omegaTwo L :=
    ErdosLargeDifference.omegaTwo_injects_difference HCH Hlarge (injective_image_small Hfinj)
  have HLA : Γ ≤ L ⊆ᴮ A := difference_subset
  obtain ⟨k, Hk⟩ := exists_increasing_injection omegaTwo_Ord (subset_trans' HLA HAκ)
    omegaOne_initial (injects_into_trans omegaOne_injects_omegaTwo HLlarge)
  obtain ⟨g, Hg⟩ := ErdosFunctionRestriction.exists_restricted_increasing_injection
    (subset_of_mem_Ord omega_mem_omegaOne omegaOne_Ord)
    (Hk.trans inf_le_left) (Hk.trans (inf_le_right.trans inf_le_left))
  have Hgfunc : Γ ≤ is_function bSet.omega L g := Hg.trans (inf_le_left.trans inf_le_left)
  have HgA : Γ ≤ is_function bSet.omega A g :=
    ErdosIndependentHomogeneous.is_function_codomain_mono HLA Hgfunc
  have Hsep : Γ ≤ separatedRanges omegaOne bSet.omega f g := by
    apply le_iInf; intro i; apply le_iInf; intro j
    apply le_iInf; intro x; apply le_iInf; intro y
    rw [← deduction]
    let Δ := Γ ⊓ ((i ∈ᴮ omegaOne ⊓ j ∈ᴮ bSet.omega) ⊓
      (pair i x ∈ᴮ f ⊓ pair j y ∈ᴮ g))
    have Hrx : Δ ≤ rangeMem omegaOne f x :=
      rangeMem_of_pair (inf_le_right.trans (inf_le_left.trans inf_le_left))
        (inf_le_right.trans (inf_le_right.trans inf_le_left))
    have HyL : Δ ≤ y ∈ᴮ L :=
      mem_codomain_of_is_function
        (inf_le_right.trans (inf_le_right.trans inf_le_right)) (inf_le_left.trans Hgfunc)
    have HyParts : Δ ≤ y ∈ᴮ A ⊓ (y ∈ᴮ image omegaOne A f)ᶜ := by
      simpa only [L, mem_difference] using HyL
    have Hnot : Δ ≤ (rangeMem omegaOne f y)ᶜ := by
      rw [← imp_bot, ← deduction]
      have Him : Δ ⊓ rangeMem omegaOne f y ≤ y ∈ᴮ image omegaOne A f :=
        mem_image_iff.mpr ⟨inf_le_left.trans (HyParts.trans inf_le_left), inf_le_right⟩
      exact bv_absurd _ Him (inf_le_left.trans (HyParts.trans inf_le_right))
    have Habove := range_below_unused (omegaTwo_Ord (Γ := Δ)) (inf_le_left.trans HAκ)
      (inf_le_left.trans Hfpart)
      (inf_le_left.trans (Hf.trans (inf_le_right.trans inf_le_right)))
      (HyParts.trans inf_le_left) Hnot
    exact (le_inf (Habove.trans (iInf_le _ x)) Hrx).trans bv_imp_elim
  apply le_iSup_of_le f
  apply le_iSup_of_le g
  refine le_inf (le_inf ?_ ?_) (le_inf (le_inf ?_ ?_) (le_inf Hsep ?_))
  · exact is_func'_of_is_function (ErdosIndependentHomogeneous.is_function_codomain_mono HAS Hffunc)
  · exact is_func'_of_is_function (ErdosIndependentHomogeneous.is_function_codomain_mono HAS HgA)
  · exact Hf.trans (inf_le_right.trans inf_le_left)
  · exact Hg.trans (inf_le_right.trans inf_le_left)
  · exact ErdosIndependentHomogeneous.homogeneousUnion_of_independent_two_ranges Hind Hffunc HgA

theorem twoBlock_of_largeIndependent_value
    {color : Bool} {R S : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HS : Γ ≤ S ⊆ᴮ omegaTwo) :
    Γ ⊓ ErdosInternalDushnikMiller.largeIndependent color R S ≤
      hasTwoBlock (!color) R omegaOne bSet.omega S := by
  change Γ ⊓ (⨆ A, (A ⊆ᴮ S ⊓ independent color R A) ⊓ injects_into omegaTwo A) ≤ _
  rw [inf_iSup_eq]
  apply iSup_le
  intro A
  let Δ := Γ ⊓ ((A ⊆ᴮ S ⊓ independent color R A) ⊓ injects_into omegaTwo A)
  have HAS : Δ ≤ A ⊆ᴮ S := inf_le_right.trans (inf_le_left.trans inf_le_left)
  exact hasTwoBlock_of_large_independent (inf_le_left.trans HCH)
    (subset_trans' HAS (inf_le_left.trans HS)) HAS
    (inf_le_right.trans inf_le_right) (inf_le_right.trans (inf_le_left.trans inf_le_right))

/-- One exact target branch is now available: an increasing omega clique
in the chosen color, or a complete omega-one-plus-omega witness in the other.
The first branch is not a balanced target and remains to be handled. -/
theorem omega_clique_or_twoBlock {color : Bool} {R S : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HS : Γ ≤ S ⊆ᴮ omegaTwo)
    (Hlarge : Γ ≤ injects_into omegaTwo S) :
    Γ ≤ ErdosInternalDushnikMiller.omegaClique color R S ⊔
      hasTwoBlock (!color) R omegaOne bSet.omega S := by
  apply (le_inf (le_refl Γ)
    (ErdosInternalDushnikMiller.omega_clique_or_large_independent HCH HS Hlarge)).trans
  rw [inf_sup_left]
  exact sup_le (inf_le_right.trans le_sup_left)
    ((twoBlock_of_largeIndependent_value HCH HS).trans le_sup_right)

end bSet.ErdosLargeTwoBlock
