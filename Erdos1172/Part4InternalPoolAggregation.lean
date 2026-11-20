/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalRelationGraph
public import Erdos1172.Part4InternalSmallFamilyUnion
public import Erdos1172.Part4InternalCountableImage

@[expose] public section

/-!
# Actual coordinate projections and unions of pool states

Both projections are fixed actual functions on the full bounded state
space. Aggregation takes the actual image of an arbitrary internal family
under these projections and then its union. Support and congruence are
unconditional; smallness is derived only for a small family of small
states. Restricting the projections gives weak totality, not a false
claim that their entire graphs are supported on the smaller family.

No increasing chain, recursion, or selector-closed hierarchy is assumed
or constructed in this module.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosPoolAggregation

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosRelationGraph ErdosOmegaTwo ErdosSmallFamilyUnion ErdosCountableImage

def poolSpace (K L : bSet 𝔹) : bSet 𝔹 :=
  prod (bv_powerset K) (bv_powerset L)

def leftRel (q A : bSet 𝔹) : 𝔹 := ⨆ B, q =ᴮ pair A B

def rightRel (q B : bSet 𝔹) : 𝔹 := ⨆ A, q =ᴮ pair A B

private theorem leftRel_ext_input (A : bSet 𝔹) : B_ext (fun q => leftRel q A) :=
  B_ext_iSup (h := fun _ => B_ext_bv_eq_left)

private theorem leftRel_ext_output (q : bSet 𝔹) : B_ext (leftRel q) :=
  B_ext_iSup (h := fun _ => B_ext_pair_left B_ext_bv_eq_right)

private theorem rightRel_ext_input (B : bSet 𝔹) : B_ext (fun q => rightRel q B) :=
  B_ext_iSup (h := fun _ => B_ext_bv_eq_left)

private theorem rightRel_ext_output (q : bSet 𝔹) : B_ext (rightRel q) :=
  B_ext_iSup (h := fun _ => B_ext_pair_right B_ext_bv_eq_right)

private theorem leftRel_witness {q A : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ leftRel q A) : ∃ B : bSet 𝔹, Γ ≤ q =ᴮ pair A B :=
  exists_convert H (B_ext_pair_right B_ext_bv_eq_right)

private theorem rightRel_witness {q B : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ rightRel q B) : ∃ A : bSet 𝔹, Γ ≤ q =ᴮ pair A B :=
  exists_convert H (B_ext_pair_left B_ext_bv_eq_right)

def leftProjection (K L : bSet 𝔹) : bSet 𝔹 :=
  relationGraph (poolSpace K L) (bv_powerset K) leftRel

def rightProjection (K L : bSet 𝔹) : bSet 𝔹 :=
  relationGraph (poolSpace K L) (bv_powerset L) rightRel

theorem leftProjection_is_function {K L : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ is_function (poolSpace K L) (bv_powerset K) (leftProjection K L) := by
  apply relationGraph_is_function (P := leftRel) leftRel_ext_input leftRel_ext_output
  · apply le_iInf
    intro q
    rw [← deduction]
    obtain ⟨A, HA, B, _, Hq⟩ := mem_prod_iff₂.mp
      (show Γ ⊓ q ∈ᴮ poolSpace K L ≤ q ∈ᴮ prod (bv_powerset K) (bv_powerset L) from
        inf_le_right)
    exact le_iSup_of_le A (le_inf HA (le_iSup_of_le B Hq))
  · intro q₁ q₂ A₁ A₂ Δ _ _ _ _ _ H₁ H₂ Hq
    obtain ⟨B₁, HB₁⟩ := leftRel_witness H₁
    obtain ⟨B₂, HB₂⟩ := leftRel_witness H₂
    exact eq_of_eq_pair_left' (bv_trans (bv_symm HB₁) (bv_trans Hq HB₂))

theorem rightProjection_is_function {K L : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ is_function (poolSpace K L) (bv_powerset L) (rightProjection K L) := by
  apply relationGraph_is_function (P := rightRel) rightRel_ext_input rightRel_ext_output
  · apply le_iInf
    intro q
    rw [← deduction]
    obtain ⟨A, _, B, HB, Hq⟩ := mem_prod_iff₂.mp
      (show Γ ⊓ q ∈ᴮ poolSpace K L ≤ q ∈ᴮ prod (bv_powerset K) (bv_powerset L) from
        inf_le_right)
    exact le_iSup_of_le B (le_inf HB (le_iSup_of_le A Hq))
  · intro q₁ q₂ B₁ B₂ Δ _ _ _ _ _ H₁ H₂ Hq
    obtain ⟨A₁, HA₁⟩ := rightRel_witness H₁
    obtain ⟨A₂, HA₂⟩ := rightRel_witness H₂
    exact eq_of_eq_pair_right' (bv_trans (bv_symm HA₁) (bv_trans Hq HA₂))

theorem mem_poolSpace_iff {K L A B : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair A B ∈ᴮ poolSpace K L ↔ Γ ≤ A ⊆ᴮ K ∧ Γ ≤ B ⊆ᴮ L := by
  constructor
  · intro H
    exact ⟨mem_powerset_iff.mp (mem_prod_iff.mp H).1,
      mem_powerset_iff.mp (mem_prod_iff.mp H).2⟩
  · rintro ⟨HA, HB⟩
    exact mem_prod (mem_powerset_iff.mpr HA) (mem_powerset_iff.mpr HB)

theorem leftProjection_pair {K L A B : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ A ⊆ᴮ K) (HB : Γ ≤ B ⊆ᴮ L) :
    Γ ≤ pair (pair A B) A ∈ᴮ leftProjection K L :=
  (mem_relationGraph_iff leftRel_ext_input leftRel_ext_output).mpr
    ⟨mem_poolSpace_iff.mpr ⟨HA, HB⟩, mem_powerset_iff.mpr HA,
      le_iSup_of_le B bv_refl⟩

theorem rightProjection_pair {K L A B : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ A ⊆ᴮ K) (HB : Γ ≤ B ⊆ᴮ L) :
    Γ ≤ pair (pair A B) B ∈ᴮ rightProjection K L :=
  (mem_relationGraph_iff rightRel_ext_input rightRel_ext_output).mpr
    ⟨mem_poolSpace_iff.mpr ⟨HA, HB⟩, mem_powerset_iff.mpr HB,
      le_iSup_of_le A bv_refl⟩

theorem leftProjection_witness {K L q A : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ pair q A ∈ᴮ leftProjection K L) :
    ∃ B : bSet 𝔹, Γ ≤ q =ᴮ pair A B ∧ Γ ≤ A ⊆ᴮ K ∧ Γ ≤ B ⊆ᴮ L := by
  have Hparts := (mem_relationGraph_iff leftRel_ext_input leftRel_ext_output).mp H
  obtain ⟨B, HB⟩ := leftRel_witness Hparts.2.2
  have Hbounds := mem_poolSpace_iff.mp (mem_congr HB bv_refl Hparts.1)
  exact ⟨B, HB, Hbounds.1, Hbounds.2⟩

theorem rightProjection_witness {K L q B : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ pair q B ∈ᴮ rightProjection K L) :
    ∃ A : bSet 𝔹, Γ ≤ q =ᴮ pair A B ∧ Γ ≤ A ⊆ᴮ K ∧ Γ ≤ B ⊆ᴮ L := by
  have Hparts := (mem_relationGraph_iff rightRel_ext_input rightRel_ext_output).mp H
  obtain ⟨A, HA⟩ := rightRel_witness Hparts.2.2
  have Hbounds := mem_poolSpace_iff.mp (mem_congr HA bv_refl Hparts.1)
  exact ⟨A, HA, Hbounds.1, Hbounds.2⟩

def aggregateLeft (K L T : bSet 𝔹) : bSet 𝔹 :=
  bv_union (image T (bv_powerset K) (leftProjection K L))

def aggregateRight (K L T : bSet 𝔹) : bSet 𝔹 :=
  bv_union (image T (bv_powerset L) (rightProjection K L))

theorem aggregateLeft_subset {K L T : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ aggregateLeft K L T ⊆ᴮ K := indexed_union_subset

theorem aggregateRight_subset {K L T : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ aggregateRight K L T ⊆ᴮ L := indexed_union_subset

theorem aggregateLeft_congr (K L : bSet 𝔹) : B_congr (aggregateLeft K L) := by
  intro T U Γ H
  exact B_congr_bv_union (B_congr_image_left H)

theorem aggregateRight_congr (K L : bSet 𝔹) : B_congr (aggregateRight K L) := by
  intro T U Γ H
  exact B_congr_bv_union (B_congr_image_left H)

theorem aggregateLeft_witness {K L T x : bSet 𝔹} {Γ : 𝔹}
    (Hx : Γ ≤ x ∈ᴮ aggregateLeft K L T) :
    ∃ A B : bSet 𝔹, Γ ≤ pair A B ∈ᴮ T ∧ Γ ≤ A ⊆ᴮ K ∧
      Γ ≤ B ⊆ᴮ L ∧ Γ ≤ x ∈ᴮ A := by
  obtain ⟨q, A, Hq⟩ := exists_indexed_union_witness Hx
  obtain ⟨B, Heq, HA, HB⟩ := leftProjection_witness
    (Hq.trans (inf_le_left.trans inf_le_right))
  exact ⟨A, B, mem_congr Heq bv_refl (Hq.trans (inf_le_left.trans inf_le_left)),
    HA, HB, Hq.trans inf_le_right⟩

theorem aggregateRight_witness {K L T x : bSet 𝔹} {Γ : 𝔹}
    (Hx : Γ ≤ x ∈ᴮ aggregateRight K L T) :
    ∃ A B : bSet 𝔹, Γ ≤ pair A B ∈ᴮ T ∧ Γ ≤ A ⊆ᴮ K ∧
      Γ ≤ B ⊆ᴮ L ∧ Γ ≤ x ∈ᴮ B := by
  obtain ⟨q, B, Hq⟩ := exists_indexed_union_witness Hx
  obtain ⟨A, Heq, HA, HB⟩ := rightProjection_witness
    (Hq.trans (inf_le_left.trans inf_le_right))
  exact ⟨A, B, mem_congr Heq bv_refl (Hq.trans (inf_le_left.trans inf_le_left)),
    HA, HB, Hq.trans inf_le_right⟩

theorem mem_aggregateLeft_of_pair {K L T A B x : bSet 𝔹} {Γ : 𝔹}
    (Hpair : Γ ≤ pair A B ∈ᴮ T) (HA : Γ ≤ A ⊆ᴮ K) (HB : Γ ≤ B ⊆ᴮ L)
    (Hx : Γ ≤ x ∈ᴮ A) : Γ ≤ x ∈ᴮ aggregateLeft K L T :=
  mem_bv_union_iff.mpr (le_iSup_of_le A
    (le_inf (mem_image (leftProjection_pair HA HB) Hpair (mem_powerset_iff.mpr HA)) Hx))

theorem mem_aggregateRight_of_pair {K L T A B x : bSet 𝔹} {Γ : 𝔹}
    (Hpair : Γ ≤ pair A B ∈ᴮ T) (HA : Γ ≤ A ⊆ᴮ K) (HB : Γ ≤ B ⊆ᴮ L)
    (Hx : Γ ≤ x ∈ᴮ B) : Γ ≤ x ∈ᴮ aggregateRight K L T :=
  mem_bv_union_iff.mpr (le_iSup_of_le B
    (le_inf (mem_image (rightProjection_pair HA HB) Hpair (mem_powerset_iff.mpr HB)) Hx))

theorem left_subset_aggregate {K L T A B : bSet 𝔹} {Γ : 𝔹}
    (HT : Γ ≤ T ⊆ᴮ poolSpace K L) (Hpair : Γ ≤ pair A B ∈ᴮ T) :
    Γ ≤ A ⊆ᴮ aggregateLeft K L T := by
  have Hbounds := mem_poolSpace_iff.mp (mem_of_mem_subset HT Hpair)
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  exact mem_aggregateLeft_of_pair (inf_le_left.trans Hpair)
    (inf_le_left.trans Hbounds.1) (inf_le_left.trans Hbounds.2) inf_le_right

theorem right_subset_aggregate {K L T A B : bSet 𝔹} {Γ : 𝔹}
    (HT : Γ ≤ T ⊆ᴮ poolSpace K L) (Hpair : Γ ≤ pair A B ∈ᴮ T) :
    Γ ≤ B ⊆ᴮ aggregateRight K L T := by
  have Hbounds := mem_poolSpace_iff.mp (mem_of_mem_subset HT Hpair)
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  exact mem_aggregateRight_of_pair (inf_le_left.trans Hpair)
    (inf_le_left.trans Hbounds.1) (inf_le_left.trans Hbounds.2) inf_le_right

theorem aggregateLeft_mono {K L T U : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ T ⊆ᴮ U) : Γ ≤ aggregateLeft K L T ⊆ᴮ aggregateLeft K L U := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  obtain ⟨A, B, Hpair, HA, HB, Hx⟩ := aggregateLeft_witness
    (show Γ ⊓ x ∈ᴮ aggregateLeft K L T ≤ x ∈ᴮ aggregateLeft K L T from inf_le_right)
  exact mem_aggregateLeft_of_pair (mem_of_mem_subset (inf_le_left.trans H) Hpair) HA HB Hx

theorem aggregateRight_mono {K L T U : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ T ⊆ᴮ U) : Γ ≤ aggregateRight K L T ⊆ᴮ aggregateRight K L U := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  obtain ⟨A, B, Hpair, HA, HB, Hx⟩ := aggregateRight_witness
    (show Γ ⊓ x ∈ᴮ aggregateRight K L T ≤ x ∈ᴮ aggregateRight K L T from inf_le_right)
  exact mem_aggregateRight_of_pair (mem_of_mem_subset (inf_le_left.trans H) Hpair) HA HB Hx

theorem leftProjection_smallValues {K L T : bSet 𝔹} {Γ : 𝔹}
    (Hsmall : Γ ≤ ⨅ A, ⨅ B, _root_.imp (pair A B ∈ᴮ T) (injects_into A omegaOne)) :
    Γ ≤ smallValues T (leftProjection K L) := by
  apply le_iInf
  intro q
  apply le_iInf
  intro A
  rw [← deduction]
  obtain ⟨B, Heq, _, _⟩ := leftProjection_witness
    (show Γ ⊓ (q ∈ᴮ T ⊓ pair q A ∈ᴮ leftProjection K L) ≤
      pair q A ∈ᴮ leftProjection K L from inf_le_right.trans inf_le_right)
  exact (le_inf (inf_le_left.trans (Hsmall.trans ((iInf_le _ A).trans (iInf_le _ B))))
    (mem_congr Heq bv_refl (inf_le_right.trans inf_le_left))).trans bv_imp_elim

theorem rightProjection_smallValues {K L T : bSet 𝔹} {Γ : 𝔹}
    (Hsmall : Γ ≤ ⨅ A, ⨅ B, _root_.imp (pair A B ∈ᴮ T) (injects_into B omegaOne)) :
    Γ ≤ smallValues T (rightProjection K L) := by
  apply le_iInf
  intro q
  apply le_iInf
  intro B
  rw [← deduction]
  obtain ⟨A, Heq, _, _⟩ := rightProjection_witness
    (show Γ ⊓ (q ∈ᴮ T ⊓ pair q B ∈ᴮ rightProjection K L) ≤
      pair q B ∈ᴮ rightProjection K L from inf_le_right.trans inf_le_right)
  exact (le_inf (inf_le_left.trans (Hsmall.trans ((iInf_le _ A).trans (iInf_le _ B))))
    (mem_congr Heq bv_refl (inf_le_right.trans inf_le_left))).trans bv_imp_elim

theorem aggregateLeft_injects_omegaOne {K L T : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HT : Γ ≤ T ⊆ᴮ poolSpace K L)
    (HTsmall : Γ ≤ injects_into T omegaOne)
    (Hsmall : Γ ≤ ⨅ A, ⨅ B, _root_.imp (pair A B ∈ᴮ T) (injects_into A omegaOne)) :
    Γ ≤ injects_into (aggregateLeft K L T) omegaOne :=
  union_injects_omegaOne HCH
    (image_injects_into_ordinal
      (is_func'_subset_of_is_func' (is_func'_of_is_function leftProjection_is_function) HT)
      HTsmall omegaOne_Ord)
    (smallValues_image (leftProjection_smallValues Hsmall))

theorem aggregateRight_injects_omegaOne {K L T : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HT : Γ ≤ T ⊆ᴮ poolSpace K L)
    (HTsmall : Γ ≤ injects_into T omegaOne)
    (Hsmall : Γ ≤ ⨅ A, ⨅ B, _root_.imp (pair A B ∈ᴮ T) (injects_into B omegaOne)) :
    Γ ≤ injects_into (aggregateRight K L T) omegaOne :=
  union_injects_omegaOne HCH
    (image_injects_into_ordinal
      (is_func'_subset_of_is_func' (is_func'_of_is_function rightProjection_is_function) HT)
      HTsmall omegaOne_Ord)
    (smallValues_image (rightProjection_smallValues Hsmall))

end bSet.ErdosPoolAggregation
