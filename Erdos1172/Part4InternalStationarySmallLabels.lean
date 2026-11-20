/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalNonstationaryPressingDown

@[expose] public section

/-!
# Stationary thinning by internally small labels

The inverse fibers form an actual supported set-valued function on the
arbitrary label name K. Its image family is internally omega-one-small.
If every fiber were nonstationary, the proved small-union closure of the
concrete nonstationary ideal would make the entire stationary source
nonstationary. Thus an actual label has a stationary subfiber at the
original Boolean condition. No large-only pigeonhole argument is used.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosStationarySmallLabels

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosNonstationary ErdosRelationGraph ErdosCountableImage

private theorem label_fiber_congr (f : bSet 𝔹) : B_congr (fiber omegaTwo f) := by
  change B_congr (ErdosFiberInjection.fiber omegaTwo f)
  exact ErdosSmallFiberBound.fiber_congr omegaTwo f

private theorem label_fiber_positive_ext (f : bSet 𝔹) :
    B_ext (fun k => positive omegaTwo nonstationaryIdeal (fiber omegaTwo f k)) :=
  B_ext_term (ϕ := positive omegaTwo nonstationaryIdeal) (t := fiber omegaTwo f)
    (B_ext_inf B_ext_subset_left (B_ext_neg (h := B_ext_mem_left))) (label_fiber_congr f)

/-- Canonical values, not an assumed family of chosen fibers. -/
def labelFibers (K f : bSet 𝔹) : bSet 𝔹 :=
  relationGraph K (bv_powerset omegaTwo) (fun k A => A =ᴮ fiber omegaTwo f k)

private theorem labelFibers_ext_index (f A : bSet 𝔹) :
    B_ext (fun k => A =ᴮ fiber omegaTwo f k) :=
  B_ext_term (ϕ := fun B => A =ᴮ B) (t := fiber omegaTwo f)
    B_ext_bv_eq_right (label_fiber_congr f)

theorem mem_labelFibers_iff {K f k A : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair k A ∈ᴮ labelFibers K f ↔
      Γ ≤ k ∈ᴮ K ∧ Γ ≤ A ∈ᴮ bv_powerset omegaTwo ∧ Γ ≤ A =ᴮ fiber omegaTwo f k :=
  mem_relationGraph_iff (labelFibers_ext_index f) (fun _ => B_ext_bv_eq_left)

theorem labelFibers_pair {K f k : bSet 𝔹} {Γ : 𝔹}
    (Hk : Γ ≤ k ∈ᴮ K) : Γ ≤ pair k (fiber omegaTwo f k) ∈ᴮ labelFibers K f :=
  mem_labelFibers_iff.mpr ⟨Hk, mem_powerset_iff.mpr fiber_subset, bv_refl⟩

theorem labelFibers_is_function (K f : bSet 𝔹) {Γ : 𝔹} :
    Γ ≤ is_function K (bv_powerset omegaTwo) (labelFibers K f) := by
  apply relationGraph_is_function (P := fun k A => A =ᴮ fiber omegaTwo f k)
    (labelFibers_ext_index f) (fun _ => B_ext_bv_eq_left)
  · apply le_iInf
    intro k
    rw [← deduction]
    exact le_iSup_of_le (fiber omegaTwo f k)
      (le_inf (mem_powerset_iff.mpr fiber_subset) bv_refl)
  · intro k₁ k₂ A₁ A₂ Δ _ _ _ _ _ H₁ H₂ Hk
    exact bv_trans H₁ (bv_trans (label_fiber_congr f Hk) (bv_symm H₂))

def fiberSet (K f : bSet 𝔹) : bSet 𝔹 :=
  image K (bv_powerset omegaTwo) (labelFibers K f)

theorem fiberSet_injects_omegaOne {K f : bSet 𝔹} {Γ : 𝔹}
    (HK : Γ ≤ injects_into K omegaOne) : Γ ≤ injects_into (fiberSet K f) omegaOne :=
  image_injects_into_ordinal (is_func'_of_is_function (labelFibers_is_function K f))
    HK omegaOne_Ord

theorem fiberSet_subset_nonstationary {K f : bSet 𝔹} {Γ : 𝔹}
    (Hsmall : Γ ≤ ⨅ k, _root_.imp (k ∈ᴮ K)
      (fiber omegaTwo f k ∈ᴮ nonstationaryIdeal)) :
    Γ ≤ fiberSet K f ⊆ᴮ nonstationaryIdeal := by
  rw [subset_unfold']
  apply le_iInf
  intro A
  rw [← deduction]
  let Δ := Γ ⊓ A ∈ᴮ fiberSet K f
  obtain ⟨k, Hk⟩ := exists_convert
    ((mem_image_iff.mp (show Δ ≤ A ∈ᴮ fiberSet K f from inf_le_right)).2)
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  have Heq : Δ ≤ A =ᴮ fiber omegaTwo f k :=
    (mem_labelFibers_iff.mp (Hk.trans inf_le_right)).2.2
  have Hfiber : Δ ≤ fiber omegaTwo f k ∈ᴮ nonstationaryIdeal :=
    (le_inf (inf_le_left.trans (Hsmall.trans (iInf_le _ k)))
      (Hk.trans inf_le_left)).trans bv_imp_elim
  exact bv_rw' Heq (ϕ := fun B => B ∈ᴮ nonstationaryIdeal)
    (h_congr := B_ext_mem_left) (H_new := Hfiber)

/-- Totality covers the source by the actual indexed fiber union. -/
theorem source_subset_fiberSet_union {S K f : bSet 𝔹} {Γ : 𝔹}
    (HS : Γ ≤ S ⊆ᴮ omegaTwo) (Hf : Γ ≤ is_function S K f) :
    Γ ≤ S ⊆ᴮ bv_union (fiberSet K f) := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  let Δ := Γ ⊓ x ∈ᴮ S
  have Hex : Δ ≤ ⨆ k, k ∈ᴮ K ⊓ pair x k ∈ᴮ f :=
    (le_inf (inf_le_left.trans ((is_total_of_is_function Hf).trans (iInf_le _ x)))
      (show Δ ≤ x ∈ᴮ S from inf_le_right)).trans bv_imp_elim
  obtain ⟨k, Hk⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hmem : Δ ≤ fiber omegaTwo f k ∈ᴮ fiberSet K f :=
    mem_image (labelFibers_pair (Hk.trans inf_le_left)) (Hk.trans inf_le_left)
      (mem_powerset_iff.mpr fiber_subset)
  have Hx : Δ ≤ x ∈ᴮ fiber omegaTwo f k := by
    rw [mem_fiber]
    exact le_inf (mem_of_mem_subset (inf_le_left.trans HS) inf_le_right)
      (Hk.trans inf_le_right)
  exact mem_bv_union_iff.mpr (le_iSup_of_le (fiber omegaTwo f k) (le_inf Hmem Hx))

/-- The supported source function retains the fiber inside S even when
the label name K is not itself a subset of omega-two. -/
theorem label_fiber_subset_source {S K f k : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_function S K f) : Γ ≤ fiber omegaTwo f k ⊆ᴮ S := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  have Hpair : Γ ⊓ x ∈ᴮ fiber omegaTwo f k ≤ pair x k ∈ᴮ f := by
    rw [mem_fiber]
    exact inf_le_right.trans inf_le_right
  exact mem_domain_of_is_function Hpair (inf_le_left.trans Hf)

/-- Stationarity, rather than cardinal largeness, survives thinning by
an internally omega-one-small label set. -/
theorem stationary_label_value {S K f : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HS : Γ ≤ positive omegaTwo nonstationaryIdeal S)
    (Hf : Γ ≤ is_function S K f) (HK : Γ ≤ injects_into K omegaOne) :
    Γ ≤ ⨆ k, k ∈ᴮ K ⊓ positive omegaTwo nonstationaryIdeal (fiber omegaTwo f k) := by
  let E : 𝔹 := ⨆ k, k ∈ᴮ K ⊓ positive omegaTwo nonstationaryIdeal (fiber omegaTwo f k)
  change Γ ≤ E
  rw [← compl_compl E, ← imp_bot, ← deduction]
  let Δ := Γ ⊓ Eᶜ
  have Hsmall : Δ ≤ ⨅ k, _root_.imp (k ∈ᴮ K)
      (fiber omegaTwo f k ∈ᴮ nonstationaryIdeal) := by
    apply le_iInf
    intro k
    rw [← deduction, ← compl_compl (fiber omegaTwo f k ∈ᴮ nonstationaryIdeal),
      ← imp_bot, ← deduction]
    let Θ := (Δ ⊓ k ∈ᴮ K) ⊓ (fiber omegaTwo f k ∈ᴮ nonstationaryIdeal)ᶜ
    have Hfound : Θ ≤ E := le_iSup_of_le k
      (le_inf (inf_le_left.trans inf_le_right) (le_inf fiber_subset inf_le_right))
    exact bv_absurd _ Hfound (inf_le_left.trans (inf_le_left.trans inf_le_right))
  have Hunion : Δ ≤ bv_union (fiberSet K f) ∈ᴮ nonstationaryIdeal :=
    nonstationaryIdeal_small_union (inf_le_left.trans HCH)
      (fiberSet_subset_nonstationary Hsmall) (fiberSet_injects_omegaOne (inf_le_left.trans HK))
  have HSsmall : Δ ≤ S ∈ᴮ nonstationaryIdeal :=
    small_of_subset nonstationaryIdeal_downward Hunion
      (source_subset_fiberSet_union (inf_le_left.trans (HS.trans inf_le_left))
        (inf_le_left.trans Hf))
  exact bv_absurd _ HSsmall (inf_le_left.trans (HS.trans inf_le_right))

/-- Fullness provides an actual label without lowering the original
Boolean condition; the resulting stationary fiber stays inside S. -/
theorem exists_stationary_subfiber_of_small_labels {S K f : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HS : Γ ≤ positive omegaTwo nonstationaryIdeal S)
    (Hf : Γ ≤ is_function S K f) (HK : Γ ≤ injects_into K omegaOne) :
    ∃ k : bSet 𝔹, Γ ≤ k ∈ᴮ K ⊓
      (positive omegaTwo nonstationaryIdeal (fiber omegaTwo f k) ⊓ fiber omegaTwo f k ⊆ᴮ S) := by
  obtain ⟨k, Hk⟩ := exists_convert (stationary_label_value HCH HS Hf HK)
    (B_ext_inf B_ext_mem_left (label_fiber_positive_ext f))
  exact ⟨k, le_inf (Hk.trans inf_le_left)
    (le_inf (Hk.trans inf_le_right) (label_fiber_subset_source Hf))⟩

theorem exists_stationary_large_subfiber_of_small_labels {S K f : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HS : Γ ≤ positive omegaTwo nonstationaryIdeal S)
    (Hf : Γ ≤ is_function S K f) (HK : Γ ≤ injects_into K omegaOne) :
    ∃ k : bSet 𝔹, Γ ≤ k ∈ᴮ K ⊓
      (positive omegaTwo nonstationaryIdeal (fiber omegaTwo f k) ⊓
        (injects_into omegaTwo (fiber omegaTwo f k) ⊓ fiber omegaTwo f k ⊆ᴮ S)) := by
  obtain ⟨k, Hk⟩ := exists_stationary_subfiber_of_small_labels HCH HS Hf HK
  have Hpos := Hk.trans (inf_le_right.trans inf_le_left)
  exact ⟨k, le_inf (Hk.trans inf_le_left) (le_inf Hpos
    (le_inf (stationary_injects_omegaTwo HCH Hpos)
      (Hk.trans (inf_le_right.trans inf_le_right))))⟩

end bSet.ErdosStationarySmallLabels
