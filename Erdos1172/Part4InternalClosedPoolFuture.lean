/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalClosedSelectorHull
public import Erdos1172.Part4InternalSimultaneousFuture
public import Erdos1172.Part4InternalFunctionRestriction

@[expose] public section

/-!
# A large common future for the actual closed whole-block pool

The fixed enumeration is restricted to the actual object pool, which may
be empty or mixed. The existing simultaneous-future theorem is applied
with that pool as its index domain and with the strict tail of the
original future above the point cut. No padding row or separate seed is
needed. Functionality of the same original enumeration transports every
seed law back from its restriction.

This constructs the future before any terminal is chosen. It does not
construct the subsequent ordered block-fusion run or assert its success.
Normality and selector success are not hypotheses of this preparation.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosClosedPoolFuture

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosIdeal ErdosDenseBasis ErdosCanonicalBlocks
open ErdosClosedSelectorHull ErdosSimultaneousFuture ErdosForwardSections
open ErdosColargeIntersection ErdosFunctionRestriction ErdosLargeDifference

/-- Every selected enumeration of every whole pool object has a co-large
opposite-color seed at every terminal in the retained future. -/
def poolSeedLaw (color : Bool) (R J E B Y : bSet 𝔹) : 𝔹 :=
  ⨅ A, ⨅ r, ⨅ y, _root_.imp
    ((A ∈ᴮ B ⊓ pair A r ∈ᴮ E) ⊓ y ∈ᴮ Y)
    (colarge omegaOne J (forwardSection (!color) R r y))

theorem poolSeedLaw_apply
    {color : Bool} {R J E B Y A r y : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ poolSeedLaw color R J E B Y)
    (HA : Γ ≤ A ∈ᴮ B) (HAr : Γ ≤ pair A r ∈ᴮ E) (Hy : Γ ≤ y ∈ᴮ Y) :
    Γ ≤ colarge omegaOne J (forwardSection (!color) R r y) :=
  (le_inf (H.trans ((iInf_le _ A).trans ((iInf_le _ r).trans (iInf_le _ y))))
    (le_inf (le_inf HA HAr) Hy)).trans bv_imp_elim

/-- The restriction keeps the original selected graph, not merely some
other enumeration of the same whole object. -/
private theorem restricted_enumeration_pair
    {color : Bool} {R E B Rows A r : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HRows : Γ ≤ is_function B blockEnumerationCodes Rows)
    (Hsub : Γ ≤ Rows ⊆ᴮ E)
    (HA : Γ ≤ A ∈ᴮ B) (HAr : Γ ≤ pair A r ∈ᴮ E) :
    Γ ≤ pair A r ∈ᴮ Rows := by
  have Hex : Γ ≤ ⨆ s, s ∈ᴮ blockEnumerationCodes ⊓ pair A s ∈ᴮ Rows :=
    (le_inf ((is_total_of_is_function HRows).trans (iInf_le _ A)) HA).trans bv_imp_elim
  obtain ⟨s, Hs⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hsr : Γ ≤ s =ᴮ r := eq_of_is_function_of_eq HE bv_refl
    (mem_of_mem_subset Hsub (Hs.trans inf_le_right)) HAr
  exact mem_congr (pair_congr bv_refl Hsr) bv_refl (Hs.trans inf_le_right)

/-- The preparation only needs a small pool of whole objects and a cut
below omega-two. The stronger selector-closed hull is not assumed here. -/
theorem exists_large_pool_future
    {color : Bool} {R J I D E B P S : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (HJ : Γ ≤ isIdeal omegaOne J) (Hclosure : Γ ≤ countableClosure J)
    (HD : Γ ≤ is_function I (bv_powerset omegaOne) D)
    (HDpos : Γ ≤ positiveValues omegaOne J I D)
    (Hdense : Γ ≤ denseValues omegaOne J I D) (HI : Γ ≤ injects_into I omegaOne)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HB : Γ ≤ B ⊆ᴮ blockObjects color R) (HBsmall : Γ ≤ injects_into B omegaOne)
    (HP : Γ ≤ P ∈ᴮ omegaTwo)
    (Hno : Γ ≤ (hasTwoBlock color R omegaOne bSet.omega omegaTwo)ᶜ)
    (HnoOpp : Γ ≤ (hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo)ᶜ)
    (HS : Γ ≤ S ⊆ᴮ omegaTwo) (HSlarge : Γ ≤ injects_into omegaTwo S) :
    ∃ Y : bSet 𝔹, Γ ≤ Y ⊆ᴮ S ⊓ (injects_into omegaTwo Y ⊓
      ((⨅ y, _root_.imp (y ∈ᴮ Y) (P ∈ᴮ y)) ⊓ poolSeedLaw color R J E B Y)) := by
  obtain ⟨Rows, HRowsData⟩ := exists_restricted_function HB HE
  have HRows : Γ ≤ is_function B blockEnumerationCodes Rows := HRowsData.trans inf_le_left
  have HRowsE : Γ ≤ Rows ⊆ᴮ E := HRowsData.trans inf_le_right
  have HrowInj : Γ ≤ ⨅ A, ⨅ r, _root_.imp (A ∈ᴮ B ⊓ pair A r ∈ᴮ Rows)
      (is_injective_function omegaOne omegaTwo r) := by
    apply le_iInf
    intro A
    apply le_iInf
    intro r
    rw [← deduction]
    exact (blockEnumerationFamilyLaw_apply (inf_le_left.trans HElaw)
      (mem_of_mem_subset (inf_le_left.trans HB) (inf_le_right.trans inf_le_left))
      (mem_of_mem_subset (inf_le_left.trans HRowsE) (inf_le_right.trans inf_le_right))).trans
        inf_le_left
  have HrowHom : Γ ≤ ⨅ A, ⨅ r, _root_.imp (A ∈ᴮ B ⊓ pair A r ∈ᴮ Rows)
      (homogeneousUnion color R omegaOne omegaOne r r) := by
    apply le_iInf
    intro A
    apply le_iInf
    intro r
    rw [← deduction]
    exact (blockEnumerationFamilyLaw_apply (inf_le_left.trans HElaw)
      (mem_of_mem_subset (inf_le_left.trans HB) (inf_le_right.trans inf_le_left))
      (mem_of_mem_subset (inf_le_left.trans HRowsE) (inf_le_right.trans inf_le_right))).trans
        (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have Htail : Γ ≤ difference S (succ P) ⊆ᴮ omegaTwo := subset_trans' difference_subset HS
  have HtailLarge : Γ ≤ injects_into omegaTwo (difference S (succ P)) :=
    omegaTwo_injects_difference_succ HCH HSlarge HP
  obtain ⟨a, Y, Hfuture⟩ := exists_large_simultaneous_future
    HCH Habsorb HJ Hclosure HD HDpos Hdense HI HRows HBsmall HrowInj HrowHom
      Hno HnoOpp Htail HtailLarge
  have Hremaining : Γ ≤ Y ⊆ᴮ difference S (succ P) ⊓ (injects_into omegaTwo Y ⊓
      ((⨅ y, _root_.imp (y ∈ᴮ Y) (a ∈ᴮ y)) ⊓
        oppositeSectionsColarge color R J B Rows Y)) :=
    Hfuture.trans (inf_le_right.trans inf_le_right)
  have HYtail : Γ ≤ Y ⊆ᴮ difference S (succ P) := Hremaining.trans inf_le_left
  have Hseeds : Γ ≤ oppositeSectionsColarge color R J B Rows Y :=
    Hremaining.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  refine ⟨Y, le_inf (subset_trans' HYtail difference_subset)
    (le_inf (Hremaining.trans (inf_le_right.trans inf_le_left)) (le_inf ?_ ?_))⟩
  · apply le_iInf
    intro y
    rw [← deduction]
    have HyTail : Γ ⊓ y ∈ᴮ Y ≤ y ∈ᴮ difference S (succ P) :=
      mem_of_mem_subset (inf_le_left.trans HYtail) inf_le_right
    have HyData : Γ ⊓ y ∈ᴮ Y ≤ y ∈ᴮ S ⊓ (y ∈ᴮ succ P)ᶜ := by
      simpa only [mem_difference] using HyTail
    exact ErdosOmegaReservoir.above_of_not_mem_succ (inf_le_left.trans HP)
      (mem_of_mem_subset (inf_le_left.trans HS) (HyData.trans inf_le_left))
      (HyData.trans inf_le_right)
  · apply le_iInf
    intro A
    apply le_iInf
    intro r
    apply le_iInf
    intro y
    rw [← deduction]
    let Δ := Γ ⊓ ((A ∈ᴮ B ⊓ pair A r ∈ᴮ E) ⊓ y ∈ᴮ Y)
    have HA : Δ ≤ A ∈ᴮ B := inf_le_right.trans (inf_le_left.trans inf_le_left)
    have HAr : Δ ≤ pair A r ∈ᴮ E := inf_le_right.trans (inf_le_left.trans inf_le_right)
    have Hy : Δ ≤ y ∈ᴮ Y := inf_le_right.trans inf_le_right
    have HArRows : Δ ≤ pair A r ∈ᴮ Rows :=
      restricted_enumeration_pair (inf_le_left.trans HE) (inf_le_left.trans HRows)
        (inf_le_left.trans HRowsE) HA HAr
    exact le_inf forwardSection_subset
      ((le_inf (inf_le_left.trans (Hseeds.trans
        ((iInf_le _ A).trans ((iInf_le _ r).trans (iInf_le _ y)))))
        (le_inf (le_inf HA HArRows) Hy)).trans bv_imp_elim)

/-- Apply the preparation to the constructed hull of the same fixed
selector. The selector, enumeration, ideal, and original future are not
reselected or changed by this theorem. -/
theorem exists_large_closed_pool_future
    {color : Bool} {R J I D E F B P S : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (HJ : Γ ≤ isIdeal omegaOne J) (Hclosure : Γ ≤ countableClosure J)
    (HD : Γ ≤ is_function I (bv_powerset omegaOne) D)
    (HDpos : Γ ≤ positiveValues omegaOne J I D)
    (Hdense : Γ ≤ denseValues omegaOne J I D) (HI : Γ ≤ injects_into I omegaOne)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (Hpool : Γ ≤ closedHullData color R F B P)
    (Hno : Γ ≤ (hasTwoBlock color R omegaOne bSet.omega omegaTwo)ᶜ)
    (HnoOpp : Γ ≤ (hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo)ᶜ)
    (HS : Γ ≤ S ⊆ᴮ omegaTwo) (HSlarge : Γ ≤ injects_into omegaTwo S) :
    ∃ Y : bSet 𝔹, Γ ≤ Y ⊆ᴮ S ⊓ (injects_into omegaTwo Y ⊓
      ((⨅ y, _root_.imp (y ∈ᴮ Y) (P ∈ᴮ y)) ⊓ poolSeedLaw color R J E B Y)) :=
  exists_large_pool_future HCH Habsorb HJ Hclosure HD HDpos Hdense HI HE HElaw
    (Hpool.trans inf_le_left) (Hpool.trans (inf_le_right.trans inf_le_left))
    (Hpool.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))) Hno HnoOpp HS HSlarge

end bSet.ErdosClosedPoolFuture
