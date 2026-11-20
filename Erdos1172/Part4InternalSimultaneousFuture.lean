/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalRowFamilySets
public import Erdos1172.Part4InternalForwardSectionComplement
public import Erdos1172.Part4InternalLargeFutureTrimming

@[expose] public section

/-!
A simultaneous future for an internally small family of actual rows.
One bound lies strictly above every value of every row. A single retained
large future lies beyond that bound and avoids every row's positive-section
exceptions, so the opposite-color sections are co-large in the given ideal.
The row family remains an explicit input; no canonical block family,
normal-ideal fusion, or consistency model is assumed to have been built.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousFuture

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosIdeal ErdosDenseBasis
open ErdosForwardSections ErdosPositiveSectionExceptions ErdosRowFamilySets

noncomputable def rowsBelow (Q Rows a : bSet 𝔹) : 𝔹 :=
  ⨅ q, ⨅ r, ⨅ x, _root_.imp ((q ∈ᴮ Q ⊓ pair q r ∈ᴮ Rows) ⊓ rangeMem omegaOne r x)
    (x ∈ᴮ a)

noncomputable def oppositeSectionsColarge
    (color : Bool) (R J Q Rows L : bSet 𝔹) : 𝔹 :=
  ⨅ q, ⨅ r, ⨅ y, _root_.imp ((q ∈ᴮ Q ⊓ pair q r ∈ᴮ Rows) ⊓ y ∈ᴮ L)
    (difference omegaOne (forwardSection (!color) R r y) ∈ᴮ J)

/-- Given the proved small unions, construct a common future, not just a
separate future for each externally displayed row. -/
theorem exists_large_simultaneous_future_of_small_unions
    {color : Bool} {R J Q Rows S : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HJ : Γ ≤ isIdeal omegaOne J)
    (HRows : Γ ≤ is_function Q (bv_powerset (prod omegaOne omegaTwo)) Rows)
    (HrowInj : Γ ≤ ⨅ q, ⨅ r, _root_.imp (q ∈ᴮ Q ⊓ pair q r ∈ᴮ Rows)
      (is_injective_function omegaOne omegaTwo r))
    (HAsmall : Γ ≤ injects_into (unionRowValues Q Rows) omegaOne)
    (HEsmall : Γ ≤ injects_into (unionRowExceptions color R J Q Rows) omegaOne)
    (HS : Γ ≤ S ⊆ᴮ omegaTwo) (HSlarge : Γ ≤ injects_into omegaTwo S) :
    ∃ a L : bSet 𝔹, Γ ≤ a ∈ᴮ omegaTwo ⊓ (rowsBelow Q Rows a ⊓
      (L ⊆ᴮ S ⊓ (injects_into omegaTwo L ⊓
        ((⨅ y, _root_.imp (y ∈ᴮ L) (a ∈ᴮ y)) ⊓
          oppositeSectionsColarge color R J Q Rows L)))) := by
  obtain ⟨a, L, Htrim⟩ :=
    ErdosLargeFutureTrimming.exists_large_future_avoiding_small_sets
      HCH unionRowValues_subset HAsmall HEsmall HS HSlarge
  have Ha : Γ ≤ a ∈ᴮ omegaTwo := Htrim.trans inf_le_left
  have HAa : Γ ≤ unionRowValues Q Rows ⊆ᴮ a :=
    Htrim.trans (inf_le_right.trans inf_le_left)
  have HLS : Γ ≤ L ⊆ᴮ S :=
    Htrim.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have HLlarge : Γ ≤ injects_into omegaTwo L :=
    Htrim.trans (inf_le_right.trans (inf_le_right.trans
      (inf_le_right.trans inf_le_left)))
  have Hlater : Γ ≤ ⨅ y, _root_.imp (y ∈ᴮ L)
      (a ∈ᴮ y ⊓ (y ∈ᴮ unionRowExceptions color R J Q Rows)ᶜ) :=
    Htrim.trans (inf_le_right.trans (inf_le_right.trans
      (inf_le_right.trans inf_le_right)))
  have Hbelow : Γ ≤ rowsBelow Q Rows a := by
    apply le_iInf
    intro q
    apply le_iInf
    intro r
    apply le_iInf
    intro x
    rw [← deduction]
    let Δ := Γ ⊓ ((q ∈ᴮ Q ⊓ pair q r ∈ᴮ Rows) ⊓ rangeMem omegaOne r x)
    have Hx : Δ ≤ x ∈ᴮ unionRowValues Q Rows :=
      row_value_mem_union (inf_le_left.trans HRows)
        (inf_le_right.trans (inf_le_left.trans inf_le_left))
        (inf_le_right.trans (inf_le_left.trans inf_le_right))
        (inf_le_right.trans inf_le_right)
    exact mem_of_mem_subset (inf_le_left.trans HAa) Hx
  refine ⟨a, L, le_inf Ha (le_inf Hbelow (le_inf HLS (le_inf HLlarge (le_inf ?_ ?_))))⟩
  · apply le_iInf
    intro y
    rw [← deduction]
    exact ((le_inf (inf_le_left.trans (Hlater.trans (iInf_le _ y)))
      inf_le_right).trans bv_imp_elim).trans inf_le_left
  · apply le_iInf
    intro q
    apply le_iInf
    intro r
    apply le_iInf
    intro y
    rw [← deduction]
    let Δ := Γ ⊓ ((q ∈ᴮ Q ⊓ pair q r ∈ᴮ Rows) ⊓ y ∈ᴮ L)
    have Hq : Δ ≤ q ∈ᴮ Q := inf_le_right.trans (inf_le_left.trans inf_le_left)
    have Hqr : Δ ≤ pair q r ∈ᴮ Rows :=
      inf_le_right.trans (inf_le_left.trans inf_le_right)
    have Hy : Δ ≤ y ∈ᴮ L := inf_le_right.trans inf_le_right
    have Hyω : Δ ≤ y ∈ᴮ omegaTwo :=
      mem_of_mem_subset (inf_le_left.trans (subset_trans' HLS HS)) Hy
    have Hydata : Δ ≤ a ∈ᴮ y ⊓ (y ∈ᴮ unionRowExceptions color R J Q Rows)ᶜ :=
      (le_inf (inf_le_left.trans (Hlater.trans (iInf_le _ y))) Hy).trans bv_imp_elim
    have Hr : Δ ≤ is_injective_function omegaOne omegaTwo r :=
      (le_inf (inf_le_left.trans (HrowInj.trans
        ((iInf_le _ q).trans (iInf_le _ r)))) (le_inf Hq Hqr)).trans bv_imp_elim
    have Hnot : Δ ≤ (y ∈ᴮ positiveSectionExceptions color R J r)ᶜ := by
      rw [← imp_bot, ← deduction]
      have Hmem : Δ ⊓ y ∈ᴮ positiveSectionExceptions color R J r ≤
          y ∈ᴮ unionRowExceptions color R J Q Rows :=
        mem_of_mem_subset
          (row_exception_subset_union (inf_le_left.trans (inf_le_left.trans HRows))
            (inf_le_left.trans Hq) (inf_le_left.trans Hqr)) inf_le_right
      exact bv_absurd _ Hmem (inf_le_left.trans (Hydata.trans inf_le_right))
    have Hsmall : Δ ≤ forwardSection color R r y ∈ᴮ J :=
      forwardSection_small_of_not_mem_exceptions Hyω Hnot
    have Hbefore : Δ ≤ ⨅ x, _root_.imp (rangeMem omegaOne r x) (x ∈ᴮ y) := by
      apply le_iInf
      intro x
      rw [← deduction]
      have Hxa : Δ ⊓ rangeMem omegaOne r x ≤ x ∈ᴮ a :=
        (le_inf
          (inf_le_left.trans (inf_le_left.trans (Hbelow.trans
            ((iInf_le _ q).trans ((iInf_le _ r).trans (iInf_le _ x))))))
          (le_inf (le_inf (inf_le_left.trans Hq) (inf_le_left.trans Hqr))
            inf_le_right)).trans bv_imp_elim
      exact mem_of_mem_Ord Hxa (inf_le_left.trans (Hydata.trans inf_le_left))
        (Ord_of_mem_Ord (inf_le_left.trans Hyω) omegaTwo_Ord)
    exact ErdosForwardSectionComplement.opposite_forwardSection_colarge
      (inf_le_left.trans HJ) (Hr.trans inf_le_left) Hbefore Hsmall

/-- Failure of both exact targets produces a genuine simultaneous co-large
opposite-color future for every internally small family of homogeneous
injective rows. Both small-union premises are derived, not supplied. -/
theorem exists_large_simultaneous_future
    {color : Bool} {R J I B Q Rows S : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (HJ : Γ ≤ isIdeal omegaOne J) (Hclosure : Γ ≤ countableClosure J)
    (HB : Γ ≤ is_function I (bv_powerset omegaOne) B)
    (HBpos : Γ ≤ positiveValues omegaOne J I B)
    (Hdense : Γ ≤ denseValues omegaOne J I B) (HI : Γ ≤ injects_into I omegaOne)
    (HRows : Γ ≤ is_function Q (bv_powerset (prod omegaOne omegaTwo)) Rows)
    (HQ : Γ ≤ injects_into Q omegaOne)
    (HrowInj : Γ ≤ ⨅ q, ⨅ r, _root_.imp (q ∈ᴮ Q ⊓ pair q r ∈ᴮ Rows)
      (is_injective_function omegaOne omegaTwo r))
    (HrowHom : Γ ≤ ⨅ q, ⨅ r, _root_.imp (q ∈ᴮ Q ⊓ pair q r ∈ᴮ Rows)
      (homogeneousUnion color R omegaOne omegaOne r r))
    (Hno : Γ ≤ (hasTwoBlock color R omegaOne bSet.omega omegaTwo)ᶜ)
    (HnoOpp : Γ ≤ (hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo)ᶜ)
    (HS : Γ ≤ S ⊆ᴮ omegaTwo) (HSlarge : Γ ≤ injects_into omegaTwo S) :
    ∃ a L : bSet 𝔹, Γ ≤ a ∈ᴮ omegaTwo ⊓ (rowsBelow Q Rows a ⊓
      (L ⊆ᴮ S ⊓ (injects_into omegaTwo L ⊓
        ((⨅ y, _root_.imp (y ∈ᴮ L) (a ∈ᴮ y)) ⊓
          oppositeSectionsColarge color R J Q Rows L)))) :=
  exists_large_simultaneous_future_of_small_unions HCH HJ HRows HrowInj
    (unionRowValues_injects_omegaOne HCH HRows HQ HrowInj)
    (unionRowExceptions_injects_omegaOne HCH HRows HQ Habsorb HJ Hclosure
      HB HBpos Hdense HI HrowInj HrowHom Hno HnoOpp) HS HSlarge

end bSet.ErdosSimultaneousFuture
