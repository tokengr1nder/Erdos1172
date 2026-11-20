/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalPositiveSectionExceptions
public import Erdos1172.Part4InternalSmallFamilyUnion

@[expose] public section

/-!
# Actual image and exception families of internally indexed rows

A bounded relational transformation constructs a coherent powerset-valued
family from the given row graph. The actual indexed unions contain every
row value and every positive-section exception. Internal smallness of the
index set and the values bounds those unions under CH; no external family
enumeration, supplied exception bound, or nonempty index is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosRowFamilySets

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosIdeal ErdosDenseBasis ErdosRelationGraph
open ErdosForwardSections ErdosPositiveSectionExceptions ErdosSmallFamilyUnion

theorem forwardSection_row_congr (color : Bool) (R y : bSet 𝔹) :
    B_congr (fun r => forwardSection color R r y) := by
  intro r₁ r₂ Γ H
  have Hext (i : bSet 𝔹) : B_ext (fun r => ⨆ x : bSet 𝔹,
      pair i x ∈ᴮ r ⊓ (x ∈ᴮ y ⊓ graphColor color R x y)) :=
    B_ext_iSup (h := fun _ => B_ext_inf B_ext_mem_right B_ext_const)
  apply mem_ext
  · apply le_iInf
    intro i
    rw [← deduction]
    have Hi := mem_forwardSection_iff.mp
      (show Γ ⊓ i ∈ᴮ forwardSection color R r₁ y ≤
        i ∈ᴮ forwardSection color R r₁ y from inf_le_right)
    exact mem_forwardSection_iff.mpr ⟨Hi.1,
      bv_rw'' (ϕ := fun r => ⨆ x : bSet 𝔹,
        pair i x ∈ᴮ r ⊓ (x ∈ᴮ y ⊓ graphColor color R x y))
        (inf_le_left.trans H) Hi.2 (Hext i)⟩
  · apply le_iInf
    intro i
    rw [← deduction]
    have Hi := mem_forwardSection_iff.mp
      (show Γ ⊓ i ∈ᴮ forwardSection color R r₂ y ≤
        i ∈ᴮ forwardSection color R r₂ y from inf_le_right)
    exact mem_forwardSection_iff.mpr ⟨Hi.1,
      bv_rw' (ϕ := fun r => ⨆ x : bSet 𝔹,
        pair i x ∈ᴮ r ⊓ (x ∈ᴮ y ⊓ graphColor color R x y))
        (inf_le_left.trans H) (h_congr := Hext i) (H_new := Hi.2)⟩

theorem positiveSectionExceptions_row_congr (color : Bool) (R J : bSet 𝔹) :
    B_congr (positiveSectionExceptions color R J) := by
  intro r₁ r₂ Γ H
  have Hext (y : bSet 𝔹) :
      B_ext (fun r => positive omegaOne J (forwardSection color R r y)) :=
    B_ext_term (ϕ := positive omegaOne J) (t := fun r => forwardSection color R r y)
      (B_ext_inf B_ext_subset_left (B_ext_neg (h := B_ext_mem_left)))
      (forwardSection_row_congr color R y)
  apply mem_ext
  · apply le_iInf
    intro y
    rw [← deduction]
    have Hy := mem_positiveSectionExceptions_iff.mp
      (show Γ ⊓ y ∈ᴮ positiveSectionExceptions color R J r₁ ≤
        y ∈ᴮ positiveSectionExceptions color R J r₁ from inf_le_right)
    exact mem_positiveSectionExceptions_iff.mpr ⟨Hy.1,
      bv_rw'' (ϕ := fun r => positive omegaOne J (forwardSection color R r y))
        (inf_le_left.trans H) Hy.2 (Hext y)⟩
  · apply le_iInf
    intro y
    rw [← deduction]
    have Hy := mem_positiveSectionExceptions_iff.mp
      (show Γ ⊓ y ∈ᴮ positiveSectionExceptions color R J r₂ ≤
        y ∈ᴮ positiveSectionExceptions color R J r₂ from inf_le_right)
    exact mem_positiveSectionExceptions_iff.mpr ⟨Hy.1,
      bv_rw' (ϕ := fun r => positive omegaOne J (forwardSection color R r y))
        (inf_le_left.trans H) (h_congr := Hext y) (H_new := Hy.2)⟩

def transformedValue (Rows : bSet 𝔹) (φ : bSet 𝔹 → bSet 𝔹)
    (q X : bSet 𝔹) : 𝔹 :=
  ⨆ r : bSet 𝔹, pair q r ∈ᴮ Rows ⊓ X =ᴮ φ r

private theorem transformedValue_ext_left (Rows : bSet 𝔹)
    (φ : bSet 𝔹 → bSet 𝔹) (X : bSet 𝔹) :
    B_ext (fun q => transformedValue Rows φ q X) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_pair_mem_left B_ext_const)

private theorem transformedValue_ext_right (Rows : bSet 𝔹)
    (φ : bSet 𝔹 → bSet 𝔹) (q : bSet 𝔹) :
    B_ext (transformedValue Rows φ q) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_bv_eq_left)

private theorem transformedValue_exists {Rows q X : bSet 𝔹}
    {φ : bSet 𝔹 → bSet 𝔹} {Γ : 𝔹} (Hφ : B_congr φ)
    (H : Γ ≤ transformedValue Rows φ q X) :
    ∃ r : bSet 𝔹, Γ ≤ pair q r ∈ᴮ Rows ⊓ X =ᴮ φ r :=
  exists_convert H (B_ext_inf B_ext_pair_mem_right
    (B_ext_term (ϕ := fun Z => X =ᴮ Z) (t := φ) B_ext_bv_eq_right Hφ))

def transformedFamily (Q Rows : bSet 𝔹) (φ : bSet 𝔹 → bSet 𝔹) : bSet 𝔹 :=
  relationGraph Q (bv_powerset omegaTwo) (transformedValue Rows φ)

private theorem transformedFamily_pair {Q Rows q r : bSet 𝔹}
    {φ : bSet 𝔹 → bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ φ r ⊆ᴮ omegaTwo) (Hq : Γ ≤ q ∈ᴮ Q)
    (Hqr : Γ ≤ pair q r ∈ᴮ Rows) :
    Γ ≤ pair q (φ r) ∈ᴮ transformedFamily Q Rows φ :=
  (mem_relationGraph_iff (transformedValue_ext_left Rows φ)
    (transformedValue_ext_right Rows φ)).mpr
    ⟨Hq, mem_powerset_iff.mpr Hsub, le_iSup_of_le r (le_inf Hqr bv_refl)⟩

private theorem transformedFamily_function {Q V Rows : bSet 𝔹}
    {φ : bSet 𝔹 → bSet 𝔹} {Γ : 𝔹}
    (HRows : Γ ≤ is_function Q V Rows) (Hφ : B_congr φ)
    (Hsub : ∀ r, (⊤ : 𝔹) ≤ φ r ⊆ᴮ omegaTwo) :
    Γ ≤ is_function Q (bv_powerset omegaTwo) (transformedFamily Q Rows φ) := by
  apply relationGraph_is_function (transformedValue_ext_left Rows φ)
    (transformedValue_ext_right Rows φ)
  · apply le_iInf
    intro q
    rw [← deduction]
    have Hex : Γ ⊓ q ∈ᴮ Q ≤ ⨆ r, r ∈ᴮ V ⊓ pair q r ∈ᴮ Rows :=
      (le_inf (inf_le_left.trans ((is_total_of_is_function HRows).trans (iInf_le _ q)))
        inf_le_right).trans bv_imp_elim
    obtain ⟨r, Hr⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
    exact le_iSup_of_le (φ r) (le_inf (mem_powerset_iff.mpr (le_top.trans (Hsub r)))
      (le_iSup_of_le r (le_inf (Hr.trans inf_le_right) bv_refl)))
  · intro q₁ q₂ X₁ X₂ Δ HΔ _ _ _ _ H₁ H₂ Hq
    obtain ⟨r₁, Hr₁⟩ := transformedValue_exists Hφ H₁
    obtain ⟨r₂, Hr₂⟩ := transformedValue_exists Hφ H₂
    have Hr : Δ ≤ r₁ =ᴮ r₂ :=
      eq_of_is_function_of_eq (HΔ.trans HRows) Hq
        (Hr₁.trans inf_le_left) (Hr₂.trans inf_le_left)
    exact bv_trans (Hr₁.trans inf_le_right)
      (bv_trans (Hφ Hr) (bv_symm (Hr₂.trans inf_le_right)))

private theorem transformedFamily_small {Q V Rows : bSet 𝔹}
    {φ : bSet 𝔹 → bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HRows : Γ ≤ is_function Q V Rows)
    (HQ : Γ ≤ injects_into Q omegaOne) (Hφ : B_congr φ)
    (Hsub : ∀ r, (⊤ : 𝔹) ≤ φ r ⊆ᴮ omegaTwo)
    (Hsmall : Γ ≤ ⨅ q, ⨅ r,
      _root_.imp (q ∈ᴮ Q ⊓ pair q r ∈ᴮ Rows) (injects_into (φ r) omegaOne)) :
    Γ ≤ injects_into
      (bv_union (image Q (bv_powerset omegaTwo) (transformedFamily Q Rows φ))) omegaOne := by
  apply indexed_union_injects_omegaOne HCH
    (transformedFamily_function HRows Hφ Hsub) HQ
  apply le_iInf
  intro q
  apply le_iInf
  intro X
  rw [← deduction]
  let Δ := Γ ⊓ (q ∈ᴮ Q ⊓ pair q X ∈ᴮ transformedFamily Q Rows φ)
  have HX := (mem_relationGraph_iff (transformedValue_ext_left Rows φ)
    (transformedValue_ext_right Rows φ)).mp
    (show Δ ≤ pair q X ∈ᴮ transformedFamily Q Rows φ from inf_le_right.trans inf_le_right)
  obtain ⟨r, Hr⟩ := transformedValue_exists Hφ HX.2.2
  have Hsmallr : Δ ≤ injects_into (φ r) omegaOne :=
    (le_inf (inf_le_left.trans (Hsmall.trans ((iInf_le _ q).trans (iInf_le _ r))))
      (le_inf HX.1 (Hr.trans inf_le_left))).trans bv_imp_elim
  exact bv_rw' (ϕ := fun A => injects_into A omegaOne) (Hr.trans inf_le_right)
    (h_congr := B_ext_injects_into_left) (H_new := Hsmallr)

def rowValueFamily (Q Rows : bSet 𝔹) : bSet 𝔹 :=
  transformedFamily Q Rows (fun r => image omegaOne omegaTwo r)

def rowExceptionFamily (color : Bool) (R J Q Rows : bSet 𝔹) : bSet 𝔹 :=
  transformedFamily Q Rows (positiveSectionExceptions color R J)

def unionRowValues (Q Rows : bSet 𝔹) : bSet 𝔹 :=
  bv_union (image Q (bv_powerset omegaTwo) (rowValueFamily Q Rows))

def unionRowExceptions (color : Bool) (R J Q Rows : bSet 𝔹) : bSet 𝔹 :=
  bv_union (image Q (bv_powerset omegaTwo) (rowExceptionFamily color R J Q Rows))

theorem rowValueFamily_is_function {Q V Rows : bSet 𝔹} {Γ : 𝔹}
    (HRows : Γ ≤ is_function Q V Rows) :
    Γ ≤ is_function Q (bv_powerset omegaTwo) (rowValueFamily Q Rows) :=
  transformedFamily_function HRows B_congr_image_right (fun _ => image_subset)

theorem rowExceptionFamily_is_function {color : Bool} {R J Q V Rows : bSet 𝔹} {Γ : 𝔹}
    (HRows : Γ ≤ is_function Q V Rows) :
    Γ ≤ is_function Q (bv_powerset omegaTwo) (rowExceptionFamily color R J Q Rows) :=
  transformedFamily_function HRows (positiveSectionExceptions_row_congr color R J)
    (fun _ => positiveSectionExceptions_subset)

theorem unionRowValues_subset {Q Rows : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ unionRowValues Q Rows ⊆ᴮ omegaTwo := indexed_union_subset

theorem unionRowExceptions_subset {color : Bool} {R J Q Rows : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ unionRowExceptions color R J Q Rows ⊆ᴮ omegaTwo := indexed_union_subset

theorem row_image_subset_union {Q V Rows q r : bSet 𝔹} {Γ : 𝔹}
    (HRows : Γ ≤ is_function Q V Rows) (Hq : Γ ≤ q ∈ᴮ Q)
    (Hqr : Γ ≤ pair q r ∈ᴮ Rows) :
    Γ ≤ image omegaOne omegaTwo r ⊆ᴮ unionRowValues Q Rows := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  exact mem_indexed_union_of_value (rowValueFamily_is_function (inf_le_left.trans HRows))
    (inf_le_left.trans Hq)
    (transformedFamily_pair (φ := fun r => image omegaOne omegaTwo r)
      image_subset (inf_le_left.trans Hq) (inf_le_left.trans Hqr))
    inf_le_right

theorem row_value_mem_union {Q Rows q r x : bSet 𝔹} {Γ : 𝔹}
    (HRows : Γ ≤ is_function Q (bv_powerset (prod omegaOne omegaTwo)) Rows)
    (Hq : Γ ≤ q ∈ᴮ Q) (Hqr : Γ ≤ pair q r ∈ᴮ Rows)
    (Hx : Γ ≤ rangeMem omegaOne r x) : Γ ≤ x ∈ᴮ unionRowValues Q Rows := by
  have Hrsub : Γ ≤ r ⊆ᴮ prod omegaOne omegaTwo :=
    mem_powerset_iff.mp (mem_codomain_of_is_function Hqr HRows)
  obtain ⟨i, Hi⟩ := exists_convert Hx (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  have HxTwo : Γ ≤ x ∈ᴮ omegaTwo :=
    (mem_prod_iff.mp (mem_of_mem_subset Hrsub (Hi.trans inf_le_right))).2
  exact mem_of_mem_subset (row_image_subset_union HRows Hq Hqr)
    (mem_image_iff.mpr ⟨HxTwo, Hx⟩)

theorem row_exception_subset_union {color : Bool} {R J Q V Rows q r : bSet 𝔹} {Γ : 𝔹}
    (HRows : Γ ≤ is_function Q V Rows) (Hq : Γ ≤ q ∈ᴮ Q)
    (Hqr : Γ ≤ pair q r ∈ᴮ Rows) :
    Γ ≤ positiveSectionExceptions color R J r ⊆ᴮ unionRowExceptions color R J Q Rows := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  exact mem_indexed_union_of_value
    (rowExceptionFamily_is_function (color := color) (R := R) (J := J)
      (inf_le_left.trans HRows)) (inf_le_left.trans Hq)
    (transformedFamily_pair (φ := positiveSectionExceptions color R J)
      positiveSectionExceptions_subset
      (inf_le_left.trans Hq) (inf_le_left.trans Hqr)) inf_le_right

theorem exists_row_image_of_mem_union {Q Rows x : bSet 𝔹} {Γ : 𝔹}
    (Hx : Γ ≤ x ∈ᴮ unionRowValues Q Rows) :
    ∃ q r : bSet 𝔹, Γ ≤ (q ∈ᴮ Q ⊓ pair q r ∈ᴮ Rows) ⊓
      x ∈ᴮ image omegaOne omegaTwo r := by
  obtain ⟨q, X, HX⟩ := exists_indexed_union_witness Hx
  have Hpair := (mem_relationGraph_iff
    (transformedValue_ext_left Rows (fun r => image omegaOne omegaTwo r))
    (transformedValue_ext_right Rows (fun r => image omegaOne omegaTwo r))).mp
    (HX.trans (inf_le_left.trans inf_le_right))
  obtain ⟨r, Hr⟩ := transformedValue_exists B_congr_image_right Hpair.2.2
  exact ⟨q, r, le_inf (le_inf (HX.trans (inf_le_left.trans inf_le_left))
    (Hr.trans inf_le_left)) (mem_congr bv_refl (Hr.trans inf_le_right) (HX.trans inf_le_right))⟩

theorem exists_row_exception_of_mem_union {color : Bool} {R J Q Rows x : bSet 𝔹} {Γ : 𝔹}
    (Hx : Γ ≤ x ∈ᴮ unionRowExceptions color R J Q Rows) :
    ∃ q r : bSet 𝔹, Γ ≤ (q ∈ᴮ Q ⊓ pair q r ∈ᴮ Rows) ⊓
      x ∈ᴮ positiveSectionExceptions color R J r := by
  obtain ⟨q, X, HX⟩ := exists_indexed_union_witness Hx
  have Hpair := (mem_relationGraph_iff
    (transformedValue_ext_left Rows (positiveSectionExceptions color R J))
    (transformedValue_ext_right Rows (positiveSectionExceptions color R J))).mp
    (HX.trans (inf_le_left.trans inf_le_right))
  obtain ⟨r, Hr⟩ := transformedValue_exists
    (positiveSectionExceptions_row_congr color R J) Hpair.2.2
  exact ⟨q, r, le_inf (le_inf (HX.trans (inf_le_left.trans inf_le_left))
    (Hr.trans inf_le_left)) (mem_congr bv_refl (Hr.trans inf_le_right) (HX.trans inf_le_right))⟩

theorem unionRowValues_injects_omegaOne {Q V Rows : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HRows : Γ ≤ is_function Q V Rows)
    (HQ : Γ ≤ injects_into Q omegaOne)
    (HrowInj : Γ ≤ ⨅ q, ⨅ r, _root_.imp (q ∈ᴮ Q ⊓ pair q r ∈ᴮ Rows)
      (is_injective_function omegaOne omegaTwo r)) :
    Γ ≤ injects_into (unionRowValues Q Rows) omegaOne := by
  apply transformedFamily_small HCH HRows HQ B_congr_image_right (fun _ => image_subset)
  apply le_iInf
  intro q
  apply le_iInf
  intro r
  rw [← deduction]
  exact ErdosLargeTwoBlock.injective_image_small
    ((le_inf (inf_le_left.trans (HrowInj.trans ((iInf_le _ q).trans (iInf_le _ r))))
      inf_le_right).trans bv_imp_elim)

theorem unionRowExceptions_injects_omegaOne
    {color : Bool} {R J I B Q V Rows : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HRows : Γ ≤ is_function Q V Rows)
    (HQ : Γ ≤ injects_into Q omegaOne)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (HJ : Γ ≤ isIdeal omegaOne J) (Hclosure : Γ ≤ countableClosure J)
    (HB : Γ ≤ is_function I (bv_powerset omegaOne) B)
    (HBpos : Γ ≤ positiveValues omegaOne J I B)
    (Hdense : Γ ≤ denseValues omegaOne J I B) (HI : Γ ≤ injects_into I omegaOne)
    (HrowInj : Γ ≤ ⨅ q, ⨅ r, _root_.imp (q ∈ᴮ Q ⊓ pair q r ∈ᴮ Rows)
      (is_injective_function omegaOne omegaTwo r))
    (HrowHom : Γ ≤ ⨅ q, ⨅ r, _root_.imp (q ∈ᴮ Q ⊓ pair q r ∈ᴮ Rows)
      (homogeneousUnion color R omegaOne omegaOne r r))
    (Hno : Γ ≤ (hasTwoBlock color R omegaOne bSet.omega omegaTwo)ᶜ)
    (HnoOpp : Γ ≤ (hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo)ᶜ) :
    Γ ≤ injects_into (unionRowExceptions color R J Q Rows) omegaOne := by
  apply transformedFamily_small HCH HRows HQ
    (positiveSectionExceptions_row_congr color R J)
    (fun _ => positiveSectionExceptions_subset)
  apply le_iInf
  intro q
  apply le_iInf
  intro r
  rw [← deduction]
  exact positiveSectionExceptions_injects_omegaOne
    (inf_le_left.trans HCH) (inf_le_left.trans Habsorb)
    (inf_le_left.trans HJ) (inf_le_left.trans Hclosure)
    (inf_le_left.trans HB) (inf_le_left.trans HBpos)
    (inf_le_left.trans Hdense) (inf_le_left.trans HI)
    ((le_inf (inf_le_left.trans (HrowInj.trans ((iInf_le _ q).trans (iInf_le _ r))))
      inf_le_right).trans bv_imp_elim)
    ((le_inf (inf_le_left.trans (HrowHom.trans ((iInf_le _ q).trans (iInf_le _ r))))
      inf_le_right).trans bv_imp_elim)
    (inf_le_left.trans Hno) (inf_le_left.trans HnoOpp)

end bSet.ErdosRowFamilySets
