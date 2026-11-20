/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalPositiveSectionsEndpoint

@[expose] public section

/-!
# Internally small exceptional sets of positive forward sections

The exceptional set is the actual separation of omega-two by positivity
of the computed forward section. If neither color admits the two-block
target, this set injects into omega-one: its alternative cardinal size
would trigger the proved positive-sections endpoint. No exception bound,
compatible mask, or external enumeration is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosPositiveSectionExceptions

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosIdeal ErdosDenseBasis
open ErdosForwardSections ErdosPositiveSectionsEndpoint

theorem positive_forwardSection_ext (color : Bool) (R J r : bSet 𝔹) :
    B_ext (fun y => positive omegaOne J (forwardSection color R r y)) :=
  B_ext_term (ϕ := positive omegaOne J) (t := forwardSection color R r)
    (B_ext_inf B_ext_subset_left (B_ext_neg (h := B_ext_mem_left)))
    (forwardSection_congr color R r)

/-- Exactly the omega-two vertices whose forward row section is positive. -/
def positiveSectionExceptions (color : Bool) (R J r : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun y => positive omegaOne J (forwardSection color R r y)) omegaTwo

theorem mem_positiveSectionExceptions_iff
    {color : Bool} {R J r y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ y ∈ᴮ positiveSectionExceptions color R J r ↔
      (Γ ≤ y ∈ᴮ omegaTwo) ∧
        Γ ≤ positive omegaOne J (forwardSection color R r y) :=
  ErdosRelationGraph.mem_comprehend_and (positive_forwardSection_ext color R J r)

theorem positiveSectionExceptions_subset
    {color : Bool} {R J r : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ positiveSectionExceptions color R J r ⊆ᴮ omegaTwo :=
  comprehend_subset
    (ϕ := fun y => positive omegaOne J (forwardSection color R r y)) omegaTwo

theorem positiveSectionExceptions_positive
    {color : Bool} {R J r : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ ⨅ y : bSet 𝔹,
      _root_.imp (y ∈ᴮ positiveSectionExceptions color R J r)
        (positive omegaOne J (forwardSection color R r y)) := by
  apply le_iInf
  intro y
  rw [← deduction]
  exact (mem_positiveSectionExceptions_iff.mp
    (show Γ ⊓ y ∈ᴮ positiveSectionExceptions color R J r ≤
      y ∈ᴮ positiveSectionExceptions color R J r from inf_le_right)).2

/-- Outside the concrete exception set, an omega-two vertex has an
ideal-small section. Its subset-of-omega-one guard is proved, not assumed. -/
theorem forwardSection_small_of_not_mem_exceptions
    {color : Bool} {R J r y : bSet 𝔹} {Γ : 𝔹}
    (Hy : Γ ≤ y ∈ᴮ omegaTwo)
    (Hnot : Γ ≤ (y ∈ᴮ positiveSectionExceptions color R J r)ᶜ) :
    Γ ≤ forwardSection color R r y ∈ᴮ J := by
  rw [← compl_compl (forwardSection color R r y ∈ᴮ J), ← imp_bot, ← deduction]
  have Hpos : Γ ⊓ (forwardSection color R r y ∈ᴮ J)ᶜ ≤
      positive omegaOne J (forwardSection color R r y) :=
    le_inf forwardSection_subset inf_le_right
  have Hmem : Γ ⊓ (forwardSection color R r y ∈ᴮ J)ᶜ ≤
      y ∈ᴮ positiveSectionExceptions color R J r :=
    mem_positiveSectionExceptions_iff.mpr ⟨inf_le_left.trans Hy, Hpos⟩
  exact bv_absurd _ Hmem (inf_le_left.trans Hnot)

/-- Failure of both exact targets forces the actual positive-section
exception set to be internally at most omega-one sized. -/
theorem positiveSectionExceptions_injects_omegaOne
    {color : Bool} {R J I B r : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (HJ : Γ ≤ isIdeal omegaOne J) (Hclosure : Γ ≤ countableClosure J)
    (HB : Γ ≤ is_function I (bv_powerset omegaOne) B)
    (HBpos : Γ ≤ positiveValues omegaOne J I B)
    (Hdense : Γ ≤ denseValues omegaOne J I B)
    (HI : Γ ≤ injects_into I omegaOne)
    (Hr : Γ ≤ is_injective_function omegaOne omegaTwo r)
    (Hrow : Γ ≤ homogeneousUnion color R omegaOne omegaOne r r)
    (Hno : Γ ≤ (hasTwoBlock color R omegaOne bSet.omega omegaTwo)ᶜ)
    (HnoOpp : Γ ≤ (hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo)ᶜ) :
    Γ ≤ injects_into (positiveSectionExceptions color R J r) omegaOne := by
  let E := positiveSectionExceptions color R J r
  have Hcases : Γ ≤ injects_into E omegaOne ⊔ injects_into omegaTwo E :=
    ErdosPartialInjection.omegaTwo_cardinal_dichotomy
  apply (le_inf (le_refl Γ) Hcases).trans
  rw [inf_sup_left]
  apply sup_le
  · exact inf_le_right
  · let Δ := Γ ⊓ injects_into omegaTwo E
    have Htarget : Δ ≤ hasTwoBlock color R omegaOne bSet.omega omegaTwo ⊔
        hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo :=
      target_of_large_positive_sections
        (inf_le_left.trans HCH) (inf_le_left.trans Habsorb)
        (inf_le_left.trans HJ) (inf_le_left.trans Hclosure)
        (inf_le_left.trans HB) (inf_le_left.trans HBpos)
        (inf_le_left.trans Hdense) (inf_le_left.trans HI)
        (inf_le_left.trans Hr) (inf_le_left.trans Hrow)
        (positiveSectionExceptions_subset (color := color) (R := R) (J := J) (r := r)
          (Γ := Δ))
        (show Δ ≤ injects_into omegaTwo E from inf_le_right)
        (positiveSectionExceptions_positive (color := color) (R := R) (J := J) (r := r)
          (Γ := Δ))
    have HnotTarget : Δ ≤ (hasTwoBlock color R omegaOne bSet.omega omegaTwo ⊔
        hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo)ᶜ := by
      rw [compl_sup]
      exact le_inf (inf_le_left.trans Hno) (inf_le_left.trans HnoOpp)
    exact (bv_absurd _ Htarget HnotTarget).trans bot_le

end bSet.ErdosPositiveSectionExceptions
