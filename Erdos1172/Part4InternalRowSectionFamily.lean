/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSectionPullback
public import Erdos1172.Part4InternalSimultaneousFuture

@[expose] public section

/-!
# Actual opposite-section graph of an internally indexed row family

The graph is constructed on all of `omegaOne × omegaTwo` from one actual
row-family graph. Its normal-row data are proved only on the supplied
simultaneous future `L`. In particular, the construction assumes neither a
pre-existing section family nor co-large sections outside that future.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosRowSectionFamily

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosIdeal ErdosColargeIntersection
open ErdosForwardSections ErdosRowFamilySets ErdosRelationGraph
open ErdosSimultaneousFuture ErdosSectionPullback

def rowSectionRel (color : Bool) (R Rows q A : bSet 𝔹) : 𝔹 :=
  ⨆ σ, ⨆ y, q =ᴮ pair σ y ⊓
    ⨆ r, pair σ r ∈ᴮ Rows ⊓ A =ᴮ forwardSection (!color) R r y

theorem rowSectionRel_ext_index (color : Bool) (R Rows A : bSet 𝔹) :
    B_ext (fun q => rowSectionRel color R Rows q A) :=
  B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
    B_ext_inf B_ext_bv_eq_left B_ext_const))

theorem rowSectionRel_ext_value (color : Bool) (R Rows q : bSet 𝔹) :
    B_ext (rowSectionRel color R Rows q) :=
  B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
    B_ext_inf B_ext_const (B_ext_iSup (h := fun _ =>
      B_ext_inf B_ext_const B_ext_bv_eq_left))))

private theorem rowSectionValue_ext_row (color : Bool) (R Rows σ y A : bSet 𝔹) :
    B_ext (fun r => pair σ r ∈ᴮ Rows ⊓ A =ᴮ forwardSection (!color) R r y) :=
  B_ext_inf B_ext_pair_mem_right
    (B_ext_term (ϕ := fun B => A =ᴮ B) (t := fun r => forwardSection (!color) R r y)
      B_ext_bv_eq_right (forwardSection_row_congr (!color) R y))

theorem rowSectionRel_pair (color : Bool) (R Rows σ y A : bSet 𝔹) :
    rowSectionRel color R Rows (pair σ y) A =
      ⨆ r, pair σ r ∈ᴮ Rows ⊓ A =ᴮ forwardSection (!color) R r y := by
  apply le_antisymm
  · unfold rowSectionRel
    apply iSup_le
    intro τ
    apply iSup_le
    intro z
    rw [inf_iSup_eq]
    apply iSup_le
    intro r
    apply le_iSup_of_le r
    refine le_inf ?_ ?_
    · exact bv_rw' (ϕ := fun t => pair t r ∈ᴮ Rows)
        (eq_of_eq_pair_left' inf_le_left) (h_congr := B_ext_pair_mem_left)
        (H_new := inf_le_right.trans inf_le_left)
    · exact bv_rw' (ϕ := fun t => A =ᴮ forwardSection (!color) R r t)
        (eq_of_eq_pair_right' inf_le_left)
        (h_congr := B_ext_term (ϕ := fun B => A =ᴮ B)
          (t := forwardSection (!color) R r) B_ext_bv_eq_right
          (forwardSection_congr (!color) R r))
        (H_new := inf_le_right.trans inf_le_right)
  · exact le_iSup_of_le σ (le_iSup_of_le y (le_inf bv_refl le_rfl))

/-- `color` is the color of the old rows; these are their opposite sections. -/
def rowSections (color : Bool) (R Rows : bSet 𝔹) : bSet 𝔹 :=
  relationGraph (prod omegaOne omegaTwo) (bv_powerset omegaOne)
    (rowSectionRel color R Rows)

theorem mem_rowSections_iff {color : Bool} {R Rows q A : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair q A ∈ᴮ rowSections color R Rows ↔
      Γ ≤ q ∈ᴮ prod omegaOne omegaTwo ∧ Γ ≤ A ∈ᴮ bv_powerset omegaOne ∧
        Γ ≤ rowSectionRel color R Rows q A :=
  mem_relationGraph_iff (rowSectionRel_ext_index color R Rows)
    (rowSectionRel_ext_value color R Rows)

theorem rowSections_pair_iff {color : Bool} {R Rows σ y A : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair (pair σ y) A ∈ᴮ rowSections color R Rows ↔
      Γ ≤ σ ∈ᴮ omegaOne ∧ Γ ≤ y ∈ᴮ omegaTwo ∧
        Γ ≤ A ∈ᴮ bv_powerset omegaOne ∧
          Γ ≤ ⨆ r, pair σ r ∈ᴮ Rows ⊓ A =ᴮ forwardSection (!color) R r y := by
  rw [mem_rowSections_iff, rowSectionRel_pair]
  constructor
  · rintro ⟨Hpair, HA, Hrel⟩
    exact ⟨(mem_prod_iff.mp Hpair).1, (mem_prod_iff.mp Hpair).2, HA, Hrel⟩
  · rintro ⟨Hσ, Hy, HA, Hrel⟩
    exact ⟨mem_prod Hσ Hy, HA, Hrel⟩

theorem rowSections_witness {color : Bool} {R Rows σ y A : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ pair (pair σ y) A ∈ᴮ rowSections color R Rows) :
    ∃ r : bSet 𝔹, Γ ≤ pair σ r ∈ᴮ Rows ⊓ A =ᴮ forwardSection (!color) R r y :=
  exists_convert (rowSections_pair_iff.mp H).2.2.2
    (rowSectionValue_ext_row color R Rows σ y A)

theorem rowSections_value_of_pair {color : Bool} {R Rows σ r y A : bSet 𝔹} {Γ : 𝔹}
    (Hfunc : Γ ≤ is_func Rows) (Hrow : Γ ≤ pair σ r ∈ᴮ Rows)
    (Hsection : Γ ≤ pair (pair σ y) A ∈ᴮ rowSections color R Rows) :
    Γ ≤ A =ᴮ forwardSection (!color) R r y := by
  obtain ⟨r', Hr'⟩ := rowSections_witness Hsection
  have Heq : Γ ≤ r' =ᴮ r :=
    eq_of_is_func_of_eq Hfunc bv_refl (Hr'.trans inf_le_left) Hrow
  exact bv_trans (Hr'.trans inf_le_right)
    (forwardSection_row_congr (!color) R y Heq)

theorem rowSections_pair_iff_of_row
    {color : Bool} {R Rows σ r y A : bSet 𝔹} {Γ : 𝔹}
    (Hfunc : Γ ≤ is_func Rows) (Hσ : Γ ≤ σ ∈ᴮ omegaOne)
    (Hy : Γ ≤ y ∈ᴮ omegaTwo) (Hrow : Γ ≤ pair σ r ∈ᴮ Rows) :
    (Γ ≤ pair (pair σ y) A ∈ᴮ rowSections color R Rows) ↔
      Γ ≤ A =ᴮ forwardSection (!color) R r y := by
  constructor
  · exact rowSections_value_of_pair Hfunc Hrow
  · intro Heq
    exact rowSections_pair_iff.mpr ⟨Hσ, Hy,
      mem_congr (bv_symm Heq) bv_refl (mem_powerset_iff.mpr forwardSection_subset),
      le_iSup_of_le r (le_inf Hrow Heq)⟩

/-- Functionality of the row family suffices: the selected rows need not
themselves be injective or even functions to construct their section sets. -/
theorem rowSections_is_function {color : Bool} {R Rows : bSet 𝔹} {Γ : 𝔹}
    (HRows : Γ ≤ is_function omegaOne (bv_powerset (prod omegaOne omegaTwo)) Rows) :
    Γ ≤ is_function (prod omegaOne omegaTwo) (bv_powerset omegaOne)
      (rowSections color R Rows) := by
  apply relationGraph_is_function (P := rowSectionRel color R Rows)
    (rowSectionRel_ext_index color R Rows) (rowSectionRel_ext_value color R Rows)
  · apply le_iInf
    intro q
    rw [← deduction]
    let Δ := Γ ⊓ q ∈ᴮ prod omegaOne omegaTwo
    obtain ⟨σ, Hσ, y, _, Hq⟩ := mem_prod_iff₂.mp
      (show Δ ≤ q ∈ᴮ prod omegaOne omegaTwo from inf_le_right)
    have Hr : Δ ≤ ⨆ r, r ∈ᴮ bv_powerset (prod omegaOne omegaTwo) ⊓ pair σ r ∈ᴮ Rows :=
      (le_inf (inf_le_left.trans
        ((is_total_of_is_function HRows).trans (iInf_le _ σ))) Hσ).trans bv_imp_elim
    obtain ⟨r, Hr⟩ := exists_convert Hr (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
    exact le_iSup_of_le (forwardSection (!color) R r y)
      (le_inf (mem_powerset_iff.mpr forwardSection_subset)
        (le_iSup_of_le σ (le_iSup_of_le y (le_inf Hq
          (le_iSup_of_le r (le_inf (Hr.trans inf_le_right) bv_refl))))))
  · intro q₁ q₂ A B Δ HΔ Hq₁ Hq₂ _ _ Hrel₁ Hrel₂ Hq
    obtain ⟨σ, _, y, _, Hqσ⟩ := mem_prod_iff₂.mp Hq₁
    obtain ⟨τ, _, z, _, Hqτ⟩ := mem_prod_iff₂.mp Hq₂
    have Heq : Δ ≤ pair σ y =ᴮ pair τ z :=
      bv_trans (bv_symm Hqσ) (bv_trans Hq Hqτ)
    have HA : Δ ≤ ⨆ r, pair σ r ∈ᴮ Rows ⊓ A =ᴮ forwardSection (!color) R r y := by
      rw [← rowSectionRel_pair]
      exact bv_rw'' (ϕ := fun q => rowSectionRel color R Rows q A) Hqσ Hrel₁
        (rowSectionRel_ext_index color R Rows A)
    have HB : Δ ≤ ⨆ r, pair τ r ∈ᴮ Rows ⊓ B =ᴮ forwardSection (!color) R r z := by
      rw [← rowSectionRel_pair]
      exact bv_rw'' (ϕ := fun q => rowSectionRel color R Rows q B) Hqτ Hrel₂
        (rowSectionRel_ext_index color R Rows B)
    obtain ⟨r, Hr⟩ := exists_convert HA (rowSectionValue_ext_row color R Rows σ y A)
    obtain ⟨s, Hs⟩ := exists_convert HB (rowSectionValue_ext_row color R Rows τ z B)
    have Hrs : Δ ≤ r =ᴮ s := eq_of_is_function_of_eq (HΔ.trans HRows)
      (eq_of_eq_pair_left' Heq) (Hr.trans inf_le_left) (Hs.trans inf_le_left)
    have Hsections : Δ ≤ forwardSection (!color) R r y =ᴮ forwardSection (!color) R s z :=
      bv_trans (forwardSection_row_congr (!color) R y Hrs)
        (forwardSection_congr (!color) R s (eq_of_eq_pair_right' Heq))
    exact bv_trans (Hr.trans inf_le_right)
      (bv_trans Hsections (bv_symm (Hs.trans inf_le_right)))

/-- The simultaneous future supplies exactly the small complement needed
for the constructed value, and no assertion about vertices outside `L`. -/
theorem rowSections_colarge_on
    {color : Bool} {R Rows L J σ y A : bSet 𝔹} {Γ : 𝔹}
    (Hfuture : Γ ≤ oppositeSectionsColarge color R J omegaOne Rows L)
    (Hy : Γ ≤ y ∈ᴮ L)
    (Hsection : Γ ≤ pair (pair σ y) A ∈ᴮ rowSections color R Rows) :
    Γ ≤ colarge omegaOne J A := by
  obtain ⟨r, Hr⟩ := rowSections_witness Hsection
  have Hsmall : Γ ≤ difference omegaOne (forwardSection (!color) R r y) ∈ᴮ J :=
    (le_inf (Hfuture.trans ((iInf_le _ σ).trans ((iInf_le _ r).trans (iInf_le _ y))))
      (le_inf (le_inf (rowSections_pair_iff.mp Hsection).1 (Hr.trans inf_le_left)) Hy)).trans
        bv_imp_elim
  exact le_inf (mem_powerset_iff.mp (rowSections_pair_iff.mp Hsection).2.2.1)
    (mem_congr (bv_symm (difference_congr_right (Hr.trans inf_le_right))) bv_refl Hsmall)

theorem rowNormalIdealDataOn_rowSections
    {color : Bool} {R Rows L J σ : bSet 𝔹} {Γ : 𝔹}
    (Hproper : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hdiag : Γ ≤ diagonalClosure omegaOne J)
    (Hfuture : Γ ≤ oppositeSectionsColarge color R J omegaOne Rows L) :
    Γ ≤ rowNormalIdealDataOn (rowSections color R Rows) L σ J := by
  refine le_inf (le_inf Hproper (le_inf Habsorb (le_inf Hclosure ?_))) Hdiag
  apply le_iInf
  intro y
  apply le_iInf
  intro A
  rw [← deduction]
  exact rowSections_colarge_on (inf_le_left.trans Hfuture)
    (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)

theorem normalRowAvailabilityOn_rowSections
    {color : Bool} {R Rows L J : bSet 𝔹} {Γ : 𝔹}
    (Hproper : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hdiag : Γ ≤ diagonalClosure omegaOne J)
    (Hfuture : Γ ≤ oppositeSectionsColarge color R J omegaOne Rows L) :
    Γ ≤ normalRowAvailabilityOn (rowSections color R Rows) L := by
  apply le_iInf
  intro σ
  rw [← deduction]
  exact le_iSup_of_le J (rowNormalIdealDataOn_rowSections (σ := σ)
    (inf_le_left.trans Hproper) (inf_le_left.trans Habsorb)
    (inf_le_left.trans Hclosure) (inf_le_left.trans Hdiag) (inf_le_left.trans Hfuture))

end bSet.ErdosRowSectionFamily
