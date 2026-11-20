/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalForwardSections

@[expose] public section

/-!
Above every used value of a total row, the two forward sections are exact
complements within omega-one. Their disjointness uses single-valuedness;
their coverage uses totality and strict order. No partition, ideal
normality, or ground-name assumptions enter these statements.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosForwardSectionComplement

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosIdeal ErdosForwardSections

private theorem color_of_not_opposite {color : Bool} {R x y : bSet 𝔹} {Γ : 𝔹}
    (Hxy : Γ ≤ x ∈ᴮ y) (Hnot : Γ ≤ (graphColor (!color) R x y)ᶜ) :
    Γ ≤ graphColor color R x y := by
  have Hcover : Γ ≤ graphColor color R x y ⊔ graphColor (!color) R x y := by
    cases color with
    | false =>
        change Γ ≤ graphColor false R x y ⊔ graphColor true R x y
        rw [graphColor_sup]
        exact Hxy.trans le_sup_left
    | true =>
        change Γ ≤ graphColor true R x y ⊔ graphColor false R x y
        rw [sup_comm, graphColor_sup]
        exact Hxy.trans le_sup_left
  apply (le_inf (le_refl Γ) Hcover).trans
  rw [inf_sup_left]
  exact sup_le inf_le_right
    ((bv_absurd _ inf_le_right (inf_le_left.trans Hnot)).trans bot_le)

/-- Totality gives a real value at every coordinate; above that value,
failure of the opposite forward section forces the chosen-color section. -/
theorem forwardSection_complement_subset
    {color : Bool} {R r y : bSet 𝔹} {Γ : 𝔹}
    (Hr : Γ ≤ is_function omegaOne omegaTwo r)
    (Hbefore : Γ ≤ ⨅ x, _root_.imp (rangeMem omegaOne r x) (x ∈ᴮ y)) :
    Γ ≤ difference omegaOne (forwardSection (!color) R r y) ⊆ᴮ
      forwardSection color R r y := by
  rw [subset_unfold']
  apply le_iInf
  intro i
  rw [← deduction]
  let Δ := Γ ⊓ i ∈ᴮ difference omegaOne (forwardSection (!color) R r y)
  have Hi : Δ ≤ i ∈ᴮ omegaOne ⊓ (i ∈ᴮ forwardSection (!color) R r y)ᶜ := by
    rw [← mem_difference]
    exact inf_le_right
  have Htotal : Δ ≤ ⨆ x, x ∈ᴮ omegaTwo ⊓ pair i x ∈ᴮ r :=
    (le_inf ((is_total_of_is_function (inf_le_left.trans Hr)).trans (iInf_le _ i))
      (Hi.trans inf_le_left)).trans bv_imp_elim
  obtain ⟨x, Hx⟩ := exists_convert Htotal
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hrange : Δ ≤ rangeMem omegaOne r x :=
    le_iSup_of_le i (le_inf (Hi.trans inf_le_left) (Hx.trans inf_le_right))
  have Hxy : Δ ≤ x ∈ᴮ y :=
    (le_inf (inf_le_left.trans (Hbefore.trans (iInf_le _ x))) Hrange).trans bv_imp_elim
  have Hnot : Δ ≤ (graphColor (!color) R x y)ᶜ := by
    rw [← imp_bot, ← deduction]
    have Hsection : Δ ⊓ graphColor (!color) R x y ≤
        i ∈ᴮ forwardSection (!color) R r y :=
      mem_forwardSection_of_pair (inf_le_left.trans (Hi.trans inf_le_left))
        (inf_le_left.trans (Hx.trans inf_le_right)) (inf_le_left.trans Hxy) inf_le_right
    exact bv_absurd _ Hsection (inf_le_left.trans (Hi.trans inf_le_right))
  exact mem_forwardSection_of_pair (Hi.trans inf_le_left) (Hx.trans inf_le_right)
    Hxy (color_of_not_opposite Hxy Hnot)

/-- A small chosen-color section makes the opposite forward section
co-large in the supplied ideal. No normality or target exclusion is used. -/
theorem opposite_forwardSection_colarge
    {color : Bool} {R J r y : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J) (Hr : Γ ≤ is_function omegaOne omegaTwo r)
    (Hbefore : Γ ≤ ⨅ x, _root_.imp (rangeMem omegaOne r x) (x ∈ᴮ y))
    (Hsmall : Γ ≤ forwardSection color R r y ∈ᴮ J) :
    Γ ≤ difference omegaOne (forwardSection (!color) R r y) ∈ᴮ J :=
  small_of_subset (downwardClosed_of_isIdeal HJ) Hsmall
    (forwardSection_complement_subset Hr Hbefore)

end bSet.ErdosForwardSectionComplement
