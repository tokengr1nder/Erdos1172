/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSmallFiberBound

@[expose] public section

/-!
# One total bounded selector with explicit failure

A fixed actual selector chooses a candidate whenever one exists, and a
specified bounded fallback otherwise. Both alternatives are Boolean
conditions: no external decision or pointwise witness coherence is
assumed. This supplies a total-choice primitive for block recursion; it
does not assert that the block candidate predicate is ever satisfied.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosBoundedFallbackChoice

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

def candidateValue (C : bSet 𝔹) (P : bSet 𝔹 → bSet 𝔹 → 𝔹) (i : bSet 𝔹) : 𝔹 :=
  ⨆ x, x ∈ᴮ C ⊓ P i x

def fallbackData (C : bSet 𝔹) (P : bSet 𝔹 → bSet 𝔹 → 𝔹)
    (fallback i x : bSet 𝔹) : 𝔹 :=
  (candidateValue C P i ⊓ P i x) ⊔
    ((candidateValue C P i)ᶜ ⊓ x =ᴮ fallback)

theorem candidateValue_ext_index {C : bSet 𝔹} {P : bSet 𝔹 → bSet 𝔹 → 𝔹}
    (Hleft : ∀ x, B_ext (fun i => P i x)) : B_ext (candidateValue C P) :=
  B_ext_iSup (h := fun x => B_ext_inf B_ext_const (Hleft x))

theorem fallbackData_ext_index {C fallback x : bSet 𝔹}
    {P : bSet 𝔹 → bSet 𝔹 → 𝔹} (Hleft : ∀ y, B_ext (fun i => P i y)) :
    B_ext (fun i => fallbackData C P fallback i x) :=
  B_ext_sup
    (h₁ := B_ext_inf (candidateValue_ext_index Hleft) (Hleft x))
    (h₂ := B_ext_inf (B_ext_neg (h := candidateValue_ext_index Hleft)) B_ext_const)

theorem fallbackData_ext_value {C fallback i : bSet 𝔹}
    {P : bSet 𝔹 → bSet 𝔹 → 𝔹} (Hright : B_ext (P i)) :
    B_ext (fallbackData C P fallback i) :=
  B_ext_sup (h₁ := B_ext_inf B_ext_const Hright) (h₂ := B_ext_inf B_ext_const B_ext_bv_eq_left)

theorem fallbackData_of_candidate {C fallback i x : bSet 𝔹}
    {P : bSet 𝔹 → bSet 𝔹 → 𝔹} {Γ : 𝔹}
    (Hx : Γ ≤ x ∈ᴮ C) (HP : Γ ≤ P i x) : Γ ≤ fallbackData C P fallback i x :=
  (le_inf (le_iSup_of_le x (le_inf Hx HP)) HP).trans le_sup_left

theorem fallbackData_of_absence {C fallback i : bSet 𝔹}
    {P : bSet 𝔹 → bSet 𝔹 → 𝔹} {Γ : 𝔹}
    (Hno : Γ ≤ (candidateValue C P i)ᶜ) : Γ ≤ fallbackData C P fallback i fallback :=
  (le_inf Hno bv_refl).trans le_sup_right

theorem fallbackData_success {C fallback i x : bSet 𝔹}
    {P : bSet 𝔹 → bSet 𝔹 → 𝔹} {Γ : 𝔹}
    (Hdata : Γ ≤ fallbackData C P fallback i x)
    (Hex : Γ ≤ candidateValue C P i) : Γ ≤ P i x := by
  apply (le_inf Hex Hdata).trans
  unfold fallbackData
  rw [inf_sup_left]
  apply sup_le
  · exact inf_le_right.trans inf_le_right
  · exact (bv_absurd _ inf_le_left (inf_le_right.trans inf_le_left)).trans bot_le

theorem fallbackData_failure {C fallback i x : bSet 𝔹}
    {P : bSet 𝔹 → bSet 𝔹 → 𝔹} {Γ : 𝔹}
    (Hdata : Γ ≤ fallbackData C P fallback i x)
    (Hno : Γ ≤ (candidateValue C P i)ᶜ) : Γ ≤ x =ᴮ fallback := by
  apply (le_inf Hno Hdata).trans
  unfold fallbackData
  rw [inf_sup_left]
  apply sup_le
  · exact (bv_absurd _ (inf_le_right.trans inf_le_left) inf_le_left).trans bot_le
  · exact inf_le_right.trans inf_le_right

theorem fallbackData_value {C fallback i : bSet 𝔹}
    {P : bSet 𝔹 → bSet 𝔹 → 𝔹} {Γ : 𝔹}
    (Hright : B_ext (P i)) (Hfallback : Γ ≤ fallback ∈ᴮ C) :
    Γ ≤ ⨆ x, x ∈ᴮ C ⊓ fallbackData C P fallback i x := by
  calc
    Γ = (Γ ⊓ candidateValue C P i) ⊔ (Γ ⊓ (candidateValue C P i)ᶜ) := by
      rw [← inf_sup_left, sup_compl_eq_top, inf_top_eq]
    _ ≤ ⨆ x, x ∈ᴮ C ⊓ fallbackData C P fallback i x := by
      apply sup_le
      · obtain ⟨x, Hx⟩ := exists_convert
          (show Γ ⊓ candidateValue C P i ≤ ⨆ x, x ∈ᴮ C ⊓ P i x from inf_le_right)
          (B_ext_inf B_ext_mem_left Hright)
        exact le_iSup_of_le x (le_inf (Hx.trans inf_le_left)
          (fallbackData_of_candidate (Hx.trans inf_le_left) (Hx.trans inf_le_right)))
      · exact le_iSup_of_le fallback (le_inf (inf_le_left.trans Hfallback)
          (fallbackData_of_absence inf_le_right))

def fallbackFamilyLaw (D C : bSet 𝔹) (P : bSet 𝔹 → bSet 𝔹 → 𝔹)
    (fallback F : bSet 𝔹) : 𝔹 :=
  ⨅ i, ⨅ x, _root_.imp (i ∈ᴮ D ⊓ pair i x ∈ᴮ F) (fallbackData C P fallback i x)

theorem exists_fallback_selector {D C fallback : bSet 𝔹}
    {P : bSet 𝔹 → bSet 𝔹 → 𝔹} {Γ : 𝔹}
    (Hleft : ∀ x, B_ext (fun i => P i x)) (Hright : ∀ i, B_ext (P i))
    (Hfallback : Γ ≤ fallback ∈ᴮ C) :
    ∃ F : bSet 𝔹, Γ ≤ is_function D C F ⊓ fallbackFamilyLaw D C P fallback F := by
  apply ErdosSmallFiberBound.exists_selector_of_pointwise
    (fun _ => fallbackData_ext_index Hleft) (fun i => fallbackData_ext_value (Hright i))
  apply le_iInf
  intro i
  rw [← deduction]
  exact fallbackData_value (Hright i) (inf_le_left.trans Hfallback)

theorem selected_fallbackData {D C fallback F i x : bSet 𝔹}
    {P : bSet 𝔹 → bSet 𝔹 → 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function D C F) (Hlaw : Γ ≤ fallbackFamilyLaw D C P fallback F)
    (Hpair : Γ ≤ pair i x ∈ᴮ F) : Γ ≤ fallbackData C P fallback i x :=
  (le_inf (Hlaw.trans ((iInf_le _ i).trans (iInf_le _ x)))
    (le_inf (mem_domain_of_is_function Hpair HF) Hpair)).trans bv_imp_elim

theorem selected_candidate {D C fallback F i x : bSet 𝔹}
    {P : bSet 𝔹 → bSet 𝔹 → 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function D C F) (Hlaw : Γ ≤ fallbackFamilyLaw D C P fallback F)
    (Hpair : Γ ≤ pair i x ∈ᴮ F) (Hex : Γ ≤ candidateValue C P i) : Γ ≤ P i x :=
  fallbackData_success (selected_fallbackData HF Hlaw Hpair) Hex

theorem selected_failure {D C fallback F i x : bSet 𝔹}
    {P : bSet 𝔹 → bSet 𝔹 → 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function D C F) (Hlaw : Γ ≤ fallbackFamilyLaw D C P fallback F)
    (Hpair : Γ ≤ pair i x ∈ᴮ F) (Hno : Γ ≤ (candidateValue C P i)ᶜ) :
    Γ ≤ x =ᴮ fallback :=
  fallbackData_failure (selected_fallbackData HF Hlaw Hpair) Hno

end bSet.ErdosBoundedFallbackChoice
