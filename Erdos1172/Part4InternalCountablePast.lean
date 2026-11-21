/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCountableAbsorption
public import Erdos1172.Part4InternalIdealCentering
public import Erdos1172.Part4InternalCountableImage

@[expose] public section

/-!
The actual past of a countable family of omega-one ordinals consists of
the family and its union. Countable absorption and countable ideal closure
make this past small, without a separate ordinal-regularity assumption.
Avoiding it is exactly the law of lying strictly above every family member.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCountablePast

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal

def past (A : bSet 𝔹) : bSet 𝔹 := binary_union A (bv_union A)

/-- Every member of a subset of omega-one is itself countable and absorbed.
The indexing family need not be countable for this pointwise statement. -/
theorem ordinal_members_small {A J : bSet 𝔹} {Γ : 𝔹}
    (Habsorb : Γ ≤ countableAbsorption omegaOne J) (HA : Γ ≤ A ⊆ᴮ omegaOne) :
    Γ ≤ A ⊆ᴮ J := by
  rw [subset_unfold']
  apply le_iInf
  intro a
  rw [← deduction]
  have Ha : Γ ⊓ a ∈ᴮ A ≤ a ∈ᴮ omegaOne := mem_of_mem_subset (inf_le_left.trans HA) inf_le_right
  exact countableAbsorption_apply (inf_le_left.trans Habsorb)
    (subset_of_mem_Ord Ha omegaOne_Ord) (omegaOne_member_injects Ha)

/-- Countable closure applies to the actual family A, since each of its
ordinal members is small. No finite-ideal or properness premise is needed. -/
theorem union_small {A J : bSet 𝔹} {Γ : 𝔹}
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J) (HA : Γ ≤ A ⊆ᴮ omegaOne)
    (Hcount : Γ ≤ injects_into A bSet.omega) : Γ ≤ bv_union A ∈ᴮ J :=
  countable_union_small Hclosure Hcount (ordinal_members_small Habsorb HA)

theorem past_small {A J : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J) (HA : Γ ≤ A ⊆ᴮ omegaOne)
    (Hcount : Γ ≤ injects_into A bSet.omega) : Γ ≤ past A ∈ᴮ J :=
  small_union (unionClosed_of_isIdeal HJ)
    (countableAbsorption_apply Habsorb HA Hcount)
    (union_small Habsorb Hclosure HA Hcount)

/-- An ordinal outside the actual past follows every member of the family. -/
theorem above_past {A x : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ A ⊆ᴮ omegaOne) (Hx : Γ ≤ x ∈ᴮ omegaOne)
    (Hnot : Γ ≤ (x ∈ᴮ past A)ᶜ) :
    Γ ≤ ⨅ a, _root_.imp (a ∈ᴮ A) (a ∈ᴮ x) := by
  apply le_iInf
  intro a
  rw [← deduction]
  let Δ := Γ ⊓ a ∈ᴮ A
  have Ha : Δ ≤ a ∈ᴮ omegaOne := mem_of_mem_subset (inf_le_left.trans HA) inf_le_right
  have Hcases := epsilon_trichotomy_of_Ord (inf_le_left.trans Hx) Ha omegaOne_Ord
  change Δ ≤ a ∈ᴮ x
  apply (le_inf (le_refl Δ) Hcases).trans
  rw [inf_sup_left, inf_sup_left]
  apply sup_le
  · apply sup_le
    · have HxA : Δ ⊓ x =ᴮ a ≤ x ∈ᴮ A :=
        mem_congr (bv_symm inf_le_right) bv_refl (inf_le_left.trans inf_le_right)
      have Hxpast : Δ ⊓ x =ᴮ a ≤ x ∈ᴮ past A := by
        change Δ ⊓ x =ᴮ a ≤ x ∈ᴮ binary_union A (bv_union A)
        rw [mem_binary_union]
        exact HxA.trans le_sup_left
      exact (bv_absurd _ Hxpast (inf_le_left.trans (inf_le_left.trans Hnot))).trans bot_le
    · have HxUnion : Δ ⊓ x ∈ᴮ a ≤ x ∈ᴮ bv_union A :=
        mem_bv_union_iff.mpr (le_iSup_of_le a
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
      have Hxpast : Δ ⊓ x ∈ᴮ a ≤ x ∈ᴮ past A := by
        change Δ ⊓ x ∈ᴮ a ≤ x ∈ᴮ binary_union A (bv_union A)
        rw [mem_binary_union]
        exact HxUnion.trans le_sup_right
      exact (bv_absurd _ Hxpast (inf_le_left.trans (inf_le_left.trans Hnot))).trans bot_le
  · exact inf_le_right

/-- The reverse implication is valid for arbitrary names, using only
the impossibility of membership self-loops and two-cycles. -/
theorem not_mem_past_of_above {A x : bSet 𝔹} {Γ : 𝔹}
    (Habove : Γ ≤ ⨅ a, _root_.imp (a ∈ᴮ A) (a ∈ᴮ x)) :
    Γ ≤ (x ∈ᴮ past A)ᶜ := by
  rw [← imp_bot, ← deduction]
  change Γ ⊓ x ∈ᴮ binary_union A (bv_union A) ≤ ⊥
  rw [mem_binary_union, inf_sup_left]
  apply sup_le
  · exact bot_of_mem_self'
      ((le_inf (inf_le_left.trans (Habove.trans (iInf_le _ x))) inf_le_right).trans bv_imp_elim)
  · have Hmem : Γ ⊓ x ∈ᴮ bv_union A ≤ ⨆ a, a ∈ᴮ A ⊓ x ∈ᴮ a := mem_bv_union_iff.mp inf_le_right
    obtain ⟨a, Ha⟩ := exists_convert Hmem (B_ext_inf B_ext_mem_left B_ext_mem_right)
    have Hax : Γ ⊓ x ∈ᴮ bv_union A ≤ a ∈ᴮ x :=
      (le_inf (inf_le_left.trans (Habove.trans (iInf_le _ a)))
        (Ha.trans inf_le_left)).trans bv_imp_elim
    exact bot_of_mem_mem' a x Hax (Ha.trans inf_le_right)

/-- The genuine image of a history indexed below omega-one has small past. -/
theorem image_past_small {δ h J : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hh : Γ ≤ is_func' δ omegaOne h) (Hδ : Γ ≤ δ ∈ᴮ omegaOne) :
    Γ ≤ past (image δ omegaOne h) ∈ᴮ J :=
  past_small HJ Habsorb Hclosure image_subset
    (ErdosCountableImage.image_countable Hh (omegaOne_member_injects Hδ))

end bSet.ErdosCountablePast
