/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalIdealSemantics

@[expose] public section

/-!
# Removing an arbitrary internally countable family of ideal losses

The countable family is itself a Boolean-valued name whose internal
countability is expressed by injection into omega. It is not an external
natural-number sequence. Removing its union from a positive base gives an
actual common positive subset whenever the family contains all relevant
losses. No ideal-existence, dense-basis, normality, or partition conclusion
is asserted here.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosIdeal

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- Closure under unions of families that are countable inside the model.
The family and the injection witnessing countability are arbitrary names. -/
def countableClosure (I : bSet 𝔹) : 𝔹 :=
  ⨅ F : bSet 𝔹,
    _root_.imp (injects_into F bSet.omega ⊓ F ⊆ᴮ I) (bv_union F ∈ᴮ I)

theorem countable_union_small {I F : bSet 𝔹} {Γ : 𝔹}
    (Hclosure : Γ ≤ countableClosure I)
    (Hcountable : Γ ≤ injects_into F bSet.omega)
    (Hsmall : Γ ≤ F ⊆ᴮ I) : Γ ≤ bv_union F ∈ᴮ I :=
  (le_inf (Hclosure.trans (iInf_le _ F)) (le_inf Hcountable Hsmall)).trans bv_imp_elim

/-- The concrete remainder, not an assumed common-subset witness. -/
def commonRemainder (A F : bSet 𝔹) : bSet 𝔹 :=
  difference A (bv_union F)

theorem commonRemainder_subset {A F : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ commonRemainder A F ⊆ᴮ A :=
  difference_subset

theorem commonRemainder_positive {κ I A F : bSet 𝔹} {Γ : 𝔹}
    (HI : Γ ≤ isIdeal κ I)
    (Hclosure : Γ ≤ countableClosure I)
    (HA : Γ ≤ positive κ I A)
    (Hcountable : Γ ≤ injects_into F bSet.omega)
    (Hsmall : Γ ≤ F ⊆ᴮ I) :
    Γ ≤ positive κ I (commonRemainder A F) :=
  positive_difference_of_small HI HA (countable_union_small Hclosure Hcountable Hsmall)

/-- Every member of the loss family lies inside its internal union. -/
theorem loss_subset_union {F X : bSet 𝔹} {Γ : 𝔹}
    (HX : Γ ≤ X ∈ᴮ F) : Γ ≤ X ⊆ᴮ bv_union F :=
  (le_inf (le_top.trans ((bv_union_spec'' F).trans (iInf_le _ X))) HX).trans bv_imp_elim

/-- Removing the loss union leaves only points in every set whose loss
from the base is covered by that union. -/
theorem commonRemainder_subset_of_loss_subset {A F B : bSet 𝔹} {Γ : 𝔹}
    (Hloss : Γ ≤ difference A B ⊆ᴮ bv_union F) :
    Γ ≤ commonRemainder A F ⊆ᴮ B := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  have Hmem : Γ ⊓ (x ∈ᴮ commonRemainder A F) ≤
      (x ∈ᴮ A) ⊓ (x ∈ᴮ bv_union F)ᶜ := by
    change Γ ⊓ (x ∈ᴮ difference A (bv_union F)) ≤ _
    rw [mem_difference]
    exact inf_le_right
  have Hbad : (x ∈ᴮ B)ᶜ ⊓ (Γ ⊓ (x ∈ᴮ commonRemainder A F)) ≤ ⊥ := by
    have Hdiff : (x ∈ᴮ B)ᶜ ⊓ (Γ ⊓ (x ∈ᴮ commonRemainder A F)) ≤
        x ∈ᴮ difference A B := by
      rw [mem_difference]
      exact le_inf (inf_le_right.trans (Hmem.trans inf_le_left)) inf_le_left
    have Hunion : (x ∈ᴮ B)ᶜ ⊓ (Γ ⊓ (x ∈ᴮ commonRemainder A F)) ≤
        x ∈ᴮ bv_union F :=
      mem_of_mem_subset (inf_le_right.trans (inf_le_left.trans Hloss)) Hdiff
    exact (le_inf Hunion (inf_le_right.trans (Hmem.trans inf_le_right))).trans
      inf_compl_eq_bot.le
  have Hresult : Γ ⊓ (x ∈ᴮ commonRemainder A F) ≤ ((x ∈ᴮ B)ᶜ)ᶜ :=
    le_neg_of_inf_eq_bot (bot_unique Hbad)
  simpa only [compl_compl] using Hresult

theorem commonRemainder_subset_of_loss_mem {A F B : bSet 𝔹} {Γ : 𝔹}
    (Hloss : Γ ≤ difference A B ∈ᴮ F) :
    Γ ≤ commonRemainder A F ⊆ᴮ B :=
  commonRemainder_subset_of_loss_subset (loss_subset_union Hloss)

/-- The same concrete remainder is contained in every member of an
arbitrary internal family whose base losses belong to `F`. -/
theorem commonRemainder_common {A F T : bSet 𝔹} {Γ : 𝔹}
    (Hlosses : Γ ≤ ⨅ B : bSet 𝔹,
      _root_.imp (B ∈ᴮ T) (difference A B ∈ᴮ F)) :
    Γ ≤ ⨅ B : bSet 𝔹, _root_.imp (B ∈ᴮ T) (commonRemainder A F ⊆ᴮ B) := by
  apply le_iInf
  intro B
  rw [← deduction]
  apply commonRemainder_subset_of_loss_mem
  exact (le_inf (inf_le_left.trans (Hlosses.trans (iInf_le _ B))) inf_le_right).trans
    bv_imp_elim

/-- Internal countable common-basis loss removal, with the positive common
subset explicitly constructed from the base and the loss family. -/
theorem commonRemainder_positive_common {κ I A F T : bSet 𝔹} {Γ : 𝔹}
    (HI : Γ ≤ isIdeal κ I)
    (Hclosure : Γ ≤ countableClosure I)
    (HA : Γ ≤ positive κ I A)
    (Hcountable : Γ ≤ injects_into F bSet.omega)
    (Hsmall : Γ ≤ F ⊆ᴮ I)
    (Hlosses : Γ ≤ ⨅ B : bSet 𝔹,
      _root_.imp (B ∈ᴮ T) (difference A B ∈ᴮ F)) :
    Γ ≤ positive κ I (commonRemainder A F) ⊓
      ((commonRemainder A F ⊆ᴮ A) ⊓
        ⨅ B : bSet 𝔹, _root_.imp (B ∈ᴮ T) (commonRemainder A F ⊆ᴮ B)) :=
  le_inf (commonRemainder_positive HI Hclosure HA Hcountable Hsmall)
    (le_inf commonRemainder_subset (commonRemainder_common Hlosses))

end bSet.ErdosIdeal
