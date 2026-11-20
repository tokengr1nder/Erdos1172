/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalIdealSemantics
public import Erdos1172.Part4InternalCardinalDichotomy

@[expose] public section

/-!
# Countable absorption and the size of positive sets

Countable absorption means that every internally countable subset of the
base belongs to the ideal. It is distinct from closure under countable
unions of ideal members. The checked internal cardinal dichotomy proves
that a positive subset of omega-one has a full omega-one injection when
countable absorption holds. No CH, normality, or properness assumption is
needed for this implication.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosIdeal

open ErdosOmegaTwo

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- All arbitrary-name internally countable subsets of the base are small. -/
def countableAbsorption (κ J : bSet 𝔹) : 𝔹 :=
  ⨅ A : bSet 𝔹,
    _root_.imp (A ⊆ᴮ κ ⊓ injects_into A bSet.omega) (A ∈ᴮ J)

theorem countableAbsorption_apply {κ J A : bSet 𝔹} {Γ : 𝔹}
    (Habsorb : Γ ≤ countableAbsorption κ J)
    (Hsub : Γ ≤ A ⊆ᴮ κ) (Hcount : Γ ≤ injects_into A bSet.omega) :
    Γ ≤ A ∈ᴮ J :=
  (le_inf (Habsorb.trans (iInf_le _ A)) (le_inf Hsub Hcount)).trans bv_imp_elim

/-- A countable subset of another internally countable set is absorbed
as soon as it also lies inside the ideal's base. -/
theorem countableAbsorption_subset {κ J A T : bSet 𝔹} {Γ : 𝔹}
    (Habsorb : Γ ≤ countableAbsorption κ J) (Hsub : Γ ≤ A ⊆ᴮ κ)
    (HAT : Γ ≤ A ⊆ᴮ T) (HT : Γ ≤ injects_into T bSet.omega) :
    Γ ≤ A ∈ᴮ J :=
  countableAbsorption_apply Habsorb Hsub
    (injects_into_trans (injects_into_of_subset HAT) HT)

/-- In particular, every subset with a finite ordinal injection is small. -/
theorem small_of_injects_into_finite {κ J A : bSet 𝔹} {Γ : 𝔹} {n : ℕ}
    (Habsorb : Γ ≤ countableAbsorption κ J) (Hsub : Γ ≤ A ⊆ᴮ κ)
    (Hfinite : Γ ≤ injects_into A (bSet.of_nat n)) : Γ ≤ A ∈ᴮ J :=
  countableAbsorption_apply Habsorb Hsub
    (injects_into_trans Hfinite (injects_into_of_subset of_nat_subset_omega))

/-- Positivity and countable absorption rule out internal countability. -/
theorem positive_not_countable {κ J A : bSet 𝔹} {Γ : 𝔹}
    (Habsorb : Γ ≤ countableAbsorption κ J) (HA : Γ ≤ positive κ J A) :
    Γ ≤ (injects_into A bSet.omega)ᶜ := by
  rw [← imp_bot, ← deduction]
  exact bv_absurd _
    (countableAbsorption_apply (inf_le_left.trans Habsorb)
      (inf_le_left.trans (HA.trans inf_le_left)) inf_le_right)
    (inf_le_left.trans (HA.trans inf_le_right))

/-- The countable branch of the actual internal omega-one dichotomy is
impossible for a positive set, leaving an omega-one injection into it. -/
theorem omegaOne_injects_positive {J A : bSet 𝔹} {Γ : 𝔹}
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (HA : Γ ≤ positive omegaOne J A) : Γ ≤ injects_into omegaOne A := by
  have Hnot := positive_not_countable Habsorb HA
  apply (le_inf (le_refl Γ)
    (ErdosPartialInjection.omegaOne_cardinal_dichotomy (S := A) (Γ := Γ))).trans
  rw [inf_sup_left]
  apply sup_le
  · exact (bv_absurd _ inf_le_right (inf_le_left.trans Hnot)).trans bot_le
  · exact inf_le_right

/-- Both injections are explicit consequences: one from being a subset
of omega-one and the other from countable absorption and positivity. -/
theorem positive_omegaOne_injections {J A : bSet 𝔹} {Γ : 𝔹}
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (HA : Γ ≤ positive omegaOne J A) :
    Γ ≤ injects_into A omegaOne ⊓ injects_into omegaOne A :=
  le_inf (injects_into_of_subset (HA.trans inf_le_left))
    (omegaOne_injects_positive Habsorb HA)

end bSet.ErdosIdeal
