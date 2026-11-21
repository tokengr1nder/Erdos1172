/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalLargeDifference
public import Erdos1172.Part4InternalSimultaneousRowChoice

@[expose] public section

/-!
An explicitly supplied proper countably closed ideal absorbing countable
sets proves internal countable boundedness of omega-one. This is a
conditional internal regularity ingredient for later club constructions,
not an appeal to regularity of ground-model ordinal representatives.
The existing row-ideal hypotheses already supply a suitable ideal.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosOmegaOneIdealBounded

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosCountablePast ErdosColargeIntersection
open ErdosCountableImage ErdosSimultaneousRowChoice

theorem exists_bound_of_countable
    {J A : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (HA : Γ ≤ A ⊆ᴮ omegaOne) (Hcount : Γ ≤ injects_into A bSet.omega) :
    ∃ b : bSet 𝔹, Γ ≤ b ∈ᴮ omegaOne ⊓ A ⊆ᴮ b := by
  have Hsmall := past_small (HJ.trans inf_le_left) Habsorb Hclosure HA Hcount
  have Hpositive := positive_difference_of_small (HJ.trans inf_le_left)
    (base_positive_of_properIdeal HJ) Hsmall
  obtain ⟨b, Hb⟩ := exists_mem_of_positive (HJ.trans inf_le_left) Hpositive
  have Hparts : Γ ≤ b ∈ᴮ omegaOne ⊓ (b ∈ᴮ past A)ᶜ := by
    simpa only [mem_difference] using Hb
  refine ⟨b, le_inf (Hparts.trans inf_le_left) ?_⟩
  rw [subset_unfold']
  exact above_past HA (Hparts.trans inf_le_left) (Hparts.trans inf_le_right)

def countablyBounded (κ : bSet 𝔹) : 𝔹 :=
  ⨅ A, _root_.imp (A ⊆ᴮ κ ⊓ injects_into A bSet.omega)
    (⨆ b, b ∈ᴮ κ ⊓ A ⊆ᴮ b)

theorem countablyBounded_of_ideal {J : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J) : Γ ≤ countablyBounded omegaOne := by
  apply le_iInf
  intro A
  rw [← deduction]
  obtain ⟨b, Hb⟩ := exists_bound_of_countable (inf_le_left.trans HJ)
    (inf_le_left.trans Habsorb) (inf_le_left.trans Hclosure)
    (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)
  exact le_iSup_of_le b Hb

/-- One internally available row ideal suffices. No externally coherent
choice of the ideals, no CH and no normality are required. -/
theorem countablyBounded_of_rowIdeals {S : bSet 𝔹} {Γ : 𝔹}
    (Hrows : Γ ≤ ⨅ σ, _root_.imp (σ ∈ᴮ omegaOne) (⨆ J, rowIdealData S σ J)) :
    Γ ≤ countablyBounded omegaOne := by
  have Hex : Γ ≤ ⨆ J, rowIdealData S (0 : bSet 𝔹) J :=
    (le_inf (Hrows.trans (iInf_le _ (0 : bSet 𝔹)))
      ErdosLargeDifference.zero_mem_omegaOne).trans bv_imp_elim
  apply (le_inf (le_refl Γ) Hex).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro J
  have Hdata : Γ ⊓ rowIdealData S (0 : bSet 𝔹) J ≤ rowIdealData S (0 : bSet 𝔹) J := inf_le_right
  exact countablyBounded_of_ideal (Hdata.trans inf_le_left)
    (Hdata.trans (inf_le_right.trans inf_le_left))
    (Hdata.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))

end bSet.ErdosOmegaOneIdealBounded
