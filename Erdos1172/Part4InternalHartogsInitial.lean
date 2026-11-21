/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalHartogs

@[expose] public section

/-!
# Initiality and successor properties of the internal Hartogs name

The predicates and quantifiers below concern Boolean-valued set names. An
initial ordinal does not inject into any of its strict predecessors. This
is independent of the upstream `bSet.Card` definition.

The Hartogs construction assumes that one injects into its base, as required
by its unconditional insertion of zero and one. Its initiality is derived
from the proved membership characterization and noninjection theorem; it is
not an additional hypothesis. For an ordinal base the resulting initial
ordinal is strictly above that base and is least among initial ordinals
strictly above it.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosHartogs

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- An ordinal admitting no injection into any strict predecessor. -/
def initialOrdinal (α : bSet 𝔹) : 𝔹 :=
  Ord α ⊓ ⨅ γ, _root_.imp (γ ∈ᴮ α) (injects_into α γ)ᶜ

lemma Ord_of_initialOrdinal {α : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ initialOrdinal α) : Γ ≤ Ord α :=
  H.trans inf_le_left

lemma not_injects_of_initialOrdinal {α γ : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ initialOrdinal α) (Hmem : Γ ≤ γ ∈ᴮ α) :
    Γ ≤ (injects_into α γ)ᶜ := by
  have Himp : Γ ≤ _root_.imp (γ ∈ᴮ α) (injects_into α γ)ᶜ :=
    (H.trans inf_le_right).trans (iInf_le _ γ)
  exact (le_inf Himp Hmem).trans bv_imp_elim

/-- The constructed Hartogs name is an initial ordinal, not merely an
ordinal whose size happens to exceed the base. -/
lemma hartogs_initial {κ : bSet 𝔹}
    (Hone : (⊤ : 𝔹) ≤ injects_into (1 : bSet 𝔹) κ) {Γ : 𝔹} :
    Γ ≤ initialOrdinal (hartogs (κ := κ)) := by
  refine le_inf (hartogs_Ord Hone) ?_
  apply le_iInf
  intro γ
  rw [← deduction, ← imp_bot, ← deduction]
  have Hmem : (Γ ⊓ γ ∈ᴮ hartogs (κ := κ)) ⊓
      injects_into (hartogs (κ := κ)) γ ≤ γ ∈ᴮ hartogs (κ := κ) :=
    inf_le_left.trans inf_le_right
  have Hsmall := injects_into_of_injection_into
    ((mem_hartogs_iff Hone (Ord_of_mem_hartogs Hmem)).mp Hmem)
  exact bv_absurd _ (injects_into_trans inf_le_right Hsmall) (hartogs_not_le_omega Hone)

/-- For an ordinal base, the Hartogs name is strictly above that base. -/
lemma base_mem_hartogs {κ : bSet 𝔹}
    (Hone : (⊤ : 𝔹) ≤ injects_into (1 : bSet 𝔹) κ) {Γ : 𝔹}
    (HOrdκ : Γ ≤ Ord κ) : Γ ≤ κ ∈ᴮ hartogs (κ := κ) := by
  apply (mem_hartogs_iff Hone HOrdκ).mpr
  exact injection_into_of_injects_into injects_into_refl

end bSet.ErdosHartogs
