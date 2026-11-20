/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalHartogsInitial
public import Erdos1172.Part4InternalCardinalLanguage

@[expose] public section

/-!
Two concrete iterations of the internal Boolean-valued Hartogs construction.
These names satisfy the least-noninjecting-ordinal specifications over omega
and over its first Hartogs ordinal, respectively. No equality with a checked
ground-model omega-two, preservation theorem, GCH, or dense ideal is asserted.
-/

open Fol bSet

universe u

namespace bSet.ErdosOmegaTwo

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- The concrete internal first uncountable ordinal name. -/
noncomputable def omegaOne : bSet 𝔹 := ErdosHartogs.hartogs (κ := bSet.omega)

/-- The concrete successor Hartogs ordinal over the internal omega-one name. -/
noncomputable def omegaTwo : bSet 𝔹 := ErdosHartogs.hartogs (κ := omegaOne)

theorem one_injects_omega : (⊤ : 𝔹) ≤ injects_into (1 : bSet 𝔹) bSet.omega := by
  apply injects_into_of_subset
  exact of_nat_subset_omega (n := 1)

theorem omegaOne_Ord {Γ : 𝔹} : Γ ≤ Ord (omegaOne : bSet 𝔹) :=
  ErdosHartogs.hartogs_Ord (κ := bSet.omega) one_injects_omega

theorem omegaOne_spec {Γ : 𝔹} :
    Γ ≤ ErdosHartogs.leastNoninjectingOrdinal bSet.omega (omegaOne : bSet 𝔹) :=
  ErdosHartogs.hartogs_spec (κ := bSet.omega) one_injects_omega

theorem omegaOne_not_injects {Γ : 𝔹} :
    Γ ≤ (injects_into (omegaOne : bSet 𝔹) bSet.omega)ᶜ :=
  ErdosHartogs.hartogs_not_le_omega (κ := bSet.omega) one_injects_omega

theorem one_mem_omegaOne : (⊤ : 𝔹) ≤ (1 : bSet 𝔹) ∈ᴮ omegaOne := by
  apply (ErdosHartogs.mem_hartogs_iff₀ (κ := bSet.omega)).mpr
  exact le_sup_of_le_left (le_sup_of_le_right bv_refl)

theorem one_injects_omegaOne : (⊤ : 𝔹) ≤ injects_into (1 : bSet 𝔹) omegaOne := by
  apply injects_into_of_subset
  exact subset_of_mem_transitive (omegaOne_Ord.trans inf_le_right) one_mem_omegaOne

theorem omegaTwo_Ord {Γ : 𝔹} : Γ ≤ Ord (omegaTwo : bSet 𝔹) :=
  ErdosHartogs.hartogs_Ord (κ := omegaOne) one_injects_omegaOne

theorem omegaTwo_not_injects {Γ : 𝔹} :
    Γ ≤ (injects_into (omegaTwo : bSet 𝔹) omegaOne)ᶜ :=
  ErdosHartogs.hartogs_not_le_omega (κ := omegaOne) one_injects_omegaOne

theorem omegaOne_initial {Γ : 𝔹} :
    Γ ≤ ErdosHartogs.initialOrdinal (omegaOne : bSet 𝔹) :=
  ErdosHartogs.hartogs_initial (κ := bSet.omega) one_injects_omega

theorem omegaTwo_initial {Γ : 𝔹} :
    Γ ≤ ErdosHartogs.initialOrdinal (omegaTwo : bSet 𝔹) :=
  ErdosHartogs.hartogs_initial (κ := omegaOne) one_injects_omegaOne

theorem omega_mem_omegaOne {Γ : 𝔹} :
    Γ ≤ (bSet.omega : bSet 𝔹) ∈ᴮ omegaOne :=
  ErdosHartogs.base_mem_hartogs (κ := bSet.omega) one_injects_omega Ord_omega

theorem omegaOne_mem_omegaTwo {Γ : 𝔹} :
    Γ ≤ (omegaOne : bSet 𝔹) ∈ᴮ omegaTwo :=
  ErdosHartogs.base_mem_hartogs (κ := omegaOne) one_injects_omegaOne omegaOne_Ord

theorem omegaOne_member_injects {Γ : 𝔹} {η : bSet 𝔹}
    (Hmem : Γ ≤ η ∈ᴮ omegaOne) : Γ ≤ injects_into η bSet.omega := by
  apply injects_into_of_injection_into
  exact (ErdosHartogs.mem_hartogs_iff (κ := bSet.omega) one_injects_omega
    (ErdosHartogs.Ord_of_mem_hartogs (κ := bSet.omega) Hmem)).mp Hmem

theorem omegaTwo_member_injects {Γ : 𝔹} {η : bSet 𝔹}
    (Hmem : Γ ≤ η ∈ᴮ omegaTwo) : Γ ≤ injects_into η omegaOne := by
  apply injects_into_of_injection_into
  exact (ErdosHartogs.mem_hartogs_iff (κ := omegaOne) one_injects_omegaOne
    (ErdosHartogs.Ord_of_mem_hartogs (κ := omegaOne) Hmem)).mp Hmem

end bSet.ErdosOmegaTwo
