/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalClosedPoolFuture

@[expose] public section

/-!
# Actual enumeration, selector, closed pools and common future

The enumeration is chosen first, then the selector for that enumeration
and the original future. The closed pools belong to this exact selector.
Only after these choices is a common large future constructed for all
whole objects in the pool. All witnesses satisfy their laws at the same
Boolean condition, including for mixed or empty object pools.

The selector continues to refer to the original future `S`, not the
subsequently retained future `Y`. Its empty failure value is not asserted
to disappear. No successful ordered fusion, terminal, normality, ideal
existence or model-consistency conclusion is assumed or proved here.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionPreparation

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosIdeal ErdosDenseBasis ErdosCanonicalBlocks
open ErdosBlockSelector ErdosCountableChoicePoolStep ErdosClosedSelectorHull
open ErdosClosedPoolFuture ErdosOmegaOneIdealBounded

def fusionPreparationData
    (color : Bool) (R J S E F B P Y : bSet 𝔹) : 𝔹 :=
  (is_function (blockObjects color R) blockEnumerationCodes E ⊓
    blockEnumerationFamilyLaw color R E) ⊓
  (is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F ⊓
    (blockSelectorLaw color R J E S F ⊓
      (closedHullData color R F B P ⊓
        (Y ⊆ᴮ S ⊓ (injects_into omegaTwo Y ⊓
          ((⨅ y, _root_.imp (y ∈ᴮ Y) (P ∈ᴮ y)) ⊓
            poolSeedLaw color R J E B Y))))))

/-- Complete the preparation without changing either previously fixed
graph. Properness supplies countable boundedness of omega-one; normality
is not required. Both target exclusions remain explicit hypotheses. -/
theorem exists_fusion_preparation_for_selector
    {color : Bool} {R J I D S E F : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HJ : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (HD : Γ ≤ is_function I (bv_powerset omegaOne) D)
    (HDpos : Γ ≤ positiveValues omegaOne J I D)
    (Hdense : Γ ≤ denseValues omegaOne J I D)
    (HI : Γ ≤ injects_into I omegaOne)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (Hno : Γ ≤ (hasTwoBlock color R omegaOne bSet.omega omegaTwo)ᶜ)
    (HnoOpp : Γ ≤ (hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo)ᶜ)
    (HS : Γ ≤ S ⊆ᴮ omegaTwo) (HSlarge : Γ ≤ injects_into omegaTwo S) :
    ∃ B P Y : bSet 𝔹, Γ ≤ fusionPreparationData color R J S E F B P Y := by
  obtain ⟨B, P, Hpool⟩ := exists_closed_pool_for_selector HCH
    (countablyBounded_of_ideal HJ Habsorb Hclosure) HF Hlaw
  obtain ⟨Y, HY⟩ := exists_large_closed_pool_future HCH Habsorb
    (HJ.trans inf_le_left) Hclosure HD HDpos Hdense HI HE HElaw Hpool Hno HnoOpp HS HSlarge
  exact ⟨B, P, Y, le_inf (le_inf HE HElaw) (le_inf HF (le_inf Hlaw (le_inf Hpool HY)))⟩

/-- Construct the enumeration, then its selector, then the selector's
closed whole-object/point pools and a simultaneous large future. All
data use the same original `R`, `J`, `S`, and the same chosen `E`, `F`. -/
theorem exists_fusion_preparation
    {color : Bool} {R J I D S : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HJ : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (HD : Γ ≤ is_function I (bv_powerset omegaOne) D)
    (HDpos : Γ ≤ positiveValues omegaOne J I D)
    (Hdense : Γ ≤ denseValues omegaOne J I D)
    (HI : Γ ≤ injects_into I omegaOne)
    (Hno : Γ ≤ (hasTwoBlock color R omegaOne bSet.omega omegaTwo)ᶜ)
    (HnoOpp : Γ ≤ (hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo)ᶜ)
    (HS : Γ ≤ S ⊆ᴮ omegaTwo) (HSlarge : Γ ≤ injects_into omegaTwo S) :
    ∃ E F B P Y : bSet 𝔹, Γ ≤ fusionPreparationData color R J S E F B P Y := by
  obtain ⟨E, HE⟩ := exists_block_enumeration_family color R (Γ := Γ)
  obtain ⟨F, HF⟩ := exists_block_selector color R J E S (Γ := Γ)
  obtain ⟨B, P, Y, Hdata⟩ := exists_fusion_preparation_for_selector
    HCH HJ Habsorb Hclosure HD HDpos Hdense HI
    (HE.trans inf_le_left) (HE.trans inf_le_right)
    (HF.trans inf_le_left) (HF.trans inf_le_right) Hno HnoOpp HS HSlarge
  exact ⟨E, F, B, P, Y, Hdata⟩

end bSet.ErdosFusionPreparation
