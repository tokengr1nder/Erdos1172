/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCountableSubsetCodes
public import Erdos1172.Part4InternalMixedProductInjection
public import Erdos1172.Part4InternalSmallFamilyUnion

@[expose] public section

/-!
# One small local step of a fixed internal selector

The local domain consists of pairs of whole internally countable subsets
of two omega-one-small pools. The same given selector is used on that
domain; weak total functionality allows it to have further graph support
elsewhere. Its local value image and the union of those values are small.

No bound on the selector's global image, closure hull, rank, or completed
fusion is asserted. The first coordinate retains whole object names;
neither membership witnesses nor the cardinal estimate replace them by
ordered histories or external enumerations.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCountableChoicePoolStep

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosCountableSubsetCodes ErdosSmallFamilyUnion
open ErdosCountableImage ErdosPartition

def choicePoolDomain (B P : bSet 𝔹) : bSet 𝔹 :=
  prod (countableSubsets B) (countableSubsets P)

def selectedObjects (κ B P F : bSet 𝔹) : bSet 𝔹 :=
  image (choicePoolDomain B P) (bv_powerset κ) F

def selectedPoints (κ B P F : bSet 𝔹) : bSet 𝔹 :=
  bv_union (selectedObjects κ B P F)

theorem mem_choicePoolDomain_iff {B P T U : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair T U ∈ᴮ choicePoolDomain B P ↔
      (Γ ≤ T ⊆ᴮ B ∧ Γ ≤ injects_into T bSet.omega) ∧
        (Γ ≤ U ⊆ᴮ P ∧ Γ ≤ injects_into U bSet.omega) := by
  change (Γ ≤ pair T U ∈ᴮ prod (countableSubsets B) (countableSubsets P)) ↔ _
  rw [mem_prod_iff, mem_countableSubsets_iff, mem_countableSubsets_iff]

theorem countableSubsets_mono {A B : bSet 𝔹} {Γ : 𝔹}
    (HAB : Γ ≤ A ⊆ᴮ B) : Γ ≤ countableSubsets A ⊆ᴮ countableSubsets B := by
  rw [subset_unfold']
  apply le_iInf
  intro T
  rw [← deduction]
  have HT := mem_countableSubsets_iff.mp
    (show Γ ⊓ T ∈ᴮ countableSubsets A ≤ T ∈ᴮ countableSubsets A from inf_le_right)
  exact mem_countableSubsets_iff.mpr ⟨subset_trans' HT.1 (inf_le_left.trans HAB), HT.2⟩

/-- The local pair domain is contained in the ambient pair domain. This
uses actual subset inclusion, not a cardinal identification of objects. -/
theorem choicePoolDomain_subset {B P K κ : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ B ⊆ᴮ K) (HP : Γ ≤ P ⊆ᴮ κ) :
    Γ ≤ choicePoolDomain B P ⊆ᴮ choicePoolDomain K κ := by
  rw [subset_unfold']
  apply le_iInf
  intro q
  rw [← deduction]
  obtain ⟨T, HT, U, HU, Hq⟩ := mem_prod_iff₂.mp
    (show Γ ⊓ q ∈ᴮ choicePoolDomain B P ≤
      q ∈ᴮ prod (countableSubsets B) (countableSubsets P) from inf_le_right)
  exact mem_prod_iff₂.mpr ⟨T,
    mem_of_mem_subset (countableSubsets_mono (inf_le_left.trans HB)) HT, U,
    mem_of_mem_subset (countableSubsets_mono (inf_le_left.trans HP)) HU, Hq⟩

/-- The entire local domain is small, including all mixed internally
countable subsets, not just externally displayed countable families. -/
theorem choicePoolDomain_injects_omegaOne {B P : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HB : Γ ≤ injects_into B omegaOne)
    (HP : Γ ≤ injects_into P omegaOne) :
    Γ ≤ injects_into (choicePoolDomain B P) omegaOne :=
  injects_into_trans
    (ErdosMixedProductInjection.injects_into_prod
      (countableSubsets_injects_omegaOne HCH HB)
      (countableSubsets_injects_omegaOne HCH HP))
    (ErdosCardinalSquare.omegaOne_square_injects HCH)

theorem selectedPoints_subset {κ B P F : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ selectedPoints κ B P F ⊆ᴮ κ := indexed_union_subset

theorem mem_selectedObjects_of_value {κ B P F T U A : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_func' (choicePoolDomain B P) (bv_powerset κ) F)
    (HT : Γ ≤ T ∈ᴮ countableSubsets B) (HU : Γ ≤ U ∈ᴮ countableSubsets P)
    (Hpair : Γ ≤ pair (pair T U) A ∈ᴮ F) :
    Γ ≤ A ∈ᴮ selectedObjects κ B P F :=
  mem_image Hpair (mem_prod HT HU) (value_mem_codomain HF (mem_prod HT HU) Hpair)

theorem selectedObject_subset_selectedPoints {κ B P F A : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ A ∈ᴮ selectedObjects κ B P F) :
    Γ ≤ A ⊆ᴮ selectedPoints κ B P F := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  exact mem_bv_union_iff.mpr (le_iSup_of_le A (le_inf (inf_le_left.trans HA) inf_le_right))

theorem selected_value_subset_selectedPoints {κ B P F T U A : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_func' (choicePoolDomain B P) (bv_powerset κ) F)
    (HT : Γ ≤ T ∈ᴮ countableSubsets B) (HU : Γ ≤ U ∈ᴮ countableSubsets P)
    (Hpair : Γ ≤ pair (pair T U) A ∈ᴮ F) :
    Γ ≤ A ⊆ᴮ selectedPoints κ B P F :=
  selectedObject_subset_selectedPoints (mem_selectedObjects_of_value HF HT HU Hpair)

/-- The fixed selector's local image is small. No smallness assertion is
made about its values on any larger ambient domain. -/
theorem selectedObjects_injects_omegaOne {κ B P F : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HB : Γ ≤ injects_into B omegaOne)
    (HP : Γ ≤ injects_into P omegaOne)
    (HF : Γ ≤ is_func' (choicePoolDomain B P) (bv_powerset κ) F) :
    Γ ≤ injects_into (selectedObjects κ B P F) omegaOne :=
  image_injects_into_ordinal HF (choicePoolDomain_injects_omegaOne HCH HB HP) omegaOne_Ord

/-- Guarded smallness of just the local selected values bounds their
actual point union. Weak functionality is enough for the image bound. -/
theorem selectedPoints_injects_omegaOne {κ B P F : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HB : Γ ≤ injects_into B omegaOne)
    (HP : Γ ≤ injects_into P omegaOne)
    (HF : Γ ≤ is_func' (choicePoolDomain B P) (bv_powerset κ) F)
    (Hvalues : Γ ≤ smallValues (choicePoolDomain B P) F) :
    Γ ≤ injects_into (selectedPoints κ B P F) omegaOne :=
  union_injects_omegaOne HCH (selectedObjects_injects_omegaOne HCH HB HP HF)
    (smallValues_image Hvalues)

theorem choice_pool_step_small {κ B P F : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HB : Γ ≤ injects_into B omegaOne)
    (HP : Γ ≤ injects_into P omegaOne)
    (HF : Γ ≤ is_func' (choicePoolDomain B P) (bv_powerset κ) F)
    (Hvalues : Γ ≤ smallValues (choicePoolDomain B P) F) :
    Γ ≤ injects_into (selectedObjects κ B P F) omegaOne ⊓
      injects_into (selectedPoints κ B P F) omegaOne :=
  le_inf (selectedObjects_injects_omegaOne HCH HB HP HF)
    (selectedPoints_injects_omegaOne HCH HB HP HF Hvalues)

end bSet.ErdosCountableChoicePoolStep
