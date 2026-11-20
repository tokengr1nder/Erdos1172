/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalBlockSelectorPool

@[expose] public section

/-!
# Unconditional congruence of local block-pool operations

Equality of the two internal input pools preserves the entire countable
history domain, the fixed selector's bounded value image, its point
union, and its successful-object filter. All comparisons retain the same
selector and the same color/relation. No validity, functionality,
smallness, or successful-run premise is used for these set identities.

The existing unconditional support lemmas are reused: even an arbitrary
bounded image has its point union inside omega-two, and filtering by block
membership puts successful objects inside the actual block family.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosBlockPoolCongruence

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosCanonicalBlocks ErdosCountableSubsetCodes
open ErdosCountableChoicePoolStep ErdosBlockSelectorPool

theorem countableSubsets_congr :
    B_congr (countableSubsets : bSet 𝔹 → bSet 𝔹) := by
  intro A B Γ H
  exact B_congr_comprehend (ϕ := fun T => injects_into T bSet.omega)
    (H_congr := B_ext_injects_into_left) (bv_powerset_congr H)

/-- Two-variable congruence; either one-variable version follows by
using reflexive equality for the other pool. -/
theorem choicePoolDomain_congr {B₁ B₂ P₁ P₂ : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ B₁ =ᴮ B₂) (HP : Γ ≤ P₁ =ᴮ P₂) :
    Γ ≤ choicePoolDomain B₁ P₁ =ᴮ choicePoolDomain B₂ P₂ :=
  prod_congr (countableSubsets_congr HB) (countableSubsets_congr HP)

theorem selectedObjects_congr {κ F B₁ B₂ P₁ P₂ : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ B₁ =ᴮ B₂) (HP : Γ ≤ P₁ =ᴮ P₂) :
    Γ ≤ selectedObjects κ B₁ P₁ F =ᴮ selectedObjects κ B₂ P₂ F :=
  B_congr_image_left (choicePoolDomain_congr HB HP)

theorem selectedPoints_congr {κ F B₁ B₂ P₁ P₂ : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ B₁ =ᴮ B₂) (HP : Γ ≤ P₁ =ᴮ P₂) :
    Γ ≤ selectedPoints κ B₁ P₁ F =ᴮ selectedPoints κ B₂ P₂ F :=
  B_congr_bv_union (selectedObjects_congr HB HP)

theorem successfulObjects_congr
    {color : Bool} {R F B₁ B₂ P₁ P₂ : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ B₁ =ᴮ B₂) (HP : Γ ≤ P₁ =ᴮ P₂) :
    Γ ≤ successfulObjects color R B₁ P₁ F =ᴮ successfulObjects color R B₂ P₂ F :=
  B_congr_comprehend (ϕ := fun A => A ∈ᴮ blockObjects color R)
    (H_congr := B_ext_mem_left) (selectedObjects_congr HB HP)

end bSet.ErdosBlockPoolCongruence
