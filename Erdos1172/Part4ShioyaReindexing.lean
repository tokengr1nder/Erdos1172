/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaProjectionRefinement

@[expose] public section

/-! # Transport of complete Boolean embeddings along a reindexing of the source -/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion
universe u
namespace Erdos1172Shioya.PartialProjection

variable {κ : Cardinal.{u}} {P Q R : Type u} [PartialOrder P] [PartialOrder Q] [PartialOrder R]

def isoProjection (e : R ≃o Q) : PartialProjection κ R Q := identity.precomposeIso e

theorem iso_condition (e : R ≃o Q) (r : R) (b : Completion Q) :
    condition r ≤ (isoProjection (κ := κ) e).booleanHom b ↔ condition (e r) ≤ b :=
  (isoProjection (κ := κ) e).dom_condition ⟨r,Set.mem_univ _⟩ b

theorem booleanHom_precomposeIso (π : PartialProjection κ Q P) (e : R ≃o Q) :
    (π.precomposeIso e).booleanHom = (isoProjection (κ := κ) e).booleanHom.comp π.booleanHom := by
  ext b
  let σ := π.precomposeIso e
  have hD (r : R) : ∃ x ∈ σ.dom, x ≤ r := by
    obtain ⟨x,hx⟩ := σ.dense r
    exact ⟨x.val,x.property,hx⟩
  have he (x : σ.dom) : condition x.val ≤ σ.booleanHom b ↔
      condition x.val ≤ (isoProjection (κ := κ) e).booleanHom (π.booleanHom b) :=
    (σ.dom_condition x b).trans (((iso_condition (κ := κ) e x.val (π.booleanHom b)).trans
      (π.dom_condition ⟨e x.val,x.property⟩ b)).symm)
  exact le_antisymm (le_of_dense_conditions_le σ.dom hD (fun x => (he x).mp))
    (le_of_dense_conditions_le σ.dom hD (fun x => (he x).mpr))

end Erdos1172Shioya.PartialProjection
