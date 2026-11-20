/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4PosetGenericFilter
public import Erdos1172.Part4LevyInitialSegmentProjection
public import Erdos1172.Part4LevyCollapseNames

@[expose] public section

/-!
# Restricting the generic filter on the larger Lévy collapse

The checked label of a smaller collapse condition belongs to the transported
generic exactly on the join of larger generic conditions whose actual
initial projections strengthen it.
-/

set_option autoImplicit false
noncomputable section
open scoped Flypitch Erdos1172LevyCollapse
universe u

namespace Erdos1172LevyCollapse

open bSet ErdosNameTransport Erdos1172PosetGeneric Erdos1172PosetCompletion

variable {κ θ : Cardinal.{u}}

def collapseGeneric (κ : Cardinal.{u}) : bSet (Completion (BelowCondition κ)) :=
  genericFilterName (Completion (BelowCondition κ))

theorem collapseGeneric_meets_dense (D : Set (BelowCondition κ))
    (hD : ∀ p, ∃ q ∈ D, q ≤ p) :
    (⊤ : Completion (BelowCondition κ)) ≤ ⨆ x : bSet (Completion (BelowCondition κ)),
      x ∈ᴮ check (PSet.mk D (fun p => genericLabel (positiveCondition p.val))) ⊓
      x ∈ᴮ collapseGeneric κ :=
  genericFilter_meets_dense D hD

theorem initial_collapseGeneric_restriction (h : κ ≤ θ) :
    mapNames (initialCollapseHom h) (collapseGeneric κ) =
      restrictedGenericName (initialCollapseHom h) (initialCollapseHom_injective h) :=
  map_genericFilterName (initialCollapseHom h) (initialCollapseHom_injective h)

theorem initial_collapseGeneric_condition (h : κ ≤ θ) (p : BelowCondition κ) :
    (check (genericLabel (positiveCondition p)) ∈ᴮ
      mapNames (initialCollapseHom h) (collapseGeneric κ)) =
    ⨆ q : {q : BelowCondition θ // initialProjection h q ≤ p},
      check (genericLabel (positiveCondition q.val)) ∈ᴮ collapseGeneric θ :=
  mapped_generic_condition_membership (initialProjection h) (initialProjection_exactLifts h) p

end Erdos1172LevyCollapse
