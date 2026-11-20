/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyChainCondition
public import Erdos1172.Part4BooleanCardinalPreservation
public import Erdos1172.Part4LevyCollapseNames

@[expose] public section

/-!
# Ground-set noncollapse for the actual below-κ Boolean algebra

The chain condition in this file is proved for the concrete finite-support
forcing, not supplied as a hypothesis. For uncountable regular κ, no internal
surjection from a smaller checked indexing set onto a separated checked
target of size at least κ has positive Boolean value. The target cardinal
may be singular; no target-regularity premise is used.

This is an exact statement about checked ground sets and arbitrary internal
function names. It does not identify the new internal omegaOne, prove full
GCH, construct the anonymous iteration, or supply the required normal ideal.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch

universe u

namespace Erdos1172LevyCollapse

open bSet Erdos1172PosetCompletion

theorem below_small_domain_surjects_onto_eq_bot (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ)
    (X Y : PSet.{u}) (HX : Cardinal.mk X.Type < κ)
    (HY : κ ≤ Cardinal.mk Y.Type)
    (Hsep : ∀ i j : Y.Type, i ≠ j → ¬ PSet.Equiv (Y.Func i) (Y.Func j)) :
    (surjects_onto (check X) (check Y) : Completion (BelowCondition κ)) = ⊥ :=
  bSet.ErdosCardinalPreservation.surjects_onto_eq_bot Hκ
    (fun w hpos hdisj => below_completion_disjoint_family_cardinal_lt κ Hκ Hunc
      w hpos hdisj) X Y HX HY Hsep

/-- The actual algebra admits no such surjection, including when the smaller
ground domain itself already has cardinality at least κ. -/
theorem below_surjects_onto_eq_bot_of_cardinal_lt (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ)
    (X Y : PSet.{u}) (Hlt : Cardinal.mk X.Type < Cardinal.mk Y.Type)
    (HY : κ ≤ Cardinal.mk Y.Type)
    (Hsep : ∀ i j : Y.Type, i ≠ j → ¬ PSet.Equiv (Y.Func i) (Y.Func j)) :
    (surjects_onto (check X) (check Y) : Completion (BelowCondition κ)) = ⊥ :=
  bSet.ErdosCardinalPreservation.surjects_onto_eq_bot_of_cardinal_lt Hκ
    (fun w hpos hdisj => below_completion_disjoint_family_cardinal_lt κ Hκ Hunc
      w hpos hdisj) X Y Hlt HY Hsep

theorem not_forces_below_ground_surjection (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ)
    (X Y : PSet.{u}) (Hlt : Cardinal.mk X.Type < Cardinal.mk Y.Type)
    (HY : κ ≤ Cardinal.mk Y.Type)
    (Hsep : ∀ i j : Y.Type, i ≠ j → ¬ PSet.Equiv (Y.Func i) (Y.Func j))
    {Γ : Completion (BelowCondition κ)} (HΓ : Γ ≠ ⊥) :
    ¬ Γ ≤ surjects_onto (check X) (check Y) := by
  rw [below_surjects_onto_eq_bot_of_cardinal_lt κ Hκ Hunc X Y Hlt HY Hsep]
  exact fun h => HΓ (bot_unique h)

end Erdos1172LevyCollapse
