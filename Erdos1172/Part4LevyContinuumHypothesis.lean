/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4CompletionAntichainRepresentation
public import Erdos1172.Part4LevyConditionCardinality
public import Erdos1172.Part4SmallSubsetCardinality
public import Erdos1172.Part4GroundIndexNameBound
public import Erdos1172.Part4LevyOmegaOne

@[expose] public section

/-!
# CH in the actual below-inaccessible collapse

Small antichains of actual conditions code all Boolean values. Inaccessibility
bounds both those codes and all countable sequences of Boolean coefficients.
The weighted ground-label construction then bounds the internal powerset of
omega by checked κ, already proved equal to the new internal omega-one.
This proves CH in this algebra, not full GCH or the required normal ideal.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch

universe u

namespace Erdos1172LevyCollapse

open bSet Erdos1172PosetCompletion Erdos1172SmallSubsetCardinality

theorem below_completion_cardinal_le (κ : Cardinal.{u}) (Hκ : κ.IsInaccessible) :
    Cardinal.mk (Completion (BelowCondition κ)) ≤ κ :=
  (completion_cardinal_le_small_subsets κ
    (below_completion_disjoint_family_cardinal_lt κ Hκ.isRegular Hκ.aleph0_lt)).trans
      (small_subsets_cardinal_le κ Hκ (belowCondition_cardinal_le κ Hκ.aleph0_lt))

theorem below_boolean_sequences_cardinal_le (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) :
    Cardinal.mk (ℕ → Completion (BelowCondition κ)) ≤ κ :=
  nat_function_cardinal_le κ Hκ (below_completion_cardinal_le κ Hκ)

theorem below_real_name_indices_cardinal_le (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) :
    Cardinal.mk ((omega : bSet (Completion (BelowCondition κ))).type →
      Completion (BelowCondition κ)) ≤ κ := by
  have Hinj : Function.Injective
      (fun f : ULift.{u} ℕ → Completion (BelowCondition κ) => fun n : ℕ => f ⟨n⟩) := by
    intro f g Hfg
    funext n
    exact congrFun Hfg n.down
  exact (Cardinal.mk_le_of_injective Hinj).trans (below_boolean_sequences_cardinal_le κ Hκ)

theorem below_powerset_omega_injects_checked_upper (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) :
    (⊤ : Completion (BelowCondition κ)) ≤
      injects_into (bv_powerset omega) (check (PSet.ordinalMk κ.ord)) :=
  ErdosGroundIndexNameBound.powerset_injects_checked_cardinal_of_index_cardinal_le
    κ omega (below_real_name_indices_cardinal_le κ Hκ)

theorem below_powerset_omega_injects_omegaOne (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) :
    (⊤ : Completion (BelowCondition κ)) ≤ injects_into (bv_powerset omega) ErdosOmegaTwo.omegaOne :=
  bv_rw'' (below_checked_upper_eq_omegaOne κ Hκ.isRegular Hκ.aleph0_lt)
    (below_powerset_omega_injects_checked_upper κ Hκ) B_ext_injects_into_right

/-- CH is derived from the actual forcing construction and inaccessibility;
it is not supplied as a premise. This does not assert full GCH. -/
theorem below_forces_CH (κ : Cardinal.{u}) (Hκ : κ.IsInaccessible) :
    (⊤ : Completion (BelowCondition κ)) ≤ CH :=
  ErdosCHHartogs.CH_iff_powerset_omega_injects_omegaOne.mpr
    (below_powerset_omega_injects_omegaOne κ Hκ)

end Erdos1172LevyCollapse
