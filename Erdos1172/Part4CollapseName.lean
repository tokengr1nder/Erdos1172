/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4CollapseMatrix
public import Erdos1172.Part4CountableMatrixName

@[expose] public section

/-!
# An explicit collapse algebra and its surjection name

For every nonempty ground set A, the constructed algebra has a name
which it forces to be a surjection from internal omega onto check A.
Its principal conditions form a positive dense family of size at most
max(aleph0, the cardinality of the indexing type).

This is the countable-collapse algebra that occurs as an ideal quotient,
NOT a GCH-preserving model construction or a construction of an ideal.
In particular, it collapses old uncountable ground sets; those must not
be confused with the new model's internal uncountable ordinals.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch

universe u

namespace Erdos1172Collapse

open bSet bSet.ErdosCountableMatrix Erdos1172PosetCompletion

variable {α : Type u}

instance algebraNontrivialCompleteBooleanAlgebra :
    NontrivialCompleteBooleanAlgebra (Algebra α) where
  toCompleteBooleanAlgebra := inferInstance
  bot_lt_top := bot_lt_top

/-- An actual name, defined from the collapse matrix without an existence premise. -/
def collapseName (A : PSet.{u}) : bSet (Algebra A.Type) :=
  graph entry (fun a => check (A.Func a))

theorem collapseName_is_function (A : PSet.{u}) [Nonempty A.Type] :
    (⊤ : Algebra A.Type) ≤ is_function omega (check A) (collapseName A) := by
  rw [check_unfold]
  exact graph_is_function entry (fun a => check (A.Func a))
    (fun _ _ _ h => entry_inf_eq_bot h) row_iSup_eq_top

theorem collapseName_is_surj (A : PSet.{u}) :
    (⊤ : Algebra A.Type) ≤ is_surj omega (check A) (collapseName A) := by
  rw [check_unfold]
  exact graph_is_surj entry (fun a => check (A.Func a))
    (fun _ _ _ h => entry_inf_eq_bot h) column_iSup_eq_top

theorem collapseName_is_surjective_function (A : PSet.{u}) [Nonempty A.Type] :
    (⊤ : Algebra A.Type) ≤ is_function omega (check A) (collapseName A) ⊓
      is_surj omega (check A) (collapseName A) :=
  le_inf (collapseName_is_function A) (collapseName_is_surj A)

/-- The forcing assertion is proved for the actual constructed algebra. -/
theorem forces_countable_surjection (A : PSet.{u}) [Nonempty A.Type] :
    (⊤ : Algebra A.Type) ≤ surjects_onto omega (check A) :=
  le_iSup_of_le (collapseName A)
    (le_inf ((collapseName_is_function A).trans inf_le_left) (collapseName_is_surj A))

theorem condition_family_positive_dense :
    (∀ p : Condition α, condition p ≠ ⊥) ∧
      ∀ b : Algebra α, b ≠ ⊥ → ∃ p : Condition α, condition p ≤ b :=
  ⟨condition_ne_bot, fun _ => exists_condition_le⟩

theorem condition_family_cardinal [Infinite α] :
    Cardinal.mk (Condition α) = Cardinal.mk α := cardinal_eq_of_infinite

end Erdos1172Collapse
