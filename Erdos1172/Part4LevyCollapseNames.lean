/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyCoordinateProjection
public import Erdos1172.Part4CountableMatrixName

@[expose] public section

/-!
# Actual coordinate collapse names in the dependent product completion

For a family of ground pre-sets, each selected nonempty coordinate has an
actual name for a surjection from internal omega onto its checked ground set.
The graph is formed by mixing the coordinate matrix rows and using the
accepted graph construction on internal omega, so its function and surjection
laws quantify over arbitrary internal names, not just ground representatives.

The algebra and names remain defined for empty alphabets. Surjectivity onto
an empty coordinate is vacuous; totality is asserted only when that coordinate
is nonempty. No preservation of the upper cardinal or GCH is claimed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch Erdos1172LevyCollapse

universe u

namespace Erdos1172LevyCollapse

open bSet bSet.ErdosCountableMatrix Erdos1172PosetCompletion

variable {I : Type u}

instance productCompletionNontrivialCompleteBooleanAlgebra (A : I → Type u) :
    NontrivialCompleteBooleanAlgebra (Completion (ProductCondition A)) where
  toCompleteBooleanAlgebra := inferInstance
  bot_lt_top := bot_lt_top

/-- The concrete graph name for one coordinate of the finite-support product. -/
def coordinateCollapseName (F : I → PSet.{u}) (i : I) :
    bSet (Completion (ProductCondition (fun j => (F j).Type))) :=
  graph (coordinateEntry (A := fun j => (F j).Type) i)
    (fun a => check ((F i).Func a))

theorem coordinateCollapseName_is_function (F : I → PSet.{u}) (i : I)
    [Nonempty (F i).Type] :
    (⊤ : Completion (ProductCondition (fun j => (F j).Type))) ≤
      is_function omega (check (F i)) (coordinateCollapseName F i) := by
  rw [check_unfold]
  exact graph_is_function (coordinateEntry (A := fun j => (F j).Type) i)
    (fun a => check ((F i).Func a))
    (fun _ _ _ h => coordinateEntry_inf_eq_bot h)
    (coordinateEntry_row_iSup_eq_top (A := fun j => (F j).Type) i)

theorem coordinateCollapseName_is_surj (F : I → PSet.{u}) (i : I) :
    (⊤ : Completion (ProductCondition (fun j => (F j).Type))) ≤
      is_surj omega (check (F i)) (coordinateCollapseName F i) := by
  rw [check_unfold]
  exact graph_is_surj (coordinateEntry (A := fun j => (F j).Type) i)
    (fun a => check ((F i).Func a))
    (fun _ _ _ h => coordinateEntry_inf_eq_bot h)
    (coordinateEntry_column_iSup_eq_top (A := fun j => (F j).Type) i)

theorem coordinateCollapseName_is_surjective_function (F : I → PSet.{u}) (i : I)
    [Nonempty (F i).Type] :
    (⊤ : Completion (ProductCondition (fun j => (F j).Type))) ≤
      is_function omega (check (F i)) (coordinateCollapseName F i) ⊓
        is_surj omega (check (F i)) (coordinateCollapseName F i) :=
  le_inf (coordinateCollapseName_is_function F i) (coordinateCollapseName_is_surj F i)

/-- Matrix weights really force the corresponding pairs into the actual graph. -/
theorem coordinateCollapseName_pair_of_entry (F : I → PSet.{u}) (i : I)
    (n : ℕ) (a : (F i).Type) :
    coordinateEntry (A := fun j => (F j).Type) i n a ≤
      pair (of_nat n) (check ((F i).Func a)) ∈ᴮ coordinateCollapseName F i :=
  graph_pair_of_weight (coordinateEntry (A := fun j => (F j).Type) i)
    (fun a => check ((F i).Func a))
    (fun _ _ _ h => coordinateEntry_inf_eq_bot h) n a

/-- The constructed completion forces this coordinate's ground set countable,
using the displayed graph name rather than an assumed function witness. -/
theorem forces_coordinate_countable_surjection (F : I → PSet.{u}) (i : I)
    [Nonempty (F i).Type] :
    (⊤ : Completion (ProductCondition (fun j => (F j).Type))) ≤
      surjects_onto omega (check (F i)) :=
  le_iSup_of_le (coordinateCollapseName F i)
    (le_inf ((coordinateCollapseName_is_function F i).trans inf_le_left)
      (coordinateCollapseName_is_surj F i))

end Erdos1172LevyCollapse
