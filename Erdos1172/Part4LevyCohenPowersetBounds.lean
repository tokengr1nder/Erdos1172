/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyCohenDensePresentation
public import Erdos1172.Part4GroundIndexNameBound
public import Mathlib.SetTheory.Cardinal.Arithmetic

@[expose] public section

/-!
# Powerset upper bounds in the actual Levy--Cohen iteration

The completed iteration has cardinality at most `2^κ`, not necessarily κ.
Nevertheless, for every ground cardinal μ ≥ κ, all Boolean coefficient
functions on a type of size at most μ number at most `2^μ`. The calculation
uses `(2^κ)^μ = 2^(κ*μ) = 2^μ` and does not require μ to be regular.

A ground GCH equation at μ then gives an actual internal injection from
the full powerset of checked μ into checked μ⁺. All mixed subset names are
covered. No identification of that checked successor with an internal
Hartogs successor, full internal GCH, or ideal construction is asserted.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch

universe u

namespace Erdos1172LevyCohen

open bSet

/-- Count all Boolean coefficient functions in the actual second-stage
algebra, including when the upper ground cardinal is singular. -/
theorem coefficients_cardinal_le_two_power (κ μ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) (Hκμ : κ ≤ μ)
    {I : Type u} (HI : Cardinal.mk I ≤ μ) :
    Cardinal.mk (I → Algebra κ) ≤ 2 ^ μ := by
  have Hμ : Cardinal.aleph0 ≤ μ := Hκ.aleph0_lt.le.trans Hκμ
  have Hpow : (2 : Cardinal.{u}) ^ κ ≠ 0 :=
    ne_of_gt (lt_of_le_of_lt bot_le (Cardinal.cantor κ))
  calc
    Cardinal.mk (I → Algebra κ) =
        Cardinal.mk (Algebra κ) ^ Cardinal.mk I :=
      (Cardinal.power_def (Algebra κ) I).symm
    _ ≤ (2 ^ κ) ^ Cardinal.mk I :=
      Cardinal.power_le_power_right (completion_cardinal_le_two_power κ Hκ)
    _ ≤ (2 ^ κ) ^ μ := Cardinal.power_le_power_left Hpow HI
    _ = 2 ^ (κ * μ) := Cardinal.power_mul.symm
    _ = 2 ^ μ := by
      rw [Cardinal.mul_eq_right Hμ Hκμ Hκ.ne_zero]

/-- Bound the full coefficient index type of the powerset of checked μ.
Only the host GCH equation at this particular μ is used. -/
theorem checked_powerset_indices_cardinal_le (κ μ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) (Hκμ : κ ≤ μ)
    (HGCHμ : (2 : Cardinal.{u}) ^ μ = Order.succ μ) :
    Cardinal.mk ((check (PSet.ordinalMk μ.ord) : bSet (Algebra κ)).type →
      Algebra κ) ≤ Order.succ μ := by
  have HI : Cardinal.mk
      ((check (PSet.ordinalMk μ.ord) : bSet (Algebra κ)).type) ≤ μ := by
    rw [check_type', PSet.ordinalMk_type, Cardinal.mk_ord_toType]
  exact (coefficients_cardinal_le_two_power κ μ Hκ Hκμ HI).trans_eq HGCHμ

/-- The full internal powerset injects into the checked ground successor.
The target is deliberately not renamed as an internal successor cardinal. -/
theorem checked_powerset_injects_successor (κ μ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) (Hκμ : κ ≤ μ)
    (HGCHμ : (2 : Cardinal.{u}) ^ μ = Order.succ μ) :
    (⊤ : Algebra κ) ≤
      injects_into (bv_powerset (check (PSet.ordinalMk μ.ord)))
        (check (PSet.ordinalMk (Order.succ μ).ord)) :=
  ErdosGroundIndexNameBound.powerset_injects_checked_cardinal_of_index_cardinal_le
    (Order.succ μ) (check (PSet.ordinalMk μ.ord))
    (checked_powerset_indices_cardinal_le κ μ Hκ Hκμ HGCHμ)

end Erdos1172LevyCohen
