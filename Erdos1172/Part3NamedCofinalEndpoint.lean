/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3RegularMembership

@[expose] public section

/-!
# Least possible strict upper bounds of regular names

Strict upper bounds quantify over actual members at every strengthening.
This predicate is itself regular. Among bounds attainable below a fixed
condition, well-foundedness selects the least one and a condition attaining
it. Minimality makes actual members densely cofinal strictly below that
endpoint. The cofinal witness is allowed to equal the test point, which is
essential for successor endpoints. No closure or generic-model assumption
is used.
-/

open Set

namespace Erdos1172Part3NamedCofinalEndpoint

open Erdos1172Part3RegularMembership

variable {P V : Type} [Preorder P] [LinearOrder V]

/-- A strict upper bound for every actual member below the condition. -/
def Upper (U : RegularName P V) (p : P) (y : V) : Prop :=
  ∀ q : P, q ≤ p → ∀ x : V, U.holds q x → x < y

theorem upper_persistent {U : RegularName P V} {p q : P} {y : V}
    (hqp : q ≤ p) (h : Upper U p y) : Upper U q y :=
  fun r hrq x hx => h r (hrq.trans hqp) x hx

/-- Actual members occur arbitrarily high strictly below the endpoint,
densely below every strengthening. Equality with the test point is allowed. -/
def CofinalBelow (U : RegularName P V) (p : P) (y : V) : Prop :=
  ∀ r : P, r ≤ p → ∀ z : V, z < y →
    ∃ s : P, s ≤ r ∧ ∃ x : V, U.holds s x ∧ z ≤ x ∧ x < y

theorem cofinalBelow_persistent {U : RegularName P V} {p q : P} {y : V}
    (hqp : q ≤ p) (h : CofinalBelow U p y) : CofinalBelow U q y :=
  fun r hrq z hzy => h r (hrq.trans hqp) z hzy

/-- If a smaller test point could bound a stronger cone, the displayed
endpoint would not be the least possible bound below the original cone. -/
theorem cofinalBelow_of_least_possible_upper
    (U : RegularName P V) (p0 q : P) (y : V)
    (hqp0 : q ≤ p0) (hy : Upper U q y)
    (hmin : ∀ z : V, (∃ r : P, r ≤ p0 ∧ Upper U r z) → y ≤ z) :
    CofinalBelow U q y := by
  classical
  intro r hrq z hzy
  have hn : ¬Upper U r z := by
    intro hz
    exact (hmin z ⟨r, hrq.trans hqp0, hz⟩).not_gt hzy
  unfold Upper at hn
  push Not at hn
  obtain ⟨s, hsr, x, hx, hzx⟩ := hn
  exact ⟨s, hsr, x, hx, hzx, hy s (hsr.trans hrq) x hx⟩

variable [WellFoundedLT V]

/-- Select and attain the least upper bound that is possible somewhere
below the original condition, retaining its global minimality on that cone. -/
theorem exists_least_possible_upper (U : RegularName P V) (p0 : P) (y0 : V)
    (hy0 : Upper U p0 y0) :
    ∃ q : P, q ≤ p0 ∧ ∃ y : V, y ≤ y0 ∧ Upper U q y ∧
      ∀ z : V, (∃ r : P, r ≤ p0 ∧ Upper U r z) → y ≤ z := by
  classical
  let bounds : Set V := {y | ∃ q : P, q ≤ p0 ∧ Upper U q y}
  have hbounds : bounds.Nonempty := ⟨y0, p0, le_rfl, hy0⟩
  let y : V := wellFounded_lt.min bounds hbounds
  have hymem : y ∈ bounds := wellFounded_lt.min_mem bounds hbounds
  obtain ⟨q, hqp0, hy⟩ := hymem
  have hmin (z : V) (hz : ∃ r : P, r ≤ p0 ∧ Upper U r z) : y ≤ z :=
    wellFounded_lt.min_le (s := bounds) hz
  exact ⟨q, hqp0, y, hmin y0 ⟨p0, le_rfl, hy0⟩, hy, hmin⟩

/-- Bounded regular membership has, after a strengthening, an actual
strict upper endpoint below the original bound and dense cofinal members
below that endpoint. No assumption on the endpoint being a limit is needed. -/
theorem exists_cofinal_endpoint (U : RegularName P V) (p0 : P) (y0 : V)
    (hy0 : Upper U p0 y0) :
    ∃ q : P, q ≤ p0 ∧ ∃ y : V, y ≤ y0 ∧ Upper U q y ∧ CofinalBelow U q y := by
  obtain ⟨q, hqp0, y, hyy0, hy, hmin⟩ := exists_least_possible_upper U p0 y0 hy0
  exact ⟨q, hqp0, y, hyy0, hy, cofinalBelow_of_least_possible_upper U p0 q y hqp0 hy hmin⟩

end Erdos1172Part3NamedCofinalEndpoint
