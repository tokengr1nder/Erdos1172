/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3FunctionDecisions
public import Erdos1172.Part3RegularMembership

@[expose] public section

/-!
# Dense least-or-empty decisions for regular names

For a regular subname of a fixed well-order, either no point is possible
below a condition, or its least possible point becomes actual after one
refinement. This gives a persistent, unique, dense least-or-empty selector.

The empty outcome excludes actual membership at every later refinement.
The nonempty outcome excludes every smaller point at every refinement.
No countable closure, generic extension, named enumeration, or completeness
principle for canonical covers is assumed or concluded.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3RegularLeastMember

open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName ground)

variable {P V : Type} [Preorder P] [LinearOrder V]

/-- `none` means permanently empty; `some x` means that x is actual and
every smaller point is permanently absent below the current condition. -/
def LeastDecision (U : RegularName P V) (p : P) : Option V → Prop
  | none => ∀ q : P, q ≤ p → ∀ x : V, ¬U.holds q x
  | some x => U.holds p x ∧
      ∀ q : P, q ≤ p → ∀ y : V, y < x → ¬U.holds q y

theorem leastDecision_persistent {U : RegularName P V} {p q : P} {v : Option V}
    (hqp : q ≤ p) (h : LeastDecision U p v) : LeastDecision U q v := by
  cases v with
  | none => exact fun r hrq x => h r (hrq.trans hqp) x
  | some x =>
      exact ⟨U.persistent hqp h.1, fun r hrq y hy => h.2 r (hrq.trans hqp) y hy⟩

theorem leastDecision_unique {U : RegularName P V} {p : P} {v w : Option V}
    (hv : LeastDecision U p v) (hw : LeastDecision U p w) : v = w := by
  cases v with
  | none =>
      cases w with
      | none => rfl
      | some y => exact (hv p le_rfl y hw.1).elim
  | some x =>
      cases w with
      | none => exact (hw p le_rfl x hv.1).elim
      | some y =>
          rcases lt_trichotomy x y with hxy | hxy | hyx
          · exact (hw.2 p le_rfl x hxy hv.1).elim
          · exact congrArg some hxy
          · exact (hv.2 p le_rfl y hyx hw.1).elim

theorem actual_of_leastDecision_some {U : RegularName P V} {p : P} {x : V}
    (h : LeastDecision U p (some x)) : U.holds p x := h.1

theorem not_actual_of_leastDecision_none {U : RegularName P V} {p q : P}
    (h : LeastDecision U p none) (hqp : q ≤ p) (x : V) : ¬U.holds q x :=
  h q hqp x

theorem no_smaller_of_leastDecision_some {U : RegularName P V} {p q : P} {x y : V}
    (h : LeastDecision U p (some x)) (hqp : q ≤ p) (hyx : y < x) : ¬U.holds q y :=
  h.2 q hqp y hyx

variable [WellFoundedLT V]

/-- Choose the least possible member, not the least member of the
possibly empty fixed-condition actual-member set. -/
theorem exists_least_deciding_refinement (U : RegularName P V) (p : P) :
    ∃ q : P, q ≤ p ∧ ∃ v : Option V, LeastDecision U q v := by
  classical
  let possible : Set V := {x | ∃ q : P, q ≤ p ∧ U.holds q x}
  by_cases hpossible : possible.Nonempty
  · let x : V := wellFounded_lt.min possible hpossible
    have hx : x ∈ possible := wellFounded_lt.min_mem possible hpossible
    obtain ⟨q, hqp, hqx⟩ := hx
    refine ⟨q, hqp, some x, hqx, ?_⟩
    intro r hrq y hyx hy
    have hyPossible : y ∈ possible := ⟨r, hrq.trans hqp, hy⟩
    have hxy : x ≤ y := wellFounded_lt.min_le (s := possible) hyPossible
    exact (not_le_of_gt hyx) hxy
  · refine ⟨p, le_rfl, none, ?_⟩
    intro q hqp x hx
    exact hpossible ⟨x, q, hqp, hx⟩

/-- An explicit total decision name for the least member, with an empty
outcome. Density requires no closure property of the decision order. -/
def leastMember (U : RegularName P V) : FunctionDecisions P Unit (Option V) where
  decides p _ v := LeastDecision U p v
  dense p _ := exists_least_deciding_refinement U p
  persistent hqp h := leastDecision_persistent hqp h
  unique hv hw := leastDecision_unique hv hw

theorem leastMember_some_iff (U : RegularName P V) (p : P) (x : V) :
    (leastMember U).decides p () (some x) ↔ U.holds p x ∧
      ∀ q : P, q ≤ p → ∀ y : V, y < x → ¬U.holds q y := Iff.rfl

theorem leastMember_none_iff (U : RegularName P V) (p : P) :
    (leastMember U).decides p () none ↔
      ∀ q : P, q ≤ p → ∀ x : V, ¬U.holds q x := Iff.rfl

/-- On a ground set the nonempty outcome is exactly its ordinary least
element; it is independent of the chosen condition. -/
theorem leastMember_ground_some_iff (s : Set V) (p : P) (x : V) :
    (leastMember (ground s)).decides p () (some x) ↔ IsLeast s x := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro y hy
    exact le_of_not_gt (fun hyx => h.2 p le_rfl y hyx hy)
  · intro h
    refine ⟨h.1, ?_⟩
    intro q _ y hyx hy
    exact (not_le_of_gt hyx) (h.2 hy)

/-- On a ground set the empty outcome is equivalent to actual emptiness. -/
theorem leastMember_ground_none_iff (s : Set V) (p : P) :
    (leastMember (ground s)).decides p () none ↔ s = ∅ := by
  constructor
  · intro h
    ext x
    constructor
    · intro hx
      exact (h p le_rfl x hx).elim
    · intro hx
      exact hx.elim
  · intro hs
    subst s
    intro q _ x hx
    exact hx

end Erdos1172Part3RegularLeastMember
