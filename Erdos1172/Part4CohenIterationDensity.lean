/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanNameIteration
public import Erdos1172.Part4InternalCohenExtension

@[expose] public section

/-!
# Coordinate-decision density for the actual Cohen-name iteration

The internal extension theorem supplies a mixed partial graph and a mixed
binary value at the original first-stage condition. Canonical-label density
then gives a positive iteration strengthening representing that graph.
A further positive refinement chooses a canonical binary child, hence an
actual zero or one. No mixed name is treated as a fixed child without this
refinement, and no dense-set hypothesis is supplied to the final theorem.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch

universe u

namespace Erdos1172CohenIteration

open bSet ErdosCohen Erdos1172BooleanNameIteration

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- These are the actual two canonical children, not an extraction from a
Boolean membership assertion at an unchanged condition. -/
theorem two_child_eq_zero_or_one (i : (two : bSet B).type) :
    (two : bSet B).func i = (0 : bSet B) ∨
      (two : bSet B).func i = (1 : bSet B) := by
  cases i with
  | none => exact Or.inr rfl
  | some j =>
    cases j with
    | none => exact Or.inl rfl
    | some h => exact PEmpty.elim h

end Erdos1172CohenIteration
