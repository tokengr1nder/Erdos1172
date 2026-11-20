/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyPreparationCohenConditions

@[expose] public section

/-! # A set of forcing names for mixed Shioya presentations in the preparing extension -/

set_option autoImplicit false
noncomputable section
universe u
open bSet ErdosCheckedIndicator ErdosRelationGraph Lattice
open scoped Flypitch
namespace bSet.ErdosShioyaInternal
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

/-- The two relation names code the order and the incidence relation
between a point of the presentation and a coordinate of its binary word. -/
structure Fields (B : Type u) [NontrivialCompleteBooleanAlgebra B] where
  carrier : bSet B
  order : bSet B
  point : bSet B
  length : bSet B
  bits : bSet B

def Fields.code (t : Fields B) : N :=
  pair t.carrier (pair t.order (pair t.point (pair t.length t.bits)))

abbrev ord (o : Ordinal.{u}) := PSet.ordinalMk o
end bSet.ErdosShioyaInternal
