/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalCarrier
public import Erdos1172.Part4LevyAnonymousSmallAuxiliary
public import Erdos1172.Part4ShioyaInternalProjectionGraph
public import Erdos1172.Part4ShioyaInternalSingletonOrder
public import Erdos1172.Part4ShioyaInternalOrderMatrix

@[expose] public section

/-! # Single ordinal enumerations of small internally named forcing orders -/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
open Lattice
universe u
namespace bSet.ErdosShioyaInternal
open ErdosPartialInjection Erdos1172LevyCohen Erdos1172CompleteSubalgebra ErdosRelationGraph

variable {κ θ : Cardinal.{u}}
local notation "A" => anonymousAlgebra κ

/-- Countable partial assignments from H to X, represented by their graphs. -/
def countableCollapse {B : Type u} [NontrivialCompleteBooleanAlgebra B] (H X : bSet B) : bSet B :=
  comprehend (fun g => is_func g ⊓ injects_into g omega) (bv_powerset (prod H X))

theorem countableCollapse_mem {B : Type u} [NontrivialCompleteBooleanAlgebra B] {Γ : B} {g H X : bSet B} :
    Γ ≤ g ∈ᴮ countableCollapse H X ↔ Γ ≤ g ⊆ᴮ prod H X ∧ Γ ≤ is_func g ∧ Γ ≤ injects_into g omega := by
  rw [countableCollapse,mem_comprehend_and (B_ext_inf ErdosPrefixFunction.is_func_ext_graph B_ext_injects_into_left),
    mem_powerset_iff,le_inf_iff]

end bSet.ErdosShioyaInternal
