/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalCarrier
public import Erdos1172.Part4LevyAnonymousSmallAuxiliary
public import Erdos1172.Part4ShioyaInternalProjectionGraph
public import Erdos1172.Part4ShioyaInternalSingletonOrder
public import Erdos1172.Part4InternalBoundedImageRecursionTotal
public import Erdos1172.Part4InternalFusionHistoryCongruence

@[expose] public section

/-! # Ordinal recursion of cones along a named collapse path -/

set_option autoImplicit false
noncomputable section
universe u
open scoped Flypitch
open Lattice
namespace bSet.ErdosShioyaInternal.CollapsePath
open ErdosBoundedFunctionValue ErdosBoundedImageRecursion ErdosRelationGraph ErdosFusionHistoryCongruence
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

/-- A condition surviving all earlier stages. -/
def survives (past p : N) : B := allIn past (fun C => p ∈ᴮ C)

def test (R past label p : N) : B :=
  survives past p ⊓ (survives past label ⟹ edge R p label)

/-- At each stage retain all past constraints. When the proposed label
survives them, also restrict to its principal lower cone. -/
def next (P R input i past : N) : N :=
  comprehend (test R past (graphValue P input i)) P

def trace (P R input : N) (history : N) : B :=
  imageRecLaw (bv_powerset P) (next P R input) history

end bSet.ErdosShioyaInternal.CollapsePath
