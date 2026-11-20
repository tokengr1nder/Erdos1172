/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaUltrapowerStage
public import Erdos1172.Part4DenseCompletionCardinality
public import Erdos1172.Part4ShioyaStringTransport
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Order.PFilter

@[expose] public section

/-! # Representatives of bounded ultrapower stage points -/

set_option autoImplicit false
noncomputable section
open Filter Erdos1172GroundUltrapower
universe u
namespace Erdos1172Shioya.UltrapowerStage

variable {I : Type u} (U : Ultrafilter I) {θ : Cardinal.{u}} (a : I → Set θ.ord.ToType)

def repr {V : Type u} (z : Point U a V) : I → V := fun i =>
  z.property.choose_spec.choose (boundedFiber θ a z.property.choose i)

theorem repr_eq {V : Type u} (z : Point U a V) :
    Germ.ofFun (repr U a z) = z.val := z.property.choose_spec.choose_spec

end Erdos1172Shioya.UltrapowerStage
