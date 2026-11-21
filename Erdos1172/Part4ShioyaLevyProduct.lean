/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.SetTheory.Cardinal.Ordinal
public import Erdos1172.Part4DenseCompletionCardinality
public import Erdos1172.Part4ShioyaStringTransport
public import Mathlib.Order.Bounds.OrderIso

@[expose] public section

/-! # Index and alphabet carriers for the Lévy product -/

set_option autoImplicit false
noncomputable section
universe u

namespace Erdos1172Shioya.LevyProduct

variable {θ : Cardinal.{u}}

abbrev Index (θ : Cardinal.{u}) := θ.ord.ToType

end Erdos1172Shioya.LevyProduct
