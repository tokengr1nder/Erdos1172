/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BoundedUltrapowerCofinality

@[expose] public section

/-! # Short sequence closure of the bounded ultrapower

For fewer than θ target parameters, regularity bounds their supports and
the indices coding them simultaneously. Fineness and normality then recover
the given target family as the range of one bounded-support name.
-/

set_option autoImplicit false
noncomputable section
open Filter
universe u
namespace Erdos1172GroundUltrapower

variable {I : Type u} (U : Ultrafilter I) (κ θ : Cardinal.{u}) (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)]

variable [Nonempty θ.ord.ToType]

theorem boundedGroundEmbedding_fix_below [CardinalInterFilter (U : Filter I) κ]
    (α : Ordinal.{u}) (hα : α < κ.ord) : (boundedGroundEmbedding U θ a α.toZFSet).val = α.toZFSet := by
  apply boundedCollapse_ordinal_agrees
  · intro β hβ
    exact ⟨boundedConst U θ a β.toZFSet, diagonal_fix_of_cardinalInterFilter U κ β (hβ.trans hα)⟩
  · exact diagonal_fix_of_cardinalInterFilter U κ α hα

end Erdos1172GroundUltrapower
