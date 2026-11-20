/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaUltrapowerStrings
public import Erdos1172.Part4ShioyaLevyChainCondition
public import Erdos1172.Part4ShioyaCohenCover
public import Erdos1172.Part4ShioyaDenseCoverIso
public import Erdos1172.Part4PosetGenericFilter

@[expose] public section

/-! # Decisions at nonconstant ordinal points of the bounded ultrapower -/

set_option autoImplicit false
noncomputable section
open Filter Erdos1172GroundUltrapower Erdos1172PosetCompletion
universe u
namespace Erdos1172Shioya.UltrapowerStage
variable {I : Type u} (U : Ultrafilter I) {κ θ : Cardinal.{u}} (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType]
variable (hθ : θ.IsInaccessible) (fine : FineOn U a) (normal : NormalOn U a) (ht : FiberOrderType U κ θ a)

/-- The critical seed is a bounded point in j(κ), and its ordinal is κ. -/
def criticalOrdinalPoint (hk : κ < θ) : Point U a κ.ord.ToType := by
  have eq : ordinalImage U a κ.ord = θ.ord := Ordinal.toZFSet_injective
    ((ordinalImage_code U a _).trans (boundedDiagonal_critical_image U κ θ a fine normal ht))
  exact (indexEquiv U a κ.ord).symm (Ordinal.ToType.mk ⟨κ.ord,(Cardinal.ord_lt_ord.mpr hk).trans_eq eq.symm⟩)

theorem criticalOrdinalPoint_ord (hk : κ < θ) :
    (indexEquiv U a κ.ord (criticalOrdinalPoint U a fine normal ht hk)).toOrd.val = κ.ord := by
  unfold criticalOrdinalPoint
  rw [Equiv.apply_symm_apply]
  exact congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)

end Erdos1172Shioya.UltrapowerStage
