/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanUltrapowerCriticalIdeal

@[expose] public section

/-! # Dense critical-seed values of weighted subsets

A ground family of Boolean coefficients gives a subset name of the checked
critical ordinal. In the target algebra, membership of the critical seed
in its lift has precisely the given germ as its value. The regular
completion therefore has a dense family of such membership values.
-/

set_option autoImplicit false
noncomputable section
open Filter bSet Erdos1172GroundUltrapower Erdos1172PosetCompletion Erdos1172PositiveBoolean
open Erdos1172LevyCohen Erdos1172BooleanFactor bSet.ErdosIdeal bSet.ErdosOmegaTwo
open scoped Flypitch

universe u v

namespace Erdos1172BooleanUltrapower

section Density

variable {I : Type u} {B : Type v} [BooleanAlgebra B] (U : Ultrafilter I)

theorem germValue_positive (p : Positive (Germ (U : Filter I) B)) :
    germValue U p.val = condition p := by
  apply Heyting.Regular.coe_injective
  have hcone : LowerSet.Iic p = (germValue U p.val).val := by
    apply SetLike.ext
    intro q
    rfl
  change (germValue U p.val).val = (LowerSet.Iic p)ᶜᶜ
  rw [hcone, (germValue U p.val).prop.eq]

end Density

end Erdos1172BooleanUltrapower
