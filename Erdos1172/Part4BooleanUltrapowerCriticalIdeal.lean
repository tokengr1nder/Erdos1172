/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanUltrapowerOperations
public import Erdos1172.Part4BooleanUltrapowerConstants
public import Erdos1172.Part4BooleanUltrapowerChecked
public import Erdos1172.Part4BooleanFactorPoset
public import Erdos1172.Part4InternalOmegaOneCountablyBounded
public import Erdos1172.Part4InternalIdealNormality

@[expose] public section

/-! # The critical-seed ideal on omega-one in the first Lévy collapse

The constants embed the collapse algebra completely into the completion
of its ultrapower. The hereditary name map fixes each checked predecessor
of the critical ordinal and moves the critical ordinal above its seed.
Splitting mixed members of omega-one into their checked values therefore
places every internally countable subset of omega-one in the seed kernel.
-/

set_option autoImplicit false
noncomputable section
open Filter bSet Erdos1172GroundUltrapower Erdos1172LevyCohen Lattice
open bSet.ErdosIdeal bSet.ErdosOmegaTwo
open scoped Flypitch
universe u

namespace Erdos1172BooleanUltrapower

variable (κ : Cardinal.{u}) (U : Ultrafilter κ.ord.ToType)
variable [CardinalInterFilter (U : Filter κ.ord.ToType) κ]
variable (hκ : κ.IsRegular) (hunc : Cardinal.aleph0 < κ)

def firstCollapseLift (x : bSet (FirstAlgebra κ)) : bSet (Algebra U (FirstAlgebra κ)) :=
  letI := CardinalInterFilter.toCountableInterFilter (U : Filter κ.ord.ToType) hunc
  hereditary U (fun _ => x)

local notation "e" => firstCollapseConstantHom U κ hκ hunc
local notation "j" => firstCollapseLift κ U hunc
local notation "s" => (check (PSet.ordinalMk κ.ord) : bSet (Algebra U (FirstAlgebra κ)))

end Erdos1172BooleanUltrapower
