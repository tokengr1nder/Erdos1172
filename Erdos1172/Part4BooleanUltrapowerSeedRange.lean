/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4GroundFineSeedOrderType
public import Erdos1172.Part4BooleanUltrapowerAtomic
public import Erdos1172.Part4BooleanUltrapowerChecked
public import Erdos1172.Part4BooleanUltrapowerConstants

@[expose] public section

/-!
# The checked critical seed for a fine Boolean ultrapower

The ultrafilter may be indexed by any small type. Its κ-completeness fixes
the checked predecessors of κ, while its normal fine fibers of order type κ
identify the image of checked κ with checked θ. For the first collapse these
facts give membership in the lifted omega-one, exclusion from every mixed
bounded initial segment, and coverage of every mixed member of the seed.
-/

set_option autoImplicit false
noncomputable section
open Filter bSet Erdos1172GroundUltrapower Lattice
open scoped Flypitch
universe u

namespace Erdos1172BooleanUltrapower

variable {I B : Type u} [NontrivialCompleteBooleanAlgebra B] (U : Ultrafilter I)
variable (κ : Cardinal.{u}) [CardinalInterFilter (U : Filter I) κ]

section Checked

variable [CountableInterFilter (U : Filter I)]

theorem hereditary_fixed_checked_ordinal (α : Ordinal.{u}) (hα : α < κ.ord) :
    (⊤ : Algebra U B) ≤ hereditary U (fun _ => (check (PSet.ordinalMk α) : bSet B)) =ᴮ
      check (PSet.ordinalMk α) := by
  apply bv_trans (liftName_checked U (fun _ => PSet.ordinalMk α))
  apply check_bv_eq
  apply PSet.equiv_iff_eq.mpr
  rw [mk_groundPSet]
  exact diagonal_fix_of_cardinalInterFilter U κ α hα

end Checked

open Erdos1172LevyCohen (FirstAlgebra firstStage_checked_upper_eq_omegaOne)
open bSet.ErdosOmegaTwo (omegaOne)

variable (hκ : κ.IsRegular) (hunc : Cardinal.aleph0 < κ)

def fineFirstCollapseLift (x : bSet (FirstAlgebra κ)) : bSet (Algebra U (FirstAlgebra κ)) :=
  letI := CardinalInterFilter.toCountableInterFilter (U : Filter I) hunc
  hereditary U (fun _ => x)

local notation "eκ" => firstCollapseConstantHom U κ hκ hunc
local notation "jκ" => fineFirstCollapseLift U κ hunc
local notation "sκ" => (check (PSet.ordinalMk κ.ord) : bSet (Algebra U (FirstAlgebra κ)))

end Erdos1172BooleanUltrapower
