/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4CohenIteration
public import Erdos1172.Part4CohenIterationDensity
public import Erdos1172.Part4LevyOmegaOne

@[expose] public section

/-!
# The concrete below-cardinal collapse followed by internal Cohen forcing

The first stage is the constructed finite-support below-κ collapse. The
second stage uses all first-stage names for countable-domain binary partial
functions on its internal omega-one. For regular uncountable κ, the earlier
Hartogs theorem identifies this domain with checked κ in the first stage.

This is a dependent name iteration, not a ground product. No identification
with the SECOND-stage internal omega-one, closure, full-GCH preservation,
generic ultrafilter, or ideal is asserted by this construction.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch

universe u

namespace Erdos1172LevyCohen

open bSet Erdos1172PosetCompletion Erdos1172LevyCollapse

abbrev FirstAlgebra (κ : Cardinal.{u}) := Completion (BelowCondition κ)

abbrev Algebra (κ : Cardinal.{u}) :=
  Erdos1172CohenIteration.omegaOneAlgebra (FirstAlgebra κ)

def firstStageHom (κ : Cardinal.{u}) : CompleteLatticeHom (FirstAlgebra κ) (Algebra κ) :=
  Erdos1172CohenIteration.omegaOneFirstStageHom

theorem firstStageHom_injective (κ : Cardinal.{u}) :
    Function.Injective (firstStageHom κ) :=
  Erdos1172CohenIteration.omegaOneFirstStageHom_injective

theorem firstStageHom_compl (κ : Cardinal.{u}) (b : FirstAlgebra κ) :
    firstStageHom κ bᶜ = (firstStageHom κ b)ᶜ :=
  Erdos1172CohenIteration.omegaOneFirstStageHom_compl b

theorem firstStage_checked_upper_eq_omegaOne (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ) :
    (⊤ : FirstAlgebra κ) ≤
      check (PSet.ordinalMk κ.ord) =ᴮ ErdosOmegaTwo.omegaOne :=
  below_checked_upper_eq_omegaOne κ Hκ Hunc

theorem firstStage_coordinate_mem (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ)
    (i : (PSet.ordinalMk κ.ord).Type) :
    (⊤ : FirstAlgebra κ) ≤
      check ((PSet.ordinalMk κ.ord).Func i) ∈ᴮ ErdosOmegaTwo.omegaOne :=
  mem_congr bv_refl (firstStage_checked_upper_eq_omegaOne κ Hκ Hunc)
    (check_mem (PSet.func_mem (PSet.ordinalMk κ.ord) i))

/-- Every ground coordinate below κ is decided densely in the actual
dependent iteration; no same-model cardinal-preservation claim is needed. -/
theorem coordinate_decision_dense (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ)
    (i : (PSet.ordinalMk κ.ord).Type) :
    ∀ p : Erdos1172CohenIteration.Conditions
        (ErdosOmegaTwo.omegaOne : bSet (FirstAlgebra κ)),
      ∃ r ∈ {r | Erdos1172CohenIteration.decidesCoordinate
        (check ((PSet.ordinalMk κ.ord).Func i)) r}, r ≤ p :=
  Erdos1172CohenIteration.coordinate_decision_dense
    ErdosOmegaTwo.omegaOne_property (firstStage_coordinate_mem κ Hκ Hunc i)

end Erdos1172LevyCohen
