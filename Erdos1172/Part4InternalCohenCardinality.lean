/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalStoppedCoordinateTriangle
public import Erdos1172.Part4InternalCountableSubsetCodes
public import Erdos1172.Part4InternalMixedProductInjection
public import Erdos1172.Part4LevyCohenIteration
public import Erdos1172.Part4LevyContinuumHypothesis

@[expose] public section

/-!
# Internal cardinality of the complete Cohen-condition family

Every valid graph is internally countable by its actual functional domain
projection. The entire condition name therefore lies in the family of all
internally countable subsets of its bounded product. Internal CH bounds
that family, including arbitrary mixed and empty graphs, by omega-one.

For the concrete first-stage Levy algebra, the proved CH and checked-kappa
identification yield an actual supported surjection from checked kappa onto
all Cohen conditions. No second-stage preservation or externally small
canonical-label type is assumed. Ground dense-presentation construction is
a separate step.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCohen

open ErdosOmegaTwo ErdosPartialInjection ErdosCountableSubsetCodes

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- The whole functional graph is countable, not merely its range. -/
theorem condition_countable {K p : bSet B} {Γ : B}
    (HK : Γ ≤ ErdosHartogs.hartogsProperty omega K)
    (Hp : Γ ≤ condition K p) : Γ ≤ injects_into p omega :=
  ErdosStoppedCoordinateTriangle.graph_countable_of_domain
    (Hp.trans (inf_le_right.trans inf_le_left))
    ((condition_function Hp).trans inf_le_right)
    (countable_of_smallDomain HK (Hp.trans (inf_le_right.trans inf_le_right)))

/-- This inclusion concerns every internally valid member of the condition
name, not just externally listed graph representatives. -/
theorem conditions_subset_countableSubsets {K : bSet B} {Γ : B}
    (HK : Γ ≤ ErdosHartogs.hartogsProperty omega K) :
    Γ ≤ conditions K ⊆ᴮ countableSubsets (prod K two) := by
  rw [subset_unfold']
  apply le_iInf
  intro p
  rw [← deduction]
  have Hp : Γ ⊓ p ∈ᴮ conditions K ≤ condition K p := mem_conditions_iff.mp inf_le_right
  exact mem_countableSubsets_iff.mpr
    ⟨Hp.trans inf_le_left, condition_countable (inf_le_left.trans HK) Hp⟩

theorem two_injects_omegaOne {Γ : B} : Γ ≤ injects_into (two : bSet B) omegaOne := by
  apply injects_into_of_subset
  exact subset_trans' (of_nat_subset_omega (n := 2))
    (subset_of_mem_transitive (omegaOne_Ord.trans inf_le_right) omega_mem_omegaOne)

theorem condition_support_injects_omegaOne {Γ : B} (HCH : Γ ≤ (CH : B)) :
    Γ ≤ injects_into (prod (omegaOne : bSet B) two) omegaOne :=
  injects_into_trans
    (ErdosMixedProductInjection.injects_into_prod injects_into_refl two_injects_omegaOne)
    (ErdosCardinalSquare.omegaOne_square_injects HCH)

/-- Local CH bounds the actual internal family of all Cohen conditions. -/
theorem conditions_injects_omegaOne {Γ : B} (HCH : Γ ≤ (CH : B)) :
    Γ ≤ injects_into (conditions (omegaOne : bSet B)) omegaOne :=
  injects_into_trans
    (injects_into_of_subset (conditions_subset_countableSubsets (le_top.trans omegaOne_property)))
    (countableSubsets_injects_omegaOne HCH (condition_support_injects_omegaOne HCH))

/-- The empty condition is present even though arbitrary condition labels
need not have coefficient one. -/
theorem conditions_omegaOne_nonempty {Γ : B} :
    Γ ≤ exists_mem (conditions (omegaOne : bSet B)) :=
  le_iSup_of_le (∅ : bSet B)
    (empty_mem_conditions (le_top.trans Erdos1172CohenIteration.zero_mem_omegaOne))

end bSet.ErdosCohen

namespace Erdos1172LevyCohen

open bSet bSet.ErdosCohen bSet.ErdosOmegaTwo

/-- Only first-stage CH and the first-stage checked-kappa equality are used. -/
theorem firstStage_conditions_injects_checked_upper (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) :
    (⊤ : FirstAlgebra κ) ≤ injects_into (conditions omegaOne) (check (PSet.ordinalMk κ.ord)) :=
  bv_rw'' (bv_symm (firstStage_checked_upper_eq_omegaOne κ Hκ.isRegular Hκ.aleph0_lt))
    (conditions_injects_omegaOne (Erdos1172LevyCollapse.below_forces_CH κ Hκ))
    B_ext_injects_into_right

/-- An actual supported surjection, chosen at top in the first-stage
algebra, enumerates the complete internal condition family. -/
theorem exists_firstStage_conditions_surjection (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) :
    ∃ f : bSet (FirstAlgebra κ), (⊤ : FirstAlgebra κ) ≤
      is_function (check (PSet.ordinalMk κ.ord)) (conditions omegaOne) f ⊓
        is_surj (check (PSet.ordinalMk κ.ord)) (conditions omegaOne) f := by
  have Hsurj : (⊤ : FirstAlgebra κ) ≤
      surjects_onto (check (PSet.ordinalMk κ.ord)) (conditions omegaOne) :=
    surjects_onto_of_injects_into'
      (firstStage_conditions_injects_checked_upper κ Hκ) conditions_omegaOne_nonempty
  have Hext : B_ext (fun f : bSet (FirstAlgebra κ) =>
      is_function (check (PSet.ordinalMk κ.ord)) (conditions omegaOne) f ⊓
        is_surj (check (PSet.ordinalMk κ.ord)) (conditions omegaOne) f) := by
    apply B_ext_inf B_ext_is_function_right
    unfold is_surj
    exact B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const)
      (h₂ := B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_mem_right)))
  exact exists_convert (exists_surjection_of_surjects_onto Hsurj) Hext

end Erdos1172LevyCohen
