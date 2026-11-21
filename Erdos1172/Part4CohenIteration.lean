/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4PositiveBooleanCompletion
public import Erdos1172.Part4BooleanNameIteration
public import Erdos1172.Part4InternalCohenConditions
public import Erdos1172.Part4InternalHartogsUniqueness

@[expose] public section

/-!
# The actual Boolean iteration by internal small partial binary graphs

The second-stage forcing is computed from the first-stage internal names.
Its canonical empty label supplies the entire positive first-stage algebra,
whose regular completion is explicitly isomorphic to that original algebra.
Thus the first-stage complete embedding is constructed, not postulated.

At the internal first uncountable ordinal this gives a nontrivial complete
Boolean algebra without extra nonemptiness assumptions. No generic subset,
preservation result, anonymous quotient, or ideal is yet asserted here.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch

universe u

namespace Erdos1172CohenIteration

open bSet Erdos1172PosetCompletion

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

abbrev Conditions (K : bSet B) :=
  Erdos1172BooleanNameIteration.Condition (ErdosCohen.conditions K)

abbrev Algebra (K : bSet B) := Completion (Conditions K)

def firstStageHom (K : bSet B) : CompleteLatticeHom B (Algebra K) :=
  (Erdos1172BooleanNameIteration.firstStageHom (ErdosCohen.conditions K)).comp
    Erdos1172PositiveBoolean.completionHom

theorem firstStageHom_injective {K : bSet B}
    (Hzero : (⊤ : B) ≤ (0 : bSet B) ∈ᴮ K) :
    Function.Injective (firstStageHom K) :=
  (Erdos1172BooleanNameIteration.firstStageHom_injective_of_top_label
    (ErdosCohen.emptyLabel K) (ErdosCohen.emptyLabel_bval_eq_top Hzero)).comp
      Erdos1172PositiveBoolean.completionHom_injective

theorem firstStageHom_compl (K : bSet B) (b : B) : firstStageHom K bᶜ = (firstStageHom K b)ᶜ := by
  change Erdos1172BooleanNameIteration.firstStageHom (ErdosCohen.conditions K)
    (Erdos1172PositiveBoolean.element bᶜ) =
    (Erdos1172BooleanNameIteration.firstStageHom (ErdosCohen.conditions K)
      (Erdos1172PositiveBoolean.element b))ᶜ
  rw [Erdos1172PositiveBoolean.element_compl]
  exact Erdos1172PosetProjection.regularPullback_compl
    (Erdos1172BooleanNameIteration.projection (ErdosCohen.conditions K))
    (Erdos1172BooleanNameIteration.projection_exactLifts (ErdosCohen.conditions K)) _

theorem condition_le_firstStageHom_iff (K : bSet B) (p : Conditions K) (b : B) :
    condition p ≤ firstStageHom K b ↔ p.value ≤ b := by
  change condition p ≤
    Erdos1172BooleanNameIteration.firstStageHom (ErdosCohen.conditions K)
      (Erdos1172PositiveBoolean.element b) ↔ p.value ≤ b
  rw [Erdos1172BooleanNameIteration.condition_le_firstStageHom_iff]
  rw [← Erdos1172PositiveBoolean.element_condition]
  exact Erdos1172PositiveBoolean.element_le_element_iff

@[instance_reducible]
def algebraNontrivialCompleteBooleanAlgebra (K : bSet B)
    (Hzero : (⊤ : B) ≤ (0 : bSet B) ∈ᴮ K) :
    NontrivialCompleteBooleanAlgebra (Algebra K) := by
  let : Nonempty (Conditions K) :=
    Erdos1172BooleanNameIteration.condition_nonempty_of_mem
      (ErdosCohen.empty_mem_conditions Hzero)
  exact { toCompleteBooleanAlgebra := inferInstance, bot_lt_top := bot_lt_top }

theorem zero_mem_omegaOne : (⊤ : B) ≤ (0 : bSet B) ∈ᴮ ErdosOmegaTwo.omegaOne :=
  mem_of_mem_Ord (of_nat_mem_omega (n := 0)) ErdosOmegaTwo.omega_mem_omegaOne
    ErdosOmegaTwo.omegaOne_Ord

/-- The extension-computed second stage at the new internal omega-one. -/
abbrev omegaOneAlgebra (B : Type u) [NontrivialCompleteBooleanAlgebra B] :=
  Algebra (ErdosOmegaTwo.omegaOne : bSet B)

instance omegaOneNontrivialCompleteBooleanAlgebra :
    NontrivialCompleteBooleanAlgebra (omegaOneAlgebra B) :=
  algebraNontrivialCompleteBooleanAlgebra _ zero_mem_omegaOne

def omegaOneFirstStageHom : CompleteLatticeHom B (omegaOneAlgebra B) :=
  firstStageHom ErdosOmegaTwo.omegaOne

theorem omegaOneFirstStageHom_injective :
    Function.Injective (omegaOneFirstStageHom (B := B)) :=
  firstStageHom_injective zero_mem_omegaOne

theorem omegaOneFirstStageHom_compl (b : B) :
    omegaOneFirstStageHom bᶜ = (omegaOneFirstStageHom b)ᶜ :=
  firstStageHom_compl _ b

end Erdos1172CohenIteration
