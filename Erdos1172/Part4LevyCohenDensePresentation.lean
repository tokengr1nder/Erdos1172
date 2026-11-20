/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCohenCardinality
public import Erdos1172.Part4BooleanIterationDensePresentation
public import Erdos1172.Part4DenseCompletionCardinality
public import Erdos1172.Part4LevyContinuumHypothesis

@[expose] public section

/-!
# A kappa-sized dense presentation of the actual Levy--Cohen iteration

The first-stage algebra has cardinality at most the inaccessible kappa.
Its actual supported surjection from checked kappa onto all internal Cohen
conditions produces a genuinely dense range of canonical iteration conditions.
This bounds the completed two-stage algebra by 2^kappa and every positive
pairwise-disjoint family by kappa.

The antichain conclusion is kappa-plus-cc, not kappa-cc. The completion is
not asserted to have cardinality at most kappa. No higher-cardinal or GCH
preservation, anonymous-quotient property, or ideal construction is assumed.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace Erdos1172LevyCohen

open bSet bSet.ErdosOmegaTwo

/-- The dense set consists of actual conditions, with a genuine stronger
member below every condition of the dependent name iteration. -/
theorem exists_dense_presentation (κ : Cardinal.{u}) (Hκ : κ.IsInaccessible) :
    ∃ D : Set (Erdos1172CohenIteration.Conditions
        (omegaOne : bSet (FirstAlgebra κ))),
      Cardinal.mk D ≤ κ ∧
        ∀ p : Erdos1172CohenIteration.Conditions
          (omegaOne : bSet (FirstAlgebra κ)), ∃ d ∈ D, d ≤ p := by
  obtain ⟨f, Hf⟩ := exists_firstStage_conditions_surjection κ Hκ
  obtain ⟨D, Hsize, Hdense⟩ :=
    Erdos1172BooleanNameIteration.exists_dense_presentation_of_checked_surjection
      (Hf.trans inf_le_left) (Hf.trans inf_le_right)
  refine ⟨D, ?_, Hdense⟩
  have Hindex : Cardinal.mk (PSet.ordinalMk κ.ord).Type = κ := by
    rw [PSet.ordinalMk_type, Cardinal.mk_ord_toType]
  calc
    Cardinal.mk D ≤ Cardinal.mk (FirstAlgebra κ) *
        Cardinal.mk (PSet.ordinalMk κ.ord).Type := Hsize
    _ ≤ κ * κ := mul_le_mul'
      (Erdos1172LevyCollapse.below_completion_cardinal_le κ Hκ) Hindex.le
    _ = κ := Cardinal.mul_eq_self Hκ.aleph0_lt.le

/-- All completed Boolean values are counted by subsets of the constructed
dense set, not merely by the number of generators. -/
theorem completion_cardinal_le_two_power (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) : Cardinal.mk (Algebra κ) ≤ 2 ^ κ := by
  obtain ⟨D, Hsize, Hdense⟩ := exists_dense_presentation κ Hκ
  exact (Erdos1172PosetCompletion.completion_cardinal_le_two_pow_dense D Hdense).trans
    (Cardinal.power_le_power_left (by simp : (2 : Cardinal.{u}) ≠ 0) Hsize)

/-- This is the actual kappa-plus chain condition, expressed as a bound
on every indexed positive pairwise-disjoint family. -/
theorem disjoint_family_cardinal_le_upper (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) {ι : Type u} (a : ι → Algebra κ)
    (Hpositive : ∀ i, a i ≠ ⊥)
    (Hdisjoint : ∀ i j, i ≠ j → a i ⊓ a j = ⊥) :
    Cardinal.mk ι ≤ κ := by
  obtain ⟨D, Hsize, Hdense⟩ := exists_dense_presentation κ Hκ
  exact (Erdos1172PosetCompletion.disjoint_family_cardinal_le_dense
    D Hdense a Hpositive Hdisjoint).trans Hsize

end Erdos1172LevyCohen
