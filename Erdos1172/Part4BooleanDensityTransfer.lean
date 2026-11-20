/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Order.Hom.BoundedLattice

@[expose] public section

/-!
# Transferring Boolean density through regular-image reductions

This file extracts a positive dense family of sets from a small dense
family in a Boolean algebra. The map need not be surjective: it suffices
that every nonzero Boolean value has a reduction in its image, meaning
that every positive image-value below the reduction remains compatible
with the given Boolean value.

Only finitary Boolean operations are preserved. In particular, no
preservation of arbitrary unions is postulated. This transfer does not
construct a regular representation, a generic extension, or a model
satisfying the assumptions.
-/

namespace Erdos1172Part4BooleanDensityTransfer

variable {V C : Type} [BooleanAlgebra C]

/-- A positive image-value is a reduction of `c` when every positive
image-value below it is compatible with `c`. -/
def IsReduction (μ : BoundedLatticeHom (Set V) C) (c : C) (A : Set V) : Prop :=
  μ A ≠ ⊥ ∧ ∀ T : Set V, μ T ≠ ⊥ → μ T ≤ μ A → μ T ⊓ c ≠ ⊥

/-- A reduction below an upper image-bound must itself lie below that
bound: otherwise its Boolean difference is a positive incompatible
image-value. -/
theorem reduction_le_of_le (μ : BoundedLatticeHom (Set V) C)
    {c : C} {A X : Set V} (hA : IsReduction μ c A) (hc : c ≤ μ X) :
    μ A ≤ μ X := by
  have hzero : μ (A \ X) = ⊥ := by
    by_contra hnonzero
    apply hA.2 (A \ X) hnonzero (OrderHomClass.mono μ Set.sdiff_subset)
    rw [map_sdiff']
    apply le_antisymm _ bot_le
    exact (inf_le_inf_left _ hc).trans_eq disjoint_sdiff_self_left.eq_bot
  exact sdiff_eq_bot_iff.mp (by simpa only [map_sdiff'] using hzero)

/-- An actual positive image-value below `c` is a reduction of `c`. -/
theorem isReduction_of_value_le (μ : BoundedLatticeHom (Set V) C)
    {c : C} {A : Set V} (hA : μ A ≠ ⊥) (hAc : μ A ≤ c) :
    IsReduction μ c A := by
  refine ⟨hA, ?_⟩
  intro T hT hTA
  simpa only [inf_of_le_left (hTA.trans hAc)] using hT

/-- Surjectivity supplies reductions, although the main density
transfer only requires the weaker regular-image reduction property. -/
theorem exists_reduction_of_surjective (μ : BoundedLatticeHom (Set V) C)
    (hμ : Function.Surjective μ) {c : C} (hc : c ≠ ⊥) :
    ∃ A : Set V, IsReduction μ c A := by
  obtain ⟨A, hA⟩ := hμ c
  refine ⟨A, isReduction_of_value_le μ ?_ ?_⟩
  · simpa only [hA] using hc
  · exact hA.le

/-- Choose one reduction per dense Boolean value. Their representatives
form a positive family dense modulo the kernel of `μ`, with exactly the
same index type as the original Boolean dense family. -/
theorem exists_positive_dense_family_of_reductions
    (μ : BoundedLatticeHom (Set V) C)
    (hreduce : ∀ c : C, c ≠ ⊥ → ∃ A : Set V, IsReduction μ c A)
    {I : Type} (d : I → C) (hd : ∀ i, d i ≠ ⊥)
    (hdense : ∀ c : C, c ≠ ⊥ → ∃ i, d i ≤ c) :
    ∃ B : I → Set V, (∀ i, μ (B i) ≠ ⊥) ∧
      ∀ X : Set V, μ X ≠ ⊥ → ∃ i, μ (B i \ X) = ⊥ := by
  classical
  choose B hB using fun i => hreduce (d i) (hd i)
  refine ⟨B, fun i => (hB i).1, ?_⟩
  intro X hX
  obtain ⟨i, hi⟩ := hdense (μ X) hX
  refine ⟨i, ?_⟩
  rw [map_sdiff']
  exact sdiff_eq_bot_iff.mpr (reduction_le_of_le μ (hB i) hi)

end Erdos1172Part4BooleanDensityTransfer
