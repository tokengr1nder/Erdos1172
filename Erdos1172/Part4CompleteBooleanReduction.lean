/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanDensityTransfer
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.Hom.CompleteLattice

@[expose] public section

/-!
# Reductions supplied by complete Boolean embeddings

The least element whose image covers a Boolean value is a reduction of
that value. Thus a complete embedding supplies the regular-image
reductions needed to transfer a small dense family. A preceding
surjective map from sets only has to preserve finite Boolean operations;
no preservation of arbitrary unions by that map is assumed.

This is an algebraic transfer theorem, not the construction of a Boolean
embedding, a generic extension, or a model of set theory.
-/

namespace Erdos1172Part4CompleteBooleanReduction

open Erdos1172Part4BooleanDensityTransfer

variable {B C : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

/-- The least source value whose image covers `c`. -/
noncomputable def lowerProjection (e : CompleteLatticeHom B C) (c : C) : B :=
  sInf {b : B | c ≤ e b}

/-- Completeness ensures that the image of the projection still covers
the original Boolean value. -/
theorem le_image_lowerProjection (e : CompleteLatticeHom B C) (c : C) :
    c ≤ e (lowerProjection e c) := by
  rw [lowerProjection, map_sInf]
  refine le_sInf ?_
  rintro _ ⟨b, hb, rfl⟩
  exact hb

/-- The projection is below every source value whose image covers `c`. -/
theorem lowerProjection_le (e : CompleteLatticeHom B C) {c : C} {b : B}
    (h : c ≤ e b) : lowerProjection e c ≤ b :=
  sInf_le h

/-- The projection is left adjoint to the complete homomorphism. -/
theorem lowerProjection_le_iff (e : CompleteLatticeHom B C) {c : C} {b : B} :
    lowerProjection e c ≤ b ↔ c ≤ e b := by
  exact ⟨fun h => (le_image_lowerProjection e c).trans (OrderHomClass.mono e h),
    lowerProjection_le e⟩

/-- A nonzero value has a nonzero projection. -/
theorem lowerProjection_ne_bot (e : CompleteLatticeHom B C)
    {c : C} (hc : c ≠ ⊥) : lowerProjection e c ≠ ⊥ := by
  intro h
  apply hc
  apply le_antisymm _ bot_le
  simpa only [h, map_bot] using le_image_lowerProjection e c

/-- Every nonzero source value below the projection has image compatible
with the original value. This fact itself does not require injectivity. -/
theorem inf_image_lowerProjection_ne_bot (e : CompleteLatticeHom B C)
    {c : C} {b : B} (hb : b ≠ ⊥) (hbp : b ≤ lowerProjection e c) :
    e b ⊓ c ≠ ⊥ := by
  intro hzero
  have hcompl : c ≤ e (bᶜ) := by
    rw [map_compl']
    exact le_compl_iff_disjoint_left.mpr (disjoint_iff.mpr hzero)
  exact hb (le_compl_self.mp (hbp.trans (lowerProjection_le e hcompl)))

/-- An injective lattice homomorphism reflects order. -/
theorem le_of_image_le (e : CompleteLatticeHom B C)
    (he : Function.Injective e) {a b : B} (h : e a ≤ e b) : a ≤ b := by
  apply inf_eq_left.mp
  apply he
  rw [map_inf, inf_of_le_left h]

/-- An injective bottom-preserving homomorphism preserves nonzeroness. -/
theorem image_ne_bot (e : CompleteLatticeHom B C)
    (he : Function.Injective e) {b : B} (hb : b ≠ ⊥) : e b ≠ ⊥ := by
  intro h
  apply hb
  apply he
  simpa only [map_bot] using h

/-- Projecting a positive dense family along a complete embedding gives
a positive dense family on the source, with the same index type. -/
theorem projected_family_positive_dense (e : CompleteLatticeHom B C)
    (he : Function.Injective e) {I : Type} (d : I → C)
    (hd : ∀ i, d i ≠ ⊥)
    (hdense : ∀ c : C, c ≠ ⊥ → ∃ i, d i ≤ c) :
    (∀ i, lowerProjection e (d i) ≠ ⊥) ∧
      ∀ b : B, b ≠ ⊥ → ∃ i, lowerProjection e (d i) ≤ b := by
  refine ⟨fun i => lowerProjection_ne_bot e (hd i), ?_⟩
  intro b hb
  obtain ⟨i, hi⟩ := hdense (e b) (image_ne_bot e he hb)
  exact ⟨i, lowerProjection_le e hi⟩

/-- A representative of the projection is a regular-image reduction for
the composite map. Only the second map is required to be complete. -/
theorem isReduction_of_value_eq_lowerProjection {V : Type}
    (μ : BoundedLatticeHom (Set V) B) (e : CompleteLatticeHom B C)
    (he : Function.Injective e) {c : C} (hc : c ≠ ⊥)
    {A : Set V} (hA : μ A = lowerProjection e c) :
    IsReduction (e.toBoundedLatticeHom.comp μ) c A := by
  refine ⟨?_, ?_⟩
  · change e (μ A) ≠ ⊥
    rw [hA]
    exact image_ne_bot e he (lowerProjection_ne_bot e hc)
  · intro T hT hTA
    change e (μ T) ⊓ c ≠ ⊥
    apply inf_image_lowerProjection_ne_bot e
    · intro hzero
      apply hT
      change e (μ T) = ⊥
      rw [hzero, map_bot]
    · rw [← hA]
      exact le_of_image_le e he hTA

/-- A surjective finitary quotient map followed by a complete embedding
supplies a regular-image reduction of every nonzero target value. -/
theorem exists_reduction_of_complete_embedding {V : Type}
    (μ : BoundedLatticeHom (Set V) B) (hμ : Function.Surjective μ)
    (e : CompleteLatticeHom B C) (he : Function.Injective e)
    {c : C} (hc : c ≠ ⊥) :
    ∃ A : Set V, IsReduction (e.toBoundedLatticeHom.comp μ) c A := by
  obtain ⟨A, hA⟩ := hμ (lowerProjection e c)
  exact ⟨A, isReduction_of_value_eq_lowerProjection μ e he hc hA⟩

end Erdos1172Part4CompleteBooleanReduction
