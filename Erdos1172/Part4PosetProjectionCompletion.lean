/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4PosetBooleanCompletion
public import Mathlib.Order.Hom.CompleteLattice

@[expose] public section

/-!
# Complete Boolean maps from actual forcing projections

Inverse image along a monotone map with exact strengthening lifts commutes
with the pseudocomplement of lower sets. It therefore gives an actual
complete Boolean homomorphism of regular completions. Surjectivity of the
condition map makes this homomorphism injective.

No generic filter, chain condition, cardinal preservation, or ideal is
asserted. The strengthening-lift hypothesis must be proved for each
concrete forcing projection.
-/

set_option autoImplicit false

noncomputable section

universe u v

namespace Erdos1172PosetProjection

open Erdos1172PosetCompletion

variable {P : Type u} {Q : Type v} [Preorder P] [Preorder Q]

def ExactLifts (π : P →o Q) : Prop :=
  ∀ p q, q ≤ π p → ∃ r, r ≤ p ∧ π r = q

def pullback (π : P →o Q) (A : LowerSet Q) : LowerSet P :=
  ⟨π ⁻¹' (A : Set Q), A.lower.preimage π.monotone⟩

@[simp] theorem mem_pullback (π : P →o Q) (A : LowerSet Q) (p : P) :
    p ∈ pullback π A ↔ π p ∈ A := Iff.rfl

theorem pullback_compl (π : P →o Q) (H : ExactLifts π) (A : LowerSet Q) :
    pullback π Aᶜ = (pullback π A)ᶜ := by
  apply SetLike.ext
  intro p
  rw [mem_pullback, mem_pseudocompl_iff, mem_pseudocompl_iff]
  constructor
  · intro h r hr
    exact h (π r) (π.monotone hr)
  · intro h q hq hA
    obtain ⟨r, hr, hπ⟩ := H p q hq
    apply h r hr
    change π r ∈ A
    exact hπ.symm ▸ hA

theorem pullback_regular (π : P →o Q) (H : ExactLifts π)
    (A : LowerSet Q) (hA : Heyting.IsRegular A) :
    Heyting.IsRegular (pullback π A) := by
  change (pullback π A)ᶜᶜ = pullback π A
  rw [← pullback_compl π H, ← pullback_compl π H, hA.eq]

def regularPullback (π : P →o Q) (H : ExactLifts π)
    (b : Completion Q) : Completion P :=
  ⟨pullback π b.val, pullback_regular π H b.val b.prop⟩

@[simp] theorem mem_regularPullback (π : P →o Q) (H : ExactLifts π)
    (b : Completion Q) (p : P) :
    p ∈ (regularPullback π H b).val ↔ π p ∈ b.val := Iff.rfl

theorem regularPullback_compl (π : P →o Q) (H : ExactLifts π)
    (b : Completion Q) :
    regularPullback π H bᶜ = (regularPullback π H b)ᶜ :=
  Heyting.Regular.coe_injective (pullback_compl π H b.val)

theorem mem_sInf_completion (S : Set (Completion P)) (p : P) :
    p ∈ (sInf S).val ↔ ∀ b ∈ S, p ∈ b.val := by
  simp only [← condition_le_iff, le_sInf_iff]

theorem regularPullback_sInf (π : P →o Q) (H : ExactLifts π)
    (S : Set (Completion Q)) :
    regularPullback π H (sInf S) = sInf (regularPullback π H '' S) := by
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro p
  simp only [mem_regularPullback, mem_sInf_completion, Set.forall_mem_image]

theorem regularPullback_sSup (π : P →o Q) (H : ExactLifts π)
    (S : Set (Completion Q)) :
    regularPullback π H (sSup S) = sSup (regularPullback π H '' S) := by
  apply compl_injective
  rw [← regularPullback_compl, compl_sSup', regularPullback_sInf, compl_sSup',
    Set.image_image, Set.image_image]
  simp only [regularPullback_compl]

/-- This map is constructed by inverse image, not assumed as input. -/
def completionHom (π : P →o Q) (H : ExactLifts π) :
    CompleteLatticeHom (Completion Q) (Completion P) where
  toFun := regularPullback π H
  map_sSup' := regularPullback_sSup π H
  map_sInf' := regularPullback_sInf π H

theorem completionHom_injective (π : P →o Q) (H : ExactLifts π)
    (hπ : Function.Surjective π) : Function.Injective (completionHom π H) := by
  intro b c h
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro q
  obtain ⟨p, rfl⟩ := hπ q
  change p ∈ (completionHom π H b).val ↔ p ∈ (completionHom π H c).val
  rw [h]

theorem condition_le_completionHom_iff (π : P →o Q) (H : ExactLifts π)
    (p : P) (b : Completion Q) :
    condition p ≤ completionHom π H b ↔ condition (π p) ≤ b := by
  simp only [condition_le_iff]
  rfl

end Erdos1172PosetProjection
