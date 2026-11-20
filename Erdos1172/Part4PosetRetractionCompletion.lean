/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4PosetProjectionCompletion

@[expose] public section

/-!
# Regular completion of a strengthening retraction

Suppose `π (s q) = q` and `s (π p) ≤ p`. On regular lower sets,
pullback along `s` inverts the complete Boolean homomorphism induced by `π`.
The second identity on regular sets follows from density of the canonical
strengthenings below each condition.
-/

set_option autoImplicit false

noncomputable section

universe u v

namespace Erdos1172PosetProjection

open Erdos1172PosetCompletion

variable {P : Type u} {Q : Type v} [Preorder P] [Preorder Q]

theorem pullback_section_compl (π : P →o Q) (s : Q →o P)
    (Hπs : ∀ q, π (s q) = q) (Hsπ : ∀ p, s (π p) ≤ p) (A : LowerSet P) :
    pullback s Aᶜ = (pullback s A)ᶜ := by
  apply SetLike.ext
  intro q
  rw [mem_pullback, mem_pseudocompl_iff, mem_pseudocompl_iff]
  constructor
  · intro h r hr
    exact h (s r) (s.monotone hr)
  · intro h p hp hpA
    have Hπp : π p ≤ q := by simpa only [Hπs q] using π.monotone hp
    exact h (π p) Hπp (A.lower (Hsπ p) hpA)

theorem pullback_section_regular (π : P →o Q) (s : Q →o P)
    (Hπs : ∀ q, π (s q) = q) (Hsπ : ∀ p, s (π p) ≤ p)
    (A : LowerSet P) (HA : Heyting.IsRegular A) : Heyting.IsRegular (pullback s A) := by
  change (pullback s A)ᶜᶜ = pullback s A
  rw [← pullback_section_compl π s Hπs Hsπ, ← pullback_section_compl π s Hπs Hsπ, HA.eq]

theorem mem_regular_retraction_iff (π : P →o Q) (s : Q →o P)
    (Hsπ : ∀ p, s (π p) ≤ p) (A : Completion P) (p : P) :
    p ∈ A.val ↔ s (π p) ∈ A.val := by
  constructor
  · exact A.val.lower (Hsπ p)
  · intro hp
    have hd : p ∈ (A.valᶜᶜ : LowerSet P) := by
      apply (mem_regularization_iff A.val p).mpr
      intro r hr
      exact ⟨s (π r), Hsπ r, A.val.lower (s.monotone (π.monotone hr)) hp⟩
    rwa [A.prop.eq] at hd

/-- The inverse is literal preimage of a regular lower set along the section. -/
def sectionRegularPullback (π : P →o Q) (s : Q →o P)
    (Hπs : ∀ q, π (s q) = q) (Hsπ : ∀ p, s (π p) ≤ p) : Completion P →o Completion Q where
  toFun A := ⟨pullback s A.val, pullback_section_regular π s Hπs Hsπ A.val A.prop⟩
  monotone' := by
    intro A B h q hq
    exact h (show s q ∈ A.val from hq)

theorem sectionRegularPullback_regularPullback (π : P →o Q) (H : ExactLifts π)
    (s : Q →o P) (Hπs : ∀ q, π (s q) = q) (Hsπ : ∀ p, s (π p) ≤ p)
    (A : Completion Q) :
    sectionRegularPullback π s Hπs Hsπ (regularPullback π H A) = A := by
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro q
  change π (s q) ∈ A.val ↔ q ∈ A.val
  rw [Hπs q]

theorem regularPullback_sectionRegularPullback (π : P →o Q) (H : ExactLifts π)
    (s : Q →o P) (Hπs : ∀ q, π (s q) = q) (Hsπ : ∀ p, s (π p) ≤ p)
    (A : Completion P) :
    regularPullback π H (sectionRegularPullback π s Hπs Hsπ A) = A := by
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro p
  exact (mem_regular_retraction_iff π s Hsπ A p).symm

/-- This equivalence has the original projection homomorphism as its forward map. -/
def retractionCompletionOrderIso (π : P →o Q) (H : ExactLifts π) (s : Q →o P)
    (Hπs : ∀ q, π (s q) = q) (Hsπ : ∀ p, s (π p) ≤ p) : Completion Q ≃o Completion P :=
  OrderIso.ofHomInv
    (⟨completionHom π H, fun _ _ h => OrderHomClass.mono (completionHom π H) h⟩)
    (sectionRegularPullback π s Hπs Hsπ)
    (DFunLike.ext _ _ (regularPullback_sectionRegularPullback π H s Hπs Hsπ))
    (DFunLike.ext _ _ (sectionRegularPullback_regularPullback π H s Hπs Hsπ))

@[simp] theorem retractionCompletionOrderIso_apply (π : P →o Q) (H : ExactLifts π)
    (s : Q →o P) (Hπs : ∀ q, π (s q) = q) (Hsπ : ∀ p, s (π p) ≤ p)
    (A : Completion Q) : retractionCompletionOrderIso π H s Hπs Hsπ A = completionHom π H A := rfl

end Erdos1172PosetProjection
