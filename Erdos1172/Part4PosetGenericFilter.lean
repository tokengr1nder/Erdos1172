/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanQuotientName
public import Erdos1172.Part4BooleanNameTransport

@[expose] public section

/-!
# Generic filter names and projections of forcing conditions

Positive Boolean values have ground ordinal labels. The canonical generic
filter gives each label its own Boolean weight. Its actual restriction
along an embedding reads membership in the upper generic at the image.
For a projection of presenting posets, membership of a small condition
is the join of upper generic memberships over genuine refinements.
-/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
universe u

namespace Erdos1172PosetGeneric

open bSet ErdosNameTransport Erdos1172PositiveBoolean Erdos1172BooleanQuotient Erdos1172PosetCompletion Erdos1172PosetProjection

section Presentation

variable {P Q : Type u} [Preorder P] [Preorder Q]

def positiveCondition (p : P) : Positive (Completion P) := ⟨condition p, condition_ne_bot p⟩

private theorem projected_cone_refinement (π : P →o Q) (H : ExactLifts π) (q : Q) (p : P)
    (hp : condition p ≤ Erdos1172PosetProjection.completionHom π H (condition q)) :
    ∃ r : P, r ≤ p ∧ π r ≤ q := by
  have h : condition (π p) ≤ condition q :=
    (condition_le_completionHom_iff π H p (condition q)).mp hp
  have hm : π p ∈ (condition q).val := condition_le_iff.mp h
  obtain ⟨t, htp, htq⟩ := (mem_condition_iff q (π p)).mp hm (π p) le_rfl
  obtain ⟨r, hrp, hrt⟩ := H p t htp
  exact ⟨r, hrp, hrt.le.trans htq⟩

/-- The actual join of the projected cone, including upper conditions
whose projections lie strictly below the given lower condition. -/
theorem completionHom_condition_eq_iSup (π : P →o Q) (H : ExactLifts π) (q : Q) :
    Erdos1172PosetProjection.completionHom π H (condition q) =
      ⨆ r : {r : P // π r ≤ q}, condition r.val := by
  let x := ⨆ r : {r : P // π r ≤ q}, condition r.val
  apply le_antisymm
  · change (Erdos1172PosetProjection.completionHom π H (condition q)).val ≤ x.val
    intro p hp
    have hp' : condition p ≤ Erdos1172PosetProjection.completionHom π H (condition q) :=
      condition_le_iff.mpr hp
    change p ∈ x.val
    rw [← x.prop.eq]
    apply (mem_regularization_iff x.val p).mpr
    intro r hr
    obtain ⟨t, htr, htq⟩ := projected_cone_refinement π H q r ((condition_mono hr).trans hp')
    refine ⟨t, htr, condition_le_iff.mp ?_⟩
    exact le_iSup (fun t : {t : P // π t ≤ q} => condition t.val) ⟨t, htq⟩
  · apply iSup_le
    intro r
    exact (condition_le_completionHom_iff π H r.val (condition q)).mpr (condition_mono r.property)

-- The underlying complete Boolean algebra is the one used by condition.
local instance genericCompletionNCBA (I : Type u) [Preorder I] [Nonempty I] :
    NontrivialCompleteBooleanAlgebra (Completion I) where
  toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra
  bot_lt_top := bot_lt_top

end Presentation
end Erdos1172PosetGeneric
