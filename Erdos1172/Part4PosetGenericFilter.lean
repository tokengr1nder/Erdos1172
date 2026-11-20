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

open bSet ErdosNameTransport Erdos1172PositiveBoolean Erdos1172BooleanQuotient
  Erdos1172PosetCompletion Erdos1172PosetProjection

section Boolean

variable {B C : Type u} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

def genericLabel (p : Positive B) : PSet.{u} :=
  (PSet.ordinalMk (Cardinal.mk (Positive B)).ord).Func (ordinalLabelEmbedding B p)

theorem genericLabel_separated {p q : Positive B} (h : p ≠ q) :
    ¬ PSet.Equiv (genericLabel p) (genericLabel q) :=
  PSet.ordinalMk_inj (Cardinal.mk (Positive B)).ord _ _ (fun he => h ((ordinalLabelEmbedding B).injective he))

def genericFilterName (B : Type u) [NontrivialCompleteBooleanAlgebra B] : bSet B :=
  .mk (Positive B) (fun p => check (genericLabel p)) Subtype.val

/-- Separation of the checked labels identifies the full membership value. -/
theorem genericFilterName_mem (p : Positive B) :
    (check (genericLabel p) ∈ᴮ genericFilterName B) = p.val := by
  apply le_antisymm _ (mem_mk' (genericFilterName B) p)
  rw [mem_unfold]
  apply iSup_le
  intro q
  change q.val ⊓ ((check (genericLabel p) : bSet B) =ᴮ check (genericLabel q)) ≤ p.val
  by_cases h : p = q
  · subst q
    exact inf_le_left
  · rw [check_bv_eq_bot_of_not_equiv (genericLabel_separated h), inf_bot_eq]
    exact bot_le

theorem genericFilter_upward {p q : Positive B} (h : p ≤ q) :
    (check (genericLabel p) ∈ᴮ genericFilterName B) ≤ check (genericLabel q) ∈ᴮ genericFilterName B := by
  simpa only [genericFilterName_mem] using (show p.val ≤ q.val from h)

theorem genericFilter_directed (p q : Positive B) :
    (check (genericLabel p) ∈ᴮ genericFilterName B) ⊓ (check (genericLabel q) ∈ᴮ genericFilterName B) =
      ⨆ r : {r : Positive B // r ≤ p ∧ r ≤ q}, check (genericLabel r.val) ∈ᴮ genericFilterName B := by
  simp only [genericFilterName_mem]
  apply le_antisymm _ (iSup_le fun r => le_inf r.property.1 r.property.2)
  by_cases h : p.val ⊓ q.val = ⊥
  · exact h.le.trans bot_le
  · exact le_iSup_of_le ⟨⟨p.val ⊓ q.val, h⟩, inf_le_left, inf_le_right⟩ le_rfl

def positiveImage (e : CompleteLatticeHom B C) (he : Function.Injective e) (p : Positive B) :
    Positive C :=
  ⟨e p.val, fun hz => p.property (he (hz.trans (map_bot e).symm))⟩

/-- Pull back the actual upper generic by querying image membership for
each checked small label. -/
def restrictedGenericName (e : CompleteLatticeHom B C) (he : Function.Injective e) : bSet C :=
  .mk (Positive B) (fun p => check (genericLabel p))
    (fun p => check (genericLabel (positiveImage e he p)) ∈ᴮ genericFilterName C)

theorem map_genericFilterName (e : CompleteLatticeHom B C) (he : Function.Injective e) :
    mapNames e (genericFilterName B) = restrictedGenericName e he := by
  unfold genericFilterName restrictedGenericName
  rw [mapNames_mk]
  simp only [map_check]
  change bSet.mk (Positive B) (fun p => check (genericLabel p)) (fun p => e p.val) =
    bSet.mk (Positive B) (fun p => check (genericLabel p))
      (fun p => check (genericLabel (positiveImage e he p)) ∈ᴮ genericFilterName C)
  simp only [genericFilterName_mem]
  rfl

theorem mapped_genericFilterName_mem (e : CompleteLatticeHom B C) (p : Positive B) :
    (check (genericLabel p) ∈ᴮ mapNames e (genericFilterName B)) = e p.val := by
  have h := map_mem e (check (genericLabel p)) (genericFilterName B)
  rw [genericFilterName_mem, map_check] at h
  exact h.symm

end Boolean

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

variable [Nonempty P] [Nonempty Q]

/-- A ground dense set of presentation conditions, encoded by their Boolean
condition labels, is met at Boolean value top. -/
theorem genericFilter_meets_dense (D : Set P) (hD : ∀ p, ∃ q ∈ D, q ≤ p) :
    (⊤ : Completion P) ≤ ⨆ x : bSet (Completion P),
      x ∈ᴮ check (PSet.mk D (fun p => genericLabel (positiveCondition p.val))) ⊓
      x ∈ᴮ genericFilterName (Completion P) := by
  rw [← iSup_condition_eq_top_of_dense D hD]
  apply iSup_le
  intro p
  apply le_iSup_of_le (check (genericLabel (positiveCondition p.val)))
  apply le_inf (check_mem (PSet.func_mem (PSet.mk D (fun p => genericLabel (positiveCondition p.val))) p))
  exact (genericFilterName_mem (positiveCondition p.val)).ge

theorem mapped_generic_condition_membership (π : P →o Q) (H : ExactLifts π) (q : Q) :
    (check (genericLabel (positiveCondition q)) ∈ᴮ
      mapNames (Erdos1172PosetProjection.completionHom π H) (genericFilterName (Completion Q))) =
    ⨆ r : {r : P // π r ≤ q}, check (genericLabel (positiveCondition r.val)) ∈ᴮ
      genericFilterName (Completion P) := by
  simp only [mapped_genericFilterName_mem, genericFilterName_mem]
  exact completionHom_condition_eq_iSup π H q

end Presentation
end Erdos1172PosetGeneric
