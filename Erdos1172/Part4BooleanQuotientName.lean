/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanFactorPoset
public import Erdos1172.Part4BooleanNameIteration

@[expose] public section

/-! # The canonical name for the quotient conditions

We code each positive Boolean value by the set of ordinal labels of
its upper bounds. Reverse inclusion of the checked codes then computes
the order on positive conditions. The coefficient of each code in the
quotient name is its lower projection to the first Boolean algebra.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch

universe u

namespace Erdos1172BooleanQuotient

open bSet Erdos1172PositiveBoolean Erdos1172BooleanFactor

/-- Distinct ground ordinal labels for the positive target values. -/
def ordinalLabelEmbedding (C : Type u) [NontrivialCompleteBooleanAlgebra C] :
    Positive C ↪ (PSet.ordinalMk (Cardinal.mk (Positive C)).ord).Type := by
  have Hcard : Cardinal.mk (Positive C) ≤
      Cardinal.mk (PSet.ordinalMk (Cardinal.mk (Positive C)).ord).Type := by
    simpa only [PSet.ordinalMk_type, Cardinal.mk_ord_toType] using
      (le_rfl : Cardinal.mk (Positive C) ≤ Cardinal.mk (Positive C))
  exact Classical.choice ((Cardinal.le_def (Positive C)
    (PSet.ordinalMk (Cardinal.mk (Positive C)).ord).Type).mp Hcard)

variable {B C : Type u}
variable [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

private theorem eq_of_ordinalLabel_equiv {c d : Positive C}
    (H : PSet.Equiv
      ((PSet.ordinalMk (Cardinal.mk (Positive C)).ord).Func (ordinalLabelEmbedding C c))
      ((PSet.ordinalMk (Cardinal.mk (Positive C)).ord).Func (ordinalLabelEmbedding C d))) :
    c = d := by
  classical
  apply (ordinalLabelEmbedding C).injective
  by_contra Hne
  exact PSet.ordinalMk_inj (Cardinal.mk (Positive C)).ord
    (ordinalLabelEmbedding C c) (ordinalLabelEmbedding C d) Hne H

/-- The ground set of labels of positive values above `c`. -/
def upperSetCode (c : Positive C) : PSet.{u} :=
  .mk {d : Positive C // c ≤ d} (fun d =>
    (PSet.ordinalMk (Cardinal.mk (Positive C)).ord).Func
      (ordinalLabelEmbedding C d.val))

theorem upperSetCode_subset_iff (c d : Positive C) : upperSetCode d ⊆ upperSetCode c ↔ c ≤ d := by
  constructor
  · intro Hsub
    obtain ⟨z, Hz⟩ := Hsub (show (upperSetCode d).Type from ⟨d, le_rfl⟩)
    have Hdz : d = z.val := eq_of_ordinalLabel_equiv Hz
    have Hcz : c ≤ z.val := z.property
    rwa [← Hdz] at Hcz
  · intro Hcd z
    exact ⟨⟨z.val, Hcd.trans z.property⟩, PSet.Equiv.refl _⟩

theorem check_upperSetCode_subset_eq_top {c d : Positive C} (Hcd : c ≤ d) :
    ((check (upperSetCode d) : bSet B) ⊆ᴮ check (upperSetCode c)) = ⊤ :=
  top_unique (check_subset_of_subset ((upperSetCode_subset_iff c d).mpr Hcd))

theorem check_upperSetCode_subset_eq_bot {c d : Positive C} (Hcd : ¬ c ≤ d) :
    ((check (upperSetCode d) : bSet B) ⊆ᴮ check (upperSetCode c)) = ⊥ := by
  have Hnot : ¬ upperSetCode d ⊆ upperSetCode c := fun H => Hcd ((upperSetCode_subset_iff c d).mp H)
  have Hneg : (⊤ : B) ≤
      ((check (upperSetCode d) : bSet B) ⊆ᴮ check (upperSetCode c))ᶜ :=
    check_not_subset Hnot
  simpa only [compl_compl, compl_top] using congrArg compl (top_unique Hneg)

theorem check_upperSetCode_subset_iff {c d : Positive C} {Γ : B} (HΓ : Γ ≠ ⊥) :
    (Γ ≤ (check (upperSetCode d) : bSet B) ⊆ᴮ check (upperSetCode c)) ↔ c ≤ d := by
  classical
  constructor
  · intro H
    by_contra Hnot
    rw [check_upperSetCode_subset_eq_bot Hnot] at H
    exact HΓ (bot_unique H)
  · intro H
    rw [check_upperSetCode_subset_eq_top H]
    exact le_top

def quotientName (e : CompleteLatticeHom B C) : bSet B :=
  .mk (Positive C) (fun c => check (upperSetCode c))
    (fun c => lowerProjection e c.val)

theorem lowerProjection_top (e : CompleteLatticeHom B C) (he : Function.Injective e) :
    lowerProjection e (⊤ : C) = ⊤ := by
  apply he
  rw [map_top]
  exact top_unique (le_image_lowerProjection e (⊤ : C))

def topLabel (C : Type u) [NontrivialCompleteBooleanAlgebra C] : Positive C :=
  ⟨⊤, top_ne_bot⟩

end Erdos1172BooleanQuotient
