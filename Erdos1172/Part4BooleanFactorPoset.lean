/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Order.Hom.BoundedLattice
public import Mathlib.Order.CompleteBooleanAlgebra
public import Erdos1172.Part4PositiveBooleanCompletion

@[expose] public section

/-!
# A factor poset for a complete Boolean homomorphism

A condition consists of positive source and target values compatible under
the lower projection. Evaluating the condition intersects its target with
the image of its source. A canonical monotone section gives exact lifts of
all strengthenings.
-/

set_option autoImplicit false

noncomputable section

universe u v

namespace Erdos1172BooleanFactor

open Erdos1172PositiveBoolean Erdos1172PosetProjection

variable {B : Type u} {C : Type v}
variable [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

/-- Least source value whose image lies above the target value. -/
def lowerProjection (e : CompleteLatticeHom B C) (c : C) : B :=
  sInf {b : B | c ≤ e b}

theorem le_image_lowerProjection (e : CompleteLatticeHom B C) (c : C) :
    c ≤ e (lowerProjection e c) := by
  rw [lowerProjection, map_sInf]
  refine le_sInf ?_
  rintro _ ⟨b, hb, rfl⟩
  exact hb

theorem lowerProjection_le (e : CompleteLatticeHom B C) {c : C} {b : B}
    (h : c ≤ e b) : lowerProjection e c ≤ b :=
  sInf_le h

theorem lowerProjection_le_iff (e : CompleteLatticeHom B C) {c : C} {b : B} :
    lowerProjection e c ≤ b ↔ c ≤ e b :=
  ⟨fun h => (le_image_lowerProjection e c).trans (OrderHomClass.mono e h),
    lowerProjection_le e⟩

theorem lowerProjection_mono (e : CompleteLatticeHom B C) :
    Monotone (lowerProjection e) := by
  intro c d hcd
  exact lowerProjection_le e (hcd.trans (le_image_lowerProjection e d))

theorem lowerProjection_ne_bot (e : CompleteLatticeHom B C)
    {c : C} (hc : c ≠ ⊥) : lowerProjection e c ≠ ⊥ := by
  intro h
  apply hc
  apply le_antisymm _ bot_le
  simpa only [h, map_bot] using le_image_lowerProjection e c

theorem inf_image_lowerProjection_ne_bot (e : CompleteLatticeHom B C)
    {c : C} {b : B} (hb : b ≠ ⊥) (hbp : b ≤ lowerProjection e c) :
    e b ⊓ c ≠ ⊥ := by
  intro hzero
  have hcompl : c ≤ e (bᶜ) := by
    rw [map_compl']
    exact le_compl_iff_disjoint_left.mpr (disjoint_iff.mpr hzero)
  exact hb (le_compl_self.mp (hbp.trans (lowerProjection_le e hcompl)))

structure FactorCondition (e : CompleteLatticeHom B C) : Type (max u v) where
  source : B
  target : C
  source_ne_bot : source ≠ ⊥
  target_ne_bot : target ≠ ⊥
  compatible : source ≤ lowerProjection e target

@[ext] theorem FactorCondition.ext {e : CompleteLatticeHom B C}
    {p q : FactorCondition e} (hs : p.source = q.source) (ht : p.target = q.target) :
    p = q := by
  cases p
  cases q
  cases hs
  cases ht
  rfl

instance factorConditionPartialOrder (e : CompleteLatticeHom B C) :
    PartialOrder (FactorCondition e) where
  le p q := p.source ≤ q.source ∧ p.target ≤ q.target
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ hpq hqr := ⟨hpq.1.trans hqr.1, hpq.2.trans hqr.2⟩
  le_antisymm _ _ hpq hqp :=
    FactorCondition.ext (le_antisymm hpq.1 hqp.1) (le_antisymm hpq.2 hqp.2)

def evaluation (e : CompleteLatticeHom B C) : FactorCondition e →o Positive C where
  toFun p := ⟨e p.source ⊓ p.target,
    inf_image_lowerProjection_ne_bot e p.source_ne_bot p.compatible⟩
  monotone' := fun _ _ h => inf_le_inf (OrderHomClass.mono e h.1) h.2

def canonicalSection (e : CompleteLatticeHom B C) : Positive C →o FactorCondition e where
  toFun c := ⟨lowerProjection e c.val, c.val,
    lowerProjection_ne_bot e c.property, c.property, le_rfl⟩
  monotone' := fun _ _ h => ⟨lowerProjection_mono e h, h⟩

theorem evaluation_section (e : CompleteLatticeHom B C) (c : Positive C) :
    evaluation e (canonicalSection e c) = c := by
  apply Subtype.ext
  change e (lowerProjection e c.val) ⊓ c.val = c.val
  exact inf_eq_right.mpr (le_image_lowerProjection e c.val)

theorem section_evaluation_le (e : CompleteLatticeHom B C) (p : FactorCondition e) :
    canonicalSection e (evaluation e p) ≤ p := by
  exact ⟨lowerProjection_le e inf_le_left, inf_le_right⟩

end Erdos1172BooleanFactor
