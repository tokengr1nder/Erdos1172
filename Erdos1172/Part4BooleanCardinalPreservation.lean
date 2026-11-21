/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
module

public import Flypitch4.BvmExtras
public import Mathlib.SetTheory.Cardinal.Pigeonhole

@[expose] public section

/-!
# A Boolean chain condition rules out small ground-domain surjections

The positive-pair witness argument is adapted from Flypitch's cardinal
preservation proof. A purported surjection supplies a positive Boolean
value for every ground target representative. Regular-cardinal pigeonhole
then produces a large family of distinct outputs with the same input,
which functionality makes pairwise disjoint.

The target representatives must be pairwise inequivalent as pre-sets.
The chain condition is an explicit hypothesis here; applying this theorem
to a forcing requires proving that condition for the actual algebra.
This alone is not full cardinal preservation or a GCH/model construction.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCardinalPreservation

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- Each checked target representative has a positive functional pair witness.
No global choice of a ground-valued total function is asserted. -/
theorem positive_pair_witness {X Y : PSet.{u}} (f : bSet B) {Γ : B}
    (Hnonzero : ⊥ < Γ) (H : Γ ≤ is_surj_onto (check X) (check Y) f) :
    ∀ i : Y.Type, ∃ j : X.Type,
      ⊥ < is_func f ⊓ pair (check (X.Func j)) (check (Y.Func i)) ∈ᴮ f := by
  intro i
  have Hfunc : Γ ≤ is_func' (check X) (check Y) f := H.trans inf_le_left
  have Hsurj : Γ ≤ is_surj (check X) (check Y) f := H.trans inf_le_right
  have Hi : Γ ≤ ⨆ w, w ∈ᴮ check X ⊓ pair w (check (Y.Func i)) ∈ᴮ f := by
    have hs := Hsurj.trans (iInf_le (f := fun v => _root_.imp (v ∈ᴮ check Y)
      (⨆ w, w ∈ᴮ check X ⊓ pair w v ∈ᴮ f)) (check (Y.Func i)))
    exact (le_inf hs mem_check_of_mem).trans (imp_inf_le _ _)
  rw [← @bounded_exists B _ (check X)
    (fun w => pair w (check (Y.Func i)) ∈ᴮ f)
    (h_congr := B_ext_pair_mem_left)] at Hi
  simp only [check_bval_top, top_inf_eq] at Hi
  have Hpos : ⊥ < ⨆ j : (check X : bSet B).type,
      is_func f ⊓ pair ((check X : bSet B).func j) (check (Y.Func i)) ∈ᴮ f := by
    apply Hnonzero.trans_le
    calc Γ
        ≤ is_func' (check X) (check Y) f ⊓
            ⨆ j, pair ((check X).func j) (check (Y.Func i)) ∈ᴮ f := le_inf Hfunc Hi
      _ = ⨆ j, is_func' (check X) (check Y) f ⊓
            pair ((check X).func j) (check (Y.Func i)) ∈ᴮ f := inf_iSup_eq'
      _ ≤ ⨆ j, is_func f ⊓ pair ((check X).func j) (check (Y.Func i)) ∈ᴮ f :=
        iSup_mono fun _ => le_inf (is_func_of_is_func' inf_le_left) inf_le_right
  obtain ⟨j, Hj⟩ := nonzero_wit Hpos
  exact ⟨check_cast j, by rwa [← check_func]⟩

theorem fiber_pair_values_disjoint (X Y : PSet.{u}) (g : Y.Type → X.Type)
    (a : X.Type) (f : bSet B)
    (Hsep : ∀ i j : Y.Type, i ≠ j → ¬ PSet.Equiv (Y.Func i) (Y.Func j)) :
    ∀ j k : (g ⁻¹' {a}), j ≠ k →
      (is_func f ⊓ pair (check (X.Func (g j.val))) (check (Y.Func j.val)) ∈ᴮ f) ⊓
        (is_func f ⊓ pair (check (X.Func (g k.val))) (check (Y.Func k.val)) ∈ᴮ f) = ⊥ := by
  intro j k hjk
  apply eq_bot_iff.mpr
  let w : (g ⁻¹' {a}) → B := fun t =>
    is_func f ⊓ pair (check (X.Func (g t.val))) (check (Y.Func t.val)) ∈ᴮ f
  change w j ⊓ w k ≤ ⊥
  have Hfunc : w j ⊓ w k ≤ is_func f := inf_le_left.trans inf_le_left
  have Hj : w j ⊓ w k ≤
      pair (check (X.Func (g j.val))) (check (Y.Func j.val)) ∈ᴮ f :=
    inf_le_left.trans inf_le_right
  have Hk : w j ⊓ w k ≤
      pair (check (X.Func (g k.val))) (check (Y.Func k.val)) ∈ᴮ f :=
    inf_le_right.trans inf_le_right
  have hj : g j.val = a := j.property
  have hk : g k.val = a := k.property
  rw [hj] at Hj
  rw [hk] at Hk
  have Heq : w j ⊓ w k ≤ check (Y.Func j.val) =ᴮ check (Y.Func k.val) :=
    eq_of_is_func_of_eq Hfunc bv_refl Hj Hk
  exact Heq.trans_eq (check_bv_eq_bot_of_not_equiv (Hsep _ _ (fun h => hjk (Subtype.ext h))))

/-- A regular-cardinal chain condition prevents a surjection from a smaller
checked indexing set onto a separated checked indexing set of size at least κ. -/
theorem is_surj_onto_eq_bot {κ : Cardinal.{u}} (Hκ : κ.IsRegular)
    (Hcc : ∀ {J : Type u} (w : J → B), (∀ j, w j ≠ ⊥) →
      (∀ j k, j ≠ k → w j ⊓ w k = ⊥) → Cardinal.mk J < κ)
    (X Y : PSet.{u}) (HX : Cardinal.mk X.Type < κ)
    (HY : κ ≤ Cardinal.mk Y.Type)
    (Hsep : ∀ i j : Y.Type, i ≠ j → ¬ PSet.Equiv (Y.Func i) (Y.Func j))
    (f : bSet B) : is_surj_onto (check X) (check Y) f = (⊥ : B) := by
  classical
  by_contra Hne
  obtain ⟨g, Hg⟩ := Classical.axiomOfChoice
    (positive_pair_witness f (bot_lt_iff_ne_bot.mpr Hne) le_rfl)
  obtain ⟨a, Ha⟩ := Cardinal.infinite_pigeonhole_card g κ HY Hκ.aleph0_le (by rwa [Hκ.cof_ord])
  let w : (g ⁻¹' {a}) → B := fun j =>
    is_func f ⊓ pair (check (X.Func (g j.val))) (check (Y.Func j.val)) ∈ᴮ f
  have Hw : ∀ j, w j ≠ ⊥ := fun j => ne_of_gt (Hg j.val)
  have Hdisj : ∀ j k, j ≠ k → w j ⊓ w k = ⊥ := fiber_pair_values_disjoint X Y g a f Hsep
  exact (Hcc w Hw Hdisj).not_ge Ha

theorem surjects_onto_eq_bot {κ : Cardinal.{u}} (Hκ : κ.IsRegular)
    (Hcc : ∀ {J : Type u} (w : J → B), (∀ j, w j ≠ ⊥) →
      (∀ j k, j ≠ k → w j ⊓ w k = ⊥) → Cardinal.mk J < κ)
    (X Y : PSet.{u}) (HX : Cardinal.mk X.Type < κ)
    (HY : κ ≤ Cardinal.mk Y.Type)
    (Hsep : ∀ i j : Y.Type, i ≠ j → ¬ PSet.Equiv (Y.Func i) (Y.Func j)) :
    surjects_onto (check X) (check Y) = (⊥ : B) := by
  apply bot_unique
  apply iSup_le
  intro f
  exact (is_surj_onto_eq_bot Hκ Hcc X Y HX HY Hsep f).le

/-- Targets of size at least κ also cannot be collapsed from domains of
size between κ and the target. This uses a larger-fiber pigeonhole argument,
not regularity of the target cardinal. -/
theorem is_surj_onto_eq_bot_of_cardinal_lt {κ : Cardinal.{u}} (Hκ : κ.IsRegular)
    (Hcc : ∀ {J : Type u} (w : J → B), (∀ j, w j ≠ ⊥) →
      (∀ j k, j ≠ k → w j ⊓ w k = ⊥) → Cardinal.mk J < κ)
    (X Y : PSet.{u}) (Hlt : Cardinal.mk X.Type < Cardinal.mk Y.Type)
    (HY : κ ≤ Cardinal.mk Y.Type)
    (Hsep : ∀ i j : Y.Type, i ≠ j → ¬ PSet.Equiv (Y.Func i) (Y.Func j))
    (f : bSet B) : is_surj_onto (check X) (check Y) f = (⊥ : B) := by
  classical
  by_cases HX : Cardinal.mk X.Type < κ
  · exact is_surj_onto_eq_bot Hκ Hcc X Y HX HY Hsep f
  · have HXκ : κ ≤ Cardinal.mk X.Type := le_of_not_gt HX
    by_contra Hne
    obtain ⟨g, Hg⟩ := Classical.axiomOfChoice
      (positive_pair_witness f (bot_lt_iff_ne_bot.mpr Hne) le_rfl)
    obtain ⟨a, Ha⟩ := Cardinal.infinite_pigeonhole_card_lt g Hlt (Hκ.aleph0_le.trans HY)
    let w : (g ⁻¹' {a}) → B := fun j =>
      is_func f ⊓ pair (check (X.Func (g j.val))) (check (Y.Func j.val)) ∈ᴮ f
    have Hw : ∀ j, w j ≠ ⊥ := fun j => ne_of_gt (Hg j.val)
    have Hdisj : ∀ j k, j ≠ k → w j ⊓ w k = ⊥ := fiber_pair_values_disjoint X Y g a f Hsep
    exact (Hcc w Hw Hdisj).not_ge (HXκ.trans Ha.le)

theorem surjects_onto_eq_bot_of_cardinal_lt {κ : Cardinal.{u}} (Hκ : κ.IsRegular)
    (Hcc : ∀ {J : Type u} (w : J → B), (∀ j, w j ≠ ⊥) →
      (∀ j k, j ≠ k → w j ⊓ w k = ⊥) → Cardinal.mk J < κ)
    (X Y : PSet.{u}) (Hlt : Cardinal.mk X.Type < Cardinal.mk Y.Type)
    (HY : κ ≤ Cardinal.mk Y.Type)
    (Hsep : ∀ i j : Y.Type, i ≠ j → ¬ PSet.Equiv (Y.Func i) (Y.Func j)) :
    surjects_onto (check X) (check Y) = (⊥ : B) := by
  apply bot_unique
  apply iSup_le
  intro f
  exact (is_surj_onto_eq_bot_of_cardinal_lt Hκ Hcc X Y Hlt HY Hsep f).le

end bSet.ErdosCardinalPreservation
