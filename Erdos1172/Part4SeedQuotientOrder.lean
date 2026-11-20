/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanSeedKernelName
public import Erdos1172.Part4BooleanQuotientDenseSets
public import Erdos1172.Part4BooleanQuotientFactorization

@[expose] public section

/-! # Density over the source algebra and order modulo the seed ideal -/

set_option autoImplicit false
noncomputable section
open bSet Erdos1172BooleanFactor Erdos1172BooleanQuotient Erdos1172PositiveBoolean
open scoped Flypitch
universe u v

namespace Erdos1172SeedQuotient

variable {B C : Type u} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]
variable (e : CompleteLatticeHom B C)

private theorem local_order (b : B) (d c : C) :
    b ≤ (lowerProjection e (d ⊓ cᶜ))ᶜ ↔ d ⊓ e b ≤ c := by
  rw [le_compl_comm, lowerProjection_le_iff, map_compl']
  constructor
  · intro h
    have hd : Disjoint (d ⊓ cᶜ) (e b) := le_compl_iff_disjoint_right.mp h
    have hh : Disjoint (d ⊓ e b) cᶜ := disjoint_iff.mpr (by
      simpa only [inf_right_comm] using disjoint_iff.mp hd)
    simpa only [compl_compl] using le_compl_iff_disjoint_right.mpr hh
  · intro h
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff.mpr
    rw [inf_right_comm]
    exact disjoint_iff.mp (le_compl_iff_disjoint_right.mp
      (show d ⊓ e b ≤ cᶜᶜ by simpa only [compl_compl] using h))

/-- The family generates a dense set when its members can be strengthened
by conditions in the source algebra. -/
def denseOver {T : Type v} (d : T → C) : Prop :=
  ∀ c : C, c ≠ ⊥ → ∃ i : T, ∃ b : B, d i ⊓ e b ≠ ⊥ ∧ d i ⊓ e b ≤ c

theorem denseOver_iff {T : Type v} (d : T → C) :
    denseOver e d ↔ ∀ c : C, lowerProjection e c ≤
      ⨆ i, lowerProjection e (d i) ⊓ (lowerProjection e (d i ⊓ cᶜ))ᶜ := by
  classical
  constructor
  · intro hd c
    let R := ⨆ i, lowerProjection e (d i) ⊓ (lowerProjection e (d i ⊓ cᶜ))ᶜ
    by_contra hn
    let a := lowerProjection e c ⊓ Rᶜ
    have ha : a ≠ ⊥ := fun h => hn (by
      simpa only [compl_compl] using
        (le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr h) : lowerProjection e c ≤ Rᶜᶜ))
    obtain ⟨i, b, hp, hh⟩ := hd (e a ⊓ c) (inf_image_lowerProjection_ne_bot e ha inf_le_left)
    let p := d i ⊓ e b
    have hpa : lowerProjection e p ≤ a := lowerProjection_le e (hh.trans inf_le_left)
    have hpb : lowerProjection e p ≤ b := lowerProjection_le e inf_le_right
    have hR : lowerProjection e p ≤ R := le_iSup_of_le i
      (le_inf (lowerProjection_mono e inf_le_left) (hpb.trans ((local_order e b (d i) c).mpr
        (hh.trans inf_le_right))))
    exact lowerProjection_ne_bot e hp (bot_unique
      ((le_inf hR (hpa.trans inf_le_right)).trans inf_compl_eq_bot.le))
  · intro h c hc
    obtain ⟨i, hi⟩ : ∃ i, lowerProjection e (d i) ⊓ (lowerProjection e (d i ⊓ cᶜ))ᶜ ≠ ⊥ := by
      by_contra! hn
      exact lowerProjection_ne_bot e hc (bot_unique ((h c).trans_eq (iSup_eq_bot.mpr hn)))
    let b := (lowerProjection e (d i ⊓ cᶜ))ᶜ
    refine ⟨i, b, ?_, (local_order e b (d i) c).mp le_rfl⟩
    intro hz
    apply hi
    rw [← lowerProjection_inf_image, hz]
    exact lowerProjection_le e bot_le |>.antisymm bot_le

open bSet.ErdosIdeal bSet.ErdosSeedKernel

variable (j : bSet B → bSet C) (s : bSet C) (K : bSet B)
variable (hEq : ∀ X Y, e (X =ᴮ Y) ≤ (j X =ᴮ j Y))
variable (hDiff : ∀ X Y, (s ∈ᴮ j (difference X Y)) = (s ∈ᴮ j X) ⊓ (s ∈ᴮ j Y)ᶜ)

include hEq hDiff in
theorem loss_value (X Y : bSet B) (hx : (⊤ : B) ≤ X ⊆ᴮ K) :
    (difference X Y ∈ᴮ seedKernelName e j s K) =
      (lowerProjection e ((s ∈ᴮ j X) ⊓ (s ∈ᴮ j Y)ᶜ))ᶜ := by
  rw [← hDiff]
  change _ = nullValue e j s (difference X Y)
  apply eq_of_forall_le_iff
  intro b
  rw [mem_seedKernelName_iff e j s hEq, le_nullValue_iff]
  exact and_iff_right (subset_trans' difference_subset (le_top.trans hx))

include hEq hDiff in
theorem loss_eq_separativeLe (X Y : bSet B) (hx : (⊤ : B) ≤ X ⊆ᴮ K)
    (p q : Positive C) (hp : (s ∈ᴮ j X) = p.val) (hq : (s ∈ᴮ j Y) = q.val) :
    (difference X Y ∈ᴮ seedKernelName e j s K) =
      separativeLeValue (quotientName e) (check (upperSetCode p)) (check (upperSetCode q)) := by
  rw [loss_value e j s K hEq hDiff X Y hx, hp, hq, separativeLeValue_checked]

include hEq hDiff in
theorem seedFamily_covers {T : Type v} (X : T → bSet B)
    (hx : ∀ i, (⊤ : B) ≤ X i ⊆ᴮ K) (hd : denseOver e (fun i => s ∈ᴮ j (X i))) (A : bSet B) :
    positive K (seedKernelName e j s K) A ≤ ⨆ i,
      positive K (seedKernelName e j s K) (X i) ⊓ (difference (X i) A ∈ᴮ seedKernelName e j s K) := by
  simp only [positive_seedKernelName e j s hEq, loss_value e j s K hEq hDiff _ _ (hx _),
    top_unique (hx _), top_inf_eq]
  exact inf_le_right.trans ((denseOver_iff e _).mp hd (s ∈ᴮ j A))

end Erdos1172SeedQuotient
