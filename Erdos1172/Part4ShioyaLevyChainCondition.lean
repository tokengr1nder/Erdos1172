/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaLevyProduct

@[expose] public section

/-! # The chain condition of the small-support Lévy product

At each cut below θ, choose representatives for the possible restrictions.
A closure along a regular cardinal below θ contains the supports of its
representatives. One condition outside the closure has its overlap with
the closure captured at a single step. Its representative there agrees
on the entire common support.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Erdos1172Shioya.LevyProduct

variable {κ θ ρ : Cardinal.{u}}

private theorem strict_bound {D : Type u} (hρ : ρ.IsRegular) (hD : Cardinal.mk D < ρ)
    (f : D → ρ.ord.ToType) : ∃ b, ∀ i, f i < b := by
  by_contra! h
  have hc : IsCofinal (Set.range f) := by
    intro a
    obtain ⟨i, hi⟩ := h a
    exact ⟨f i, Set.mem_range_self i, hi⟩
  have hh := Order.cof_le hc
  rw [Ordinal.cof_toType, hρ.cof_ord] at hh
  exact hD.not_ge (hh.trans Cardinal.mk_range_le)

private theorem exists_cut_sequence (hθ : θ.IsRegular) (hρθ : ρ < θ)
    (step : θ.ord.ToType → θ.ord.ToType) :
    ∃ v : ρ.ord.ToType → θ.ord.ToType, ∀ i j, j < i → step (v j) < v i := by
  have hs (i : ρ.ord.ToType) : Cardinal.mk (Set.Iio i) < θ :=
    (show Cardinal.mk (Set.Iio i) < ρ by simpa using Cardinal.mk_Iio_lt i (by simp)).trans hρθ
  let next (i : ρ.ord.ToType) (prior : ∀ j, j < i → θ.ord.ToType) : θ.ord.ToType :=
    (strict_bound hθ (hs i) (fun j : Set.Iio i => step (prior j.val j.property))).choose
  let v : ρ.ord.ToType → θ.ord.ToType := wellFounded_lt.fix next
  refine ⟨v, fun i j hji => ?_⟩
  have he : v i = next i (fun j _ => v j) := WellFounded.fix_eq _ _ _
  exact he ▸ (strict_bound hθ (hs i) (fun j : Set.Iio i => step (v j.val))).choose_spec ⟨j,hji⟩

/-- Two indices agree on a bounded code whose cut contains all of their common support.
The cardinal of possible codes may grow with the cut. -/
theorem exists_pair_agree_on_common_support (hθ : θ.IsRegular) (hρ : ρ.IsRegular) (hρθ : ρ < θ)
    (supp : θ.ord.ToType → Set θ.ord.ToType) (hs : ∀ i, Cardinal.mk (supp i) < ρ)
    {C : θ.ord.ToType → Type u} (code : ∀ cut, θ.ord.ToType → C cut)
    (hc : ∀ cut, Cardinal.mk (C cut) < θ) :
    ∃ a b : θ.ord.ToType, a < b ∧ ∃ cut,
      code cut a = code cut b ∧ supp a ∩ supp b ⊆ Set.Iio cut := by
  classical
  choose stop hstop using fun i => strict_bound hθ ((hs i).trans hρθ) (fun x : supp i => x.val)
  let rep (cut : θ.ord.ToType) (v : Set.range (code cut)) := v.property.choose
  have rep_spec (cut : θ.ord.ToType) (v : Set.range (code cut)) : code cut (rep cut v) = v.val :=
    v.property.choose_spec
  choose step hstep using fun cut => strict_bound hθ
    ((Cardinal.mk_set_le (Set.range (code cut))).trans_lt (hc cut))
    (fun v : Set.range (code cut) => max (rep cut v) (stop (rep cut v)))
  obtain ⟨v, hv⟩ := exists_cut_sequence hθ hρθ step
  obtain ⟨b, hb⟩ := strict_bound hθ ((Cardinal.mk_ord_toType ρ).trans_lt hρθ) (fun i => step (v i))
  let inside : Set θ.ord.ToType := {x | ∃ i, x < step (v i)}
  let overlap := supp b ∩ inside
  have ho : Cardinal.mk overlap < ρ := (Cardinal.mk_le_mk_of_subset Set.inter_subset_left).trans_lt (hs b)
  choose witness hw using fun x : overlap => x.property.2
  obtain ⟨i, hi⟩ := strict_bound hρ ho witness
  let c : Set.range (code (v i)) := ⟨code (v i) b, Set.mem_range_self b⟩
  let a := rep (v i) c
  have ha : max a (stop a) < step (v i) := hstep (v i) c
  refine ⟨a, b, ((le_max_left _ _).trans_lt ha).trans (hb i), v i, rep_spec _ c, ?_⟩
  intro x hx
  have hxIn : x ∈ inside := ⟨i, (hstop a ⟨x,hx.1⟩).trans ((le_max_right _ _).trans_lt ha)⟩
  let y : overlap := ⟨x, hx.2, hxIn⟩
  exact (hw y).trans (hv i (witness y) (hi y))

open Erdos1172PosetCompletion

/-- The small-support product on any set of coordinates has the θ-chain
condition whenever each alphabet has cardinality below θ. -/
theorem family_compatible_pair (hθ : θ.IsInaccessible) (hκθ : κ < θ)
    (hκ : Cardinal.aleph0 ≤ κ) {A : Index θ → Type u} {S : Set (Index θ)}
    (hA : ∀ i, Cardinal.mk (A i) < θ) {J : Type u} (f : J → Family κ A S)
    (hJ : θ ≤ Cardinal.mk J) :
    ∃ a b : J, a ≠ b ∧ ∃ r, r ≤ f a ∧ r ≤ f b := by
  obtain ⟨label⟩ : Nonempty (Index θ ↪ J) :=
    (Cardinal.mk_ord_toType θ).le.trans hJ
  let p (i : Index θ) := f (label i)
  let pos := Cardinal.aleph0_pos.trans_le hκ
  let code (cutoff : Index θ) (i : Index θ) := cut pos (Set.Iio cutoff) (p i)
  have hc (cutoff : Index θ) : Cardinal.mk (Family κ A (Set.Iio cutoff)) < θ :=
    cardinal_lt hθ hκθ pos (by simpa [Index] using Cardinal.mk_Iio_lt cutoff (by simp [Index]))
      (fun i _ => hA i)
  obtain ⟨a, b, hab, cutoff, he, hs⟩ := exists_pair_agree_on_common_support hθ.isRegular
    (Cardinal.isRegular_succ hκ) (hθ.isSuccLimit.succ_lt hκθ)
    (fun i => support (p i).value) (fun i => (p i).small.trans_le (Order.le_succ κ)) code hc
  refine ⟨label a, label b, fun h => hab.ne (label.injective h), ?_⟩
  apply compatible_of_agree_on_support hκ (p a) (p b)
  intro i hia hib
  have hi := hs ⟨hia,hib⟩
  exact (cut_at pos (p a) hi).symm.trans
    ((congrArg (fun r : Family κ A (Set.Iio cutoff) => r.value i) he).trans (cut_at pos (p b) hi))

theorem full_compatible_pair (hθ : θ.IsInaccessible) (hκθ : κ < θ)
    (hκ : Cardinal.aleph0 ≤ κ) {J : Type u} (f : J → Full κ θ) (hJ : θ ≤ Cardinal.mk J) :
    ∃ a b : J, a ≠ b ∧ ∃ r, r ≤ f a ∧ r ≤ f b :=
  family_compatible_pair hθ hκθ hκ (alphabet_cardinal_lt hθ) f hJ

/-- Every antichain of actual conditions in the full product has size below θ. -/
theorem full_antichain_cardinal_lt (hθ : θ.IsInaccessible) (hκθ : κ < θ)
    (hκ : Cardinal.aleph0 ≤ κ) (s : Set (Full κ θ))
    (hs : s.Pairwise (fun p q => ¬ ∃ r, r ≤ p ∧ r ≤ q)) : Cardinal.mk s < θ := by
  by_contra! h
  obtain ⟨a, b, hab, hr⟩ := full_compatible_pair hθ hκθ hκ (fun p : s => p.val) h
  exact hs a.property b.property (fun he => hab (Subtype.ext he)) hr

/-- The complete Boolean algebra has the same strict bound for every
indexed disjoint family of positive elements. -/
theorem full_completion_disjoint_family_cardinal_lt (hθ : θ.IsInaccessible) (hκθ : κ < θ)
    (hκ : Cardinal.aleph0 ≤ κ) {J : Type u} (b : J → Completion (Full κ θ))
    (hpos : ∀ j, b j ≠ ⊥) (hdisj : ∀ j k, j ≠ k → b j ⊓ b k = ⊥) :
    Cardinal.mk J < θ := by
  choose p hp using fun j => exists_condition_le (hpos j)
  by_contra! h
  obtain ⟨j, k, hjk, r, hrj, hrk⟩ := full_compatible_pair hθ hκθ hκ p h
  have hr : condition r ≤ b j ⊓ b k :=
    le_inf ((condition_mono hrj).trans (hp j)) ((condition_mono hrk).trans (hp k))
  exact condition_ne_bot r (bot_unique (hr.trans_eq (hdisj j k hjk)))

end Erdos1172Shioya.LevyProduct
