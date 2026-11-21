/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.SetTheory.Cardinal.Ordinal
public import Erdos1172.Part4DenseCompletionCardinality
public import Erdos1172.Part4ShioyaStringTransport
public import Mathlib.Order.Bounds.OrderIso

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

end Erdos1172Shioya.LevyProduct
