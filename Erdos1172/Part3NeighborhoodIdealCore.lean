/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NeighborhoodIdeal
public import Mathlib.Order.Zorn

@[expose] public section

/-!
# Homogeneous cores in positive color fibers of the constructed ideal
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NeighborhoodIdealCore

open Erdos1172Part3NeighborhoodCode Erdos1172Part3NeighborhoodIdeal

def colorGraph (G H : SimpleGraph W2) (b : Bool) : SimpleGraph W2 :=
  if b then G else H

def neighborhoodCode (b : Bool) (x : W2) : Code :=
  SmallUnionCode.atom ((if b then 0 else 1), x)

theorem eval_neighborhoodCode (G H : SimpleGraph W2) (b : Bool) (x : W2) :
    eval G H (neighborhoodCode b x) = {y | (colorGraph G H b).Adj x y} := by
  cases b <;> rfl

variable {r : Code ↪ W2} {G H : SimpleGraph W2} {a : W2}

theorem nonneighbors_small (ha : GoodCut r G H a) (b : Bool) {x : W2}
    (hx : x < a) (hxa : (colorGraph G H b).Adj x a) :
    Small r G H a {y | ¬(colorGraph G H b).Adj x y} := by
  simpa only [eval_neighborhoodCode, Set.compl_setOf] using
    named_compl_small (c := neighborhoodCode b x) ha (ha.atom_lt _ x hx) (by rwa [eval_neighborhoodCode])

theorem exists_extension (ha : GoodCut r G H a) (b : Bool)
    (s : Set W2) (hs : ¬Small r G H a s) (hsBelow : s ⊆ Set.Iio a)
    (hsColor : ∀ x ∈ s, (colorGraph G H b).Adj x a)
    (selected : Set W2) (hselected : selected ⊆ s) (hcard : #selected < ℵ_ 1) :
    ∃ y ∈ s, (∀ x ∈ selected, x < y) ∧
      ∀ x ∈ selected, (colorGraph G H b).Adj x y := by
  obtain ⟨cutoff, hcutoff, hbound⟩ :=
    ErdosRadoCHAsym.exists_strict_bound_of_countable_of_IsOmegaOneSup ha.isOmegaOneSup
      (Cardinal.lt_aleph_one_iff.mp hcard) (fun x hx => hsBelow (hselected hx))
  have hsmall : Small r G H a ((⋃ x : selected, {y | ¬(colorGraph G H b).Adj x.val y}) ∪ Set.Iic cutoff) :=
    union_small ha (iUnion_small ha _ hcard fun x =>
      nonneighbors_small ha b (hsBelow (hselected x.property)) (hsColor x.val (hselected x.property)))
      (bounded_interval_small ha hcutoff)
  obtain ⟨y, hys, hy⟩ := Set.not_subset.mp fun h => hs (small_mono h hsmall)
  exact ⟨y, hys, fun x hx => (hbound x hx).trans (lt_of_not_ge fun h => hy (Or.inr h)),
    fun x hx => Classical.byContradiction fun hxy => hy (Or.inl (Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxy⟩))⟩

theorem exists_maximal_clique_subset (K : SimpleGraph W2) (s : Set W2) :
    ∃ c : Set W2, Maximal (fun c => c ⊆ s ∧ K.IsClique c) c := by
  refine zorn_subset {c | c ⊆ s ∧ K.IsClique c} fun chain hchain hordered =>
    ⟨⋃₀ chain, ⟨fun _ ⟨c, hc, hxc⟩ => (hchain hc).1 hxc,
      (K.isClique_sUnion hordered.directedOn).2 fun c hc => (hchain hc).2⟩,
      fun _ hc => Set.subset_sUnion_of_mem hc⟩

theorem exists_core (ha : GoodCut r G H a) (b : Bool)
    (s : Set W2) (hs : ¬Small r G H a s) (hsBelow : s ⊆ Set.Iio a)
    (hsColor : ∀ x ∈ s, (colorGraph G H b).Adj x a) :
    ∃ core : Set W2, core ⊆ s ∧ (colorGraph G H b).IsClique core ∧
      typeLT core = ω_ 1 := by
  obtain ⟨c, hc⟩ := exists_maximal_clique_subset (colorGraph G H b) s
  have hcard : ℵ_ 1 ≤ #c := by
    by_contra h
    obtain ⟨y, hys, hlater, hadj⟩ := exists_extension ha b s hs hsBelow hsColor
      c hc.1.1 (lt_of_not_ge h)
    have hinsert : insert y c ⊆ s ∧ (colorGraph G H b).IsClique (insert y c) :=
      ⟨Set.insert_subset hys hc.1.1, hc.1.2.insert fun x hx _ => (hadj x hx).symm⟩
    exact (hlater y (hc.2 hinsert (Set.subset_insert y c) (Set.mem_insert y c))).false
  have htype : (ω_ 1 : Ordinal.{0}) ≤ typeLT c := by
    rw [← Cardinal.ord_aleph]
    exact (Cardinal.ord_le_ord.mpr hcard).trans (Cardinal.ord_le_type (· < ·))
  obtain ⟨core, hsub, htype⟩ := Ordinal.exists_subset_typeLT_eq c htype
  exact ⟨core, hsub.trans hc.1.1, hc.1.2.subset hsub, htype⟩

end Erdos1172Part3NeighborhoodIdealCore
