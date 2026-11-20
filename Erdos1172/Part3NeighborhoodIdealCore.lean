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

Every ideal-positive subset of a single color's predecessor neighborhood
contains a homogeneous `omegaOne` core. Small seed extension is supplied by
the actual coded ideal, and a maximal clique gives the full core. This is a
base-ideal theorem, not the mixed-color endpoint conclusion of Problem 1172.
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
  have hc : r (neighborhoodCode b x) < a := ha.atom_lt _ x hx
  have hmem : a ∈ eval G H (neighborhoodCode b x) := by
    rwa [eval_neighborhoodCode]
  simpa only [eval_neighborhoodCode, Set.compl_setOf] using
    named_compl_small ha hc hmem

theorem exists_extension (ha : GoodCut r G H a) (b : Bool)
    (s : Set W2) (hs : ¬Small r G H a s) (hsBelow : s ⊆ Set.Iio a)
    (hsColor : ∀ x ∈ s, (colorGraph G H b).Adj x a)
    (selected : Set W2) (hselected : selected ⊆ s) (hcard : #selected < ℵ_ 1) :
    ∃ y ∈ s, (∀ x ∈ selected, x < y) ∧
      ∀ x ∈ selected, (colorGraph G H b).Adj x y := by
  classical
  obtain ⟨cutoff, hcutoff, hbound⟩ :=
    ErdosRadoCHAsym.exists_strict_bound_of_countable_of_IsOmegaOneSup ha.isOmegaOneSup
      (Cardinal.lt_aleph_one_iff.mp hcard)
      (fun x hx => hsBelow (hselected hx))
  let bad : Set W2 := ⋃ x : selected, {y | ¬(colorGraph G H b).Adj x.val y}
  have hbad : Small r G H a bad := iUnion_small ha _ hcard (fun x =>
    nonneighbors_small ha b (hsBelow (hselected x.property))
      (hsColor x.val (hselected x.property)))
  have hsmall : Small r G H a (bad ∪ Set.Iic cutoff) :=
    union_small ha hbad (bounded_interval_small ha hcutoff)
  have hnot : ¬s ⊆ bad ∪ Set.Iic cutoff := fun h => hs (small_mono h hsmall)
  obtain ⟨y, hys, hy⟩ := Set.not_subset.mp hnot
  refine ⟨y, hys, ?_, ?_⟩
  · intro x hx
    exact (hbound x hx).trans
      (lt_of_not_ge (fun h => hy (Or.inr h)))
  · intro x hx
    by_contra hxy
    apply hy
    exact Or.inl (Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxy⟩)

/-- Zorn's lemma supplies a maximal clique inside any prescribed set. -/
theorem exists_maximal_clique_subset (K : SimpleGraph W2) (s : Set W2) :
    ∃ c : Set W2, Maximal (fun c => c ⊆ s ∧ K.IsClique c) c := by
  apply zorn_subset {c | c ⊆ s ∧ K.IsClique c}
  intro chain hchain hordered
  refine ⟨⋃₀ chain, ⟨?_, ?_⟩, ?_⟩
  · rintro x ⟨c, hc, hxc⟩
    exact (hchain hc).1 hxc
  · exact (K.isClique_sUnion hordered.directedOn).2 (fun c hc => (hchain hc).2)
  · exact fun c hc => Set.subset_sUnion_of_mem hc

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
      ⟨Set.insert_subset hys hc.1.1,
        hc.1.2.insert (fun x hx _ => (hadj x hx).symm)⟩
    have hyc : y ∈ c := hc.2 hinsert (Set.subset_insert y c) (Set.mem_insert y c)
    exact (hlater y hyc).false
  have htype : (ω_ 1 : Ordinal.{0}) ≤ typeLT c := by
    rw [← Cardinal.ord_aleph]
    exact (Cardinal.ord_le_ord.mpr hcard).trans (Cardinal.ord_le_type (· < ·))
  obtain ⟨core, hsub, htype⟩ := Ordinal.exists_subset_typeLT_eq c htype
  exact ⟨core, hsub.trans hc.1.1, hc.1.2.subset hsub, htype⟩

end Erdos1172Part3NeighborhoodIdealCore
