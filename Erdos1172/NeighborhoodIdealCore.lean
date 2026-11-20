/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.NeighborhoodIdeal
public import Mathlib.Order.Zorn

@[expose] public section

/-!
# Homogeneous cores in positive color fibers of the constructed ideal
-/

open Cardinal Ordinal Set Order

namespace Erdos1172NeighborhoodIdealCore

open Erdos1172NeighborhoodCode Erdos1172NeighborhoodIdeal

def colorGraph (G H : SimpleGraph W3) (b : Bool) : SimpleGraph W3 :=
  if b then G else H

def neighborhoodCode (b : Bool) (x : W3) : Code :=
  SmallUnionCode.atom ((if b then 0 else 1), x)

theorem eval_neighborhoodCode (G H : SimpleGraph W3) (b : Bool) (x : W3) :
    eval G H (neighborhoodCode b x) = {y | (colorGraph G H b).Adj x y} := by
  cases b <;> rfl

/-- Zorn's lemma supplies a maximal clique inside any prescribed set. -/
theorem exists_maximal_clique_subset (K : SimpleGraph W3) (s : Set W3) :
    ∃ c : Set W3, Maximal (fun c => c ⊆ s ∧ K.IsClique c) c := by
  refine zorn_subset {c | c ⊆ s ∧ K.IsClique c} fun chain hchain hordered =>
    ⟨⋃₀ chain, ⟨fun _ ⟨c, hc, hxc⟩ => (hchain hc).1 hxc,
      (K.isClique_sUnion hordered.directedOn).2 fun c hc => (hchain hc).2⟩,
      fun _ hc => Set.subset_sUnion_of_mem hc⟩

theorem exists_core_of_small {small : Set W3 → Prop} {a : W3}
    (ha : ErdosRadoGCHAsym.IsOmegaTwoSup a)
    (hmono : ∀ {s t}, s ⊆ t → small t → small s)
    (hunion : ∀ {s t}, small s → small t → small (s ∪ t))
    (hiUnion : ∀ {J : Type} (s : J → Set W3), #J < ℵ_ 2 → (∀ j, small (s j)) → small (⋃ j, s j))
    (hbd : ∀ {x}, x < a → small (Set.Iic x))
    (K : SimpleGraph W3)
    (hnon : ∀ {x}, x < a → K.Adj x a → small {y | ¬K.Adj x y})
    (s : Set W3) (hs : ¬small s) (hsBelow : s ⊆ Set.Iio a)
    (hsColor : ∀ x ∈ s, K.Adj x a) :
    ∃ core : Set W3, core ⊆ s ∧ K.IsClique core ∧ typeLT core = ω_ 2 := by
  obtain ⟨c, hc⟩ := exists_maximal_clique_subset K s
  have hcard : ℵ_ 2 ≤ #c := by
    by_contra h
    have hlt : #c < ℵ_ 2 := lt_of_not_ge h
    obtain ⟨cutoff, hcutoff, hbound⟩ :=
      ErdosRadoGCHAsym.exists_strict_bound_of_small_of_IsOmegaTwoSup ha
        (mk_le_alephOne_of_lt_alephTwo hlt) (fun x hx => hsBelow (hc.1.1 hx))
    have hsmall : small ((⋃ x : c, {y | ¬K.Adj x.val y}) ∪ Set.Iic cutoff) :=
      hunion (hiUnion _ hlt fun x => hnon (hsBelow (hc.1.1 x.property)) (hsColor x.val (hc.1.1 x.property)))
        (hbd hcutoff)
    obtain ⟨y, hys, hy⟩ := Set.not_subset.mp fun hsub => hs (hmono hsub hsmall)
    have hlater (x : W3) (hx : x ∈ c) : x < y :=
      (hbound x hx).trans (lt_of_not_ge fun hle => hy (Or.inr hle))
    have hadj (x : W3) (hx : x ∈ c) : K.Adj x y :=
      Classical.byContradiction fun hxy => hy (Or.inl (Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxy⟩))
    have hinsert : insert y c ⊆ s ∧ K.IsClique (insert y c) :=
      ⟨Set.insert_subset hys hc.1.1, hc.1.2.insert fun x hx _ => (hadj x hx).symm⟩
    exact (hlater y (hc.2 hinsert (Set.subset_insert y c) (Set.mem_insert y c))).false
  have htype : (ω_ 2 : Ordinal.{0}) ≤ typeLT c := by
    rw [← Cardinal.ord_aleph]
    exact (Cardinal.ord_le_ord.mpr hcard).trans (Cardinal.ord_le_type (· < ·))
  obtain ⟨core, hsub, htype⟩ := Ordinal.exists_subset_typeLT_eq c htype
  exact ⟨core, hsub.trans hc.1.1, hc.1.2.subset hsub, htype⟩

variable {r : Code ↪ W3} {G H : SimpleGraph W3} {a : W3}

theorem nonneighbors_small (ha : GoodCut r G H a) (b : Bool) {x : W3}
    (hx : x < a) (hxa : (colorGraph G H b).Adj x a) :
    Small r G H a {y | ¬(colorGraph G H b).Adj x y} := by
  simpa only [eval_neighborhoodCode, Set.compl_setOf] using
    named_compl_small (c := neighborhoodCode b x) ha (ha.atom_lt _ x hx) (by rwa [eval_neighborhoodCode])

theorem exists_extension (ha : GoodCut r G H a) (b : Bool)
    (s : Set W3) (hs : ¬Small r G H a s) (hsBelow : s ⊆ Set.Iio a)
    (hsColor : ∀ x ∈ s, (colorGraph G H b).Adj x a)
    (selected : Set W3) (hselected : selected ⊆ s) (hcard : #selected < ℵ_ 2) :
    ∃ y ∈ s, (∀ x ∈ selected, x < y) ∧
      ∀ x ∈ selected, (colorGraph G H b).Adj x y := by
  obtain ⟨cutoff, hcutoff, hbound⟩ :=
    ErdosRadoGCHAsym.exists_strict_bound_of_small_of_IsOmegaTwoSup ha.isOmegaTwoSup
      (mk_le_alephOne_of_lt_alephTwo hcard) (fun x hx => hsBelow (hselected hx))
  have hsmall : Small r G H a ((⋃ x : selected, {y | ¬(colorGraph G H b).Adj x.val y}) ∪ Set.Iic cutoff) :=
    union_small ha (iUnion_small ha _ hcard fun x =>
      nonneighbors_small ha b (hsBelow (hselected x.property)) (hsColor x.val (hselected x.property)))
      (bounded_interval_small ha hcutoff)
  obtain ⟨y, hys, hy⟩ := Set.not_subset.mp fun h => hs (small_mono h hsmall)
  exact ⟨y, hys, fun x hx => (hbound x hx).trans (lt_of_not_ge fun h => hy (Or.inr h)),
    fun x hx => Classical.byContradiction fun hxy => hy (Or.inl (Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxy⟩))⟩

theorem exists_core (ha : GoodCut r G H a) (b : Bool)
    (s : Set W3) (hs : ¬Small r G H a s) (hsBelow : s ⊆ Set.Iio a)
    (hsColor : ∀ x ∈ s, (colorGraph G H b).Adj x a) :
    ∃ core : Set W3, core ⊆ s ∧ (colorGraph G H b).IsClique core ∧
      typeLT core = ω_ 2 :=
  exists_core_of_small ha.isOmegaTwoSup small_mono (union_small ha) (iUnion_small ha)
    (bounded_interval_small ha) (colorGraph G H b) (nonneighbors_small ha b) s hs hsBelow hsColor

end Erdos1172NeighborhoodIdealCore
