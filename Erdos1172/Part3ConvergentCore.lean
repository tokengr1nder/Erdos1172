/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CoreObjectIdealCore
public import Erdos1172.ForMathlib.Combinatorics.SimpleGraph.CliqueFamilyUnion

@[expose] public section

/-!
# Cores converging to every locally named neighborhood

Countable extension constructs a homogeneous omegaOne sequence. Its tail
lies in every local named set containing the cut, so its trace upgrades
the coded ideal to the ordinary countable-set ideal on this core.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3ConvergentCore

open Erdos1172Part3CoreObjectCode Erdos1172Part3CoreObjectIdeal
open Erdos1172Part3CoreObjectIdealCore
open Erdos1172Part3NeighborhoodCode (W2)
open ErdosRadoCHAsym (W1)
open Erdos1172Part3CountableRankClosure (Local mk_local_le)

variable {r : Code ↪ W2} {σ : Obj ↪ W2} {G H : SimpleGraph W2} {a : W2}

theorem exists_extension_avoiding (ha : GoodCut r σ G H a) (b : Bool)
    (s : Set W2) (hs : ¬Small r G H a s) (hsBelow : s ⊆ Set.Iio a)
    (hsColor : ∀ x ∈ s, (colorGraph G H b).Adj x a)
    (selected : Set W2) (hselected : selected ⊆ s) (hcard : #selected < ℵ_ 1)
    (avoid : Set W2) (havoid : Small r G H a avoid) :
    ∃ y ∈ s, y ∉ avoid ∧ (∀ x ∈ selected, x < y) ∧
      ∀ x ∈ selected, (colorGraph G H b).Adj x y := by
  classical
  obtain ⟨cutoff, hcutoff, hbound⟩ :=
    ErdosRadoCHAsym.exists_strict_bound_of_countable_of_IsOmegaOneSup ha.isOmegaOneSup
      (Cardinal.lt_aleph_one_iff.mp hcard) (fun x hx => hsBelow (hselected hx))
  let bad : Set W2 := ⋃ x : selected, {y | ¬(colorGraph G H b).Adj x.val y}
  have hbad : Small r G H a bad := iUnion_small ha _ hcard (fun x =>
    nonneighbors_small ha b (hsBelow (hselected x.property))
      (hsColor x.val (hselected x.property)))
  have hsmall : Small r G H a (avoid ∪ (bad ∪ Set.Iic cutoff)) :=
    union_small ha havoid (union_small ha hbad (bounded_interval_small ha hcutoff))
  obtain ⟨y, hys, hy⟩ := Set.not_subset.mp
    (fun h => hs (small_mono h hsmall))
  refine ⟨y, hys, fun h => hy (Or.inl h), ?_, ?_⟩
  · intro x hx
    exact (hbound x hx).trans (lt_of_not_ge (fun h => hy (Or.inr (Or.inr h))))
  · intro x hx
    by_contra hxy
    exact hy (Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxy⟩)))

theorem mk_Iio_W1_lt (i : W1) : #(Set.Iio i) < ℵ_ 1 := by
  simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using
    Cardinal.mk_Iio_lt i (by simp [W1])

theorem mk_Iic_W1_lt (i : W1) : #(Set.Iic i) < ℵ_ 1 := by
  simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using
    Cardinal.mk_Iic_lt i (by simp [W1]) (by simp [W1])

theorem exists_convergent_core (ha : GoodCut r σ G H a) (b : Bool)
    (s : Set W2) (hs : ¬Small r G H a s) (hsBelow : s ⊆ Set.Iio a)
    (hsColor : ∀ x ∈ s, (colorGraph G H b).Adj x a) :
    ∃ f : W1 → W2, StrictMono f ∧ Set.range f ⊆ s ∧
      (colorGraph G H b).IsClique (Set.range f) ∧
      ∀ c : Code, r c < a → a ∈ eval G H c →
        ∃ i : W1, ∀ j : W1, i < j → f j ∈ eval G H c := by
  classical
  obtain ⟨index⟩ : Nonempty (Local r a ↪ W1) := (Cardinal.le_def _ _).mp (by
    simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using mk_local_le r a)
  have step (i : W1) (previous : ∀ j, j < i → s) :
      ∃ y : s, (∀ j (hj : j < i), (previous j hj).val < y.val ∧
        (colorGraph G H b).Adj (previous j hj).val y.val) ∧
      ∀ c : Local r a, index c < i → a ∈ eval G H c.val → y.val ∈ eval G H c.val := by
    let active := {c : Local r a // index c < i ∧ a ∈ eval G H c.val}
    have hactive : #active < ℵ_ 1 := by
      let e : active ↪ Set.Iio i :=
        ⟨fun c => ⟨index c.val, c.property.1⟩,
          fun _ _ h => Subtype.ext (index.injective (congrArg Subtype.val h))⟩
      exact (Cardinal.mk_le_of_injective e.injective).trans_lt (mk_Iio_W1_lt i)
    let avoid : Set W2 := ⋃ c : active, (eval G H c.val.val)ᶜ
    have havoid : Small r G H a avoid := iUnion_small ha _ hactive
      (fun c => named_compl_small ha c.val.property c.property.2)
    let selected : Set W2 := Set.range (fun j : Set.Iio i => (previous j.val j.property).val)
    have hselected : selected ⊆ s := by
      rintro x ⟨j, rfl⟩
      exact (previous j.val j.property).property
    have hcard : #selected < ℵ_ 1 :=
      (Cardinal.mk_range_le (f := fun j : Set.Iio i => (previous j.val j.property).val)).trans_lt
        (mk_Iio_W1_lt i)
    obtain ⟨y, hys, hyn, hyl, hyc⟩ := exists_extension_avoiding ha b s hs hsBelow hsColor
      selected hselected hcard avoid havoid
    refine ⟨⟨y, hys⟩, ?_, ?_⟩
    · intro j hj
      exact ⟨hyl _ ⟨⟨j, hj⟩, rfl⟩, hyc _ ⟨⟨j, hj⟩, rfl⟩⟩
    · intro c hci hac
      by_contra hy
      exact hyn (Set.mem_iUnion.mpr ⟨⟨c, hci, hac⟩, hy⟩)
  let next (i : W1) (previous : ∀ j, j < i → s) : s := (step i previous).choose
  let branch : W1 → s := WellFoundedLT.fix next
  have hbranch (i : W1) : branch i = next i (fun j _ => branch j) := by
    dsimp only [branch]
    rw [WellFoundedLT.fix_eq]
  have hspec (i : W1) := (step i (fun j _ => branch j)).choose_spec
  have hnext (i : W1) : next i (fun j _ => branch j) = branch i := (hbranch i).symm
  have hmono : StrictMono (fun i => (branch i).val) := by
    intro i j hij
    have h := (hspec j).1 i hij
    change (branch i).val < (next j (fun k _ => branch k)).val ∧ _ at h
    rw [hnext] at h
    exact h.1
  refine ⟨fun i => (branch i).val, hmono, ?_, ?_, ?_⟩
  · rintro x ⟨i, rfl⟩
    exact (branch i).property
  · rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ hne
    have hij : i ≠ j := fun h => hne (congrArg (fun k => (branch k).val) h)
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have h := (hspec j).1 i hlt
      change _ ∧ (colorGraph G H b).Adj (branch i).val (next j (fun k _ => branch k)).val at h
      rw [hnext] at h
      exact h.2
    · have h := (hspec i).1 j hgt
      change _ ∧ (colorGraph G H b).Adj (branch j).val (next i (fun k _ => branch k)).val at h
      rw [hnext] at h
      exact h.2.symm
  · intro c hc hac
    refine ⟨index ⟨c, hc⟩, ?_⟩
    intro j hij
    have h := (hspec j).2 ⟨c, hc⟩ hij hac
    change (next j (fun k _ => branch k)).val ∈ eval G H c at h
    rwa [hnext] at h

/-- A convergent sequence meets every member of the coded ideal in a
countable set. This is stronger than merely extracting one clique. -/
theorem small_trace_of_convergent (ha : GoodCut r σ G H a) (f : W1 → W2)
    (hconv : ∀ c : Code, r c < a → a ∈ eval G H c →
      ∃ i : W1, ∀ j : W1, i < j → f j ∈ eval G H c)
    {x : Set W2} (hx : Small r G H a x) :
    #(Set.range f ∩ x : Set W2) < ℵ_ 1 := by
  obtain ⟨c, hc, hac, hxc⟩ := hx
  obtain ⟨i, hi⟩ := hconv (SmallUnionCode.compl c) (ha.compl_lt c hc) hac
  have hsub : (Set.range f ∩ x : Set W2) ⊆ f '' Set.Iic i := by
    rintro y ⟨⟨j, rfl⟩, hjx⟩
    refine ⟨j, ?_, rfl⟩
    exact le_of_not_gt (fun hij => (hi j hij) (hxc hjx))
  exact ((Cardinal.mk_le_mk_of_subset hsub).trans Cardinal.mk_image_le).trans_lt
    (mk_Iic_W1_lt i)

theorem isLUB_of_convergent (ha : GoodCut r σ G H a) (f : W1 → W2)
    (hf : StrictMono f) (hbelow : Set.range f ⊆ Set.Iio a)
    (hconv : ∀ c : Code, r c < a → a ∈ eval G H c →
      ∃ i : W1, ∀ j : W1, i < j → f j ∈ eval G H c) :
    IsLUB (Set.range f) a := by
  refine ⟨fun x hx => (hbelow hx).le, ?_⟩
  intro upper hupper
  by_contra h
  have hua : upper < a := lt_of_not_ge h
  have hsmall := small_trace_of_convergent ha f hconv (bounded_interval_small ha hua)
  have hrange : Set.range f ∩ Set.Iic upper = Set.range f := Set.inter_eq_left.mpr hupper
  rw [hrange, Cardinal.mk_range_eq f hf.injective] at hsmall
  simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega, lt_self_iff_false] using hsmall

/-- The ordinary countable ideal on one fixed core. -/
def TraceSmall (core x : Set W2) : Prop := #(core ∩ x : Set W2) < ℵ_ 1

theorem traceSmall_iff_countable (core x : Set W2) :
    TraceSmall core x ↔ (core ∩ x).Countable := by
  exact Cardinal.lt_aleph_one_iff.trans Cardinal.le_aleph0_iff_set_countable

def traceSmallness (core : Set W2) :
    Erdos1172Part3FiniteIdealEndpoint.FiniteSmallness W2 where
  small := TraceSmall core
  empty_small := by simp [TraceSmall]
  mono := by
    intro s t hst ht
    rw [traceSmall_iff_countable] at ht ⊢
    exact ht.mono (Set.inter_subset_inter_right core hst)
  union_small := by
    intro s t hs ht
    rw [traceSmall_iff_countable] at hs ht ⊢
    rw [Set.inter_union_distrib_left]
    exact hs.union ht

theorem core_of_trace_positive {K : SimpleGraph W2} {core x : Set W2}
    (hc : K.IsClique core) (ht : typeLT core = ω_ 1)
    (hx : ¬TraceSmall core x) :
    K.IsClique (core ∩ x) ∧ typeLT (core ∩ x : Set W2) = ω_ 1 := by
  refine ⟨hc.subset Set.inter_subset_left, le_antisymm ?_ ?_⟩
  · exact (Ordinal.type_mono Set.inter_subset_left).trans_eq ht
  · rw [← Cardinal.ord_aleph]
    exact (Cardinal.ord_le_ord.mpr (le_of_not_gt hx)).trans (Cardinal.ord_le_type (· < ·))

/-- All the properties needed for the first red-block ideal are produced
from the positive red predecessor fiber itself. -/
theorem exists_cofinal_core_with_small_traces (ha : GoodCut r σ G H a) (b : Bool)
    (s : Set W2) (hs : ¬Small r G H a s) (hsBelow : s ⊆ Set.Iio a)
    (hsColor : ∀ x ∈ s, (colorGraph G H b).Adj x a) :
    ∃ core : Set W2, core ⊆ s ∧ (colorGraph G H b).IsClique core ∧
      typeLT core = ω_ 1 ∧ IsLUB core a ∧
      ∀ x : Set W2, Small r G H a x → TraceSmall core x := by
  obtain ⟨f, hf, hfs, hfc, hconv⟩ := exists_convergent_core ha b s hs hsBelow hsColor
  refine ⟨Set.range f, hfs, hfc, ?_, isLUB_of_convergent ha f hf (hfs.trans hsBelow) hconv,
    fun x hx => small_trace_of_convergent ha f hconv hx⟩
  simpa only [W1, Ordinal.type_toType] using Ordinal.typeLT_range_of_strictMono f hf

end Erdos1172Part3ConvergentCore
