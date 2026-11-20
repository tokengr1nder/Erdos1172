/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaCollapseConditions

@[expose] public section

/-! # The closed dense tree of ordinal-domain collapse conditions -/

set_option autoImplicit false
noncomputable section
universe u

namespace Erdos1172Shioya.Collapse

structure Sequence (κ : Cardinal.{u}) (X : Type u) where
  length : κ.ord.ToType
  letter : Set.Iio length → X

def ordinalDomain (κ : Cardinal.{u}) (X : Type u) : Set (Condition κ X) :=
  {p | ∃ l : κ.ord.ToType, Prod.fst '' p.graph = Set.Iio l}

namespace Sequence

variable {κ : Cardinal.{u}} {X : Type u}

def toCondition (s : Sequence κ X) : Condition κ X where
  graph := Set.range (fun i : Set.Iio s.length => (i.val, s.letter i))
  functional := by
    rintro _ _ _ ⟨i, hi⟩ ⟨j, hj⟩
    have hij : i = j := Subtype.ext ((congrArg Prod.fst hi).trans (congrArg Prod.fst hj).symm)
    exact (congrArg Prod.snd hi).symm.trans ((congrArg s.letter hij).trans (congrArg Prod.snd hj))
  small := Cardinal.mk_range_le.trans_lt (by simpa using (Cardinal.mk_Iio_lt s.length (by simp)))

theorem mem_toCondition (s : Sequence κ X) (i : Set.Iio s.length) :
    (i.val, s.letter i) ∈ s.toCondition.graph := ⟨i, rfl⟩

theorem dom_toCondition (s : Sequence κ X) : Prod.fst '' s.toCondition.graph = Set.Iio s.length := by
  ext i
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    exact j.property
  · intro hi
    exact ⟨(i, s.letter ⟨i, hi⟩), mem_toCondition s ⟨i,hi⟩, rfl⟩

theorem toCondition_le_iff (s t : Sequence κ X) : s.toCondition ≤ t.toCondition ↔
    ∃ h : t.length ≤ s.length, ∀ i : Set.Iio t.length,
      s.letter ⟨i.val, i.property.trans_le h⟩ = t.letter i := by
  constructor
  · intro hp
    have hdom : Set.Iio t.length ⊆ Set.Iio s.length := by
      rw [← dom_toCondition, ← dom_toCondition]
      exact Set.image_mono (Collapse.le_iff.mp hp)
    have hl : t.length ≤ s.length := Set.Iio_subset_Iio_iff.mp hdom
    exact ⟨hl, fun i => s.toCondition.functional (mem_toCondition s _) (Collapse.le_iff.mp hp (mem_toCondition t i))⟩
  · rintro ⟨hl, hf⟩ _ ⟨i,rfl⟩
    exact ⟨⟨i.val, i.property.trans_le hl⟩, Prod.ext rfl (hf i)⟩

theorem toCondition_injective : Function.Injective (toCondition : Sequence κ X → _) := by
  rintro ⟨l, f⟩ ⟨k, g⟩ he
  obtain ⟨h, hg⟩ := (toCondition_le_iff _ _).mp he.le
  obtain ⟨h', _⟩ := (toCondition_le_iff _ _).mp he.ge
  obtain rfl : k = l := le_antisymm h h'
  have he' : f = g := funext (fun i => hg i)
  cases he'
  rfl

instance : PartialOrder (Sequence κ X) := PartialOrder.lift toCondition toCondition_injective

theorem le_iff (s t : Sequence κ X) : s ≤ t ↔ ∃ h : t.length ≤ s.length, ∀ i : Set.Iio t.length,
    s.letter ⟨i.val, i.property.trans_le h⟩ = t.letter i := toCondition_le_iff s t

def take (s : Sequence κ X) (l : κ.ord.ToType) (h : l ≤ s.length) : Sequence κ X :=
  ⟨l, fun i => s.letter ⟨i.val, i.property.trans_le h⟩⟩

theorem le_take (s : Sequence κ X) (l : κ.ord.ToType) (h : l ≤ s.length) : s ≤ s.take l h :=
  (le_iff _ _).mpr ⟨h, fun _ => rfl⟩

def empty (hκ : 0 < κ) : Sequence κ X := by
  let l : κ.ord.ToType := Ordinal.ToType.mk ⟨0, Cardinal.ord_pos.mpr hκ⟩
  have hl : l.toOrd.val = 0 := congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
  refine ⟨l, fun i => ?_⟩
  have hi : i.val.toOrd.val < l.toOrd.val := Ordinal.ToType.mk.symm.strictMono i.property
  exact (not_lt_of_ge zero_le (hi.trans_eq hl)).elim

theorem empty_length (hκ : 0 < κ) : (empty (X := X) hκ).length.toOrd.val = 0 :=
  congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)

def append (s : Sequence κ X) (hκ : Cardinal.aleph0 ≤ κ) (x : X) : Sequence κ X := by
  classical
  have ho : Order.succ s.length.toOrd.val < κ.ord :=
    (Cardinal.isSuccLimit_ord hκ).succ_lt (show s.length.toOrd.val < κ.ord from s.length.toOrd.property)
  exact ⟨Ordinal.ToType.mk ⟨Order.succ s.length.toOrd.val, ho⟩,
    fun i => if h : i.val < s.length then s.letter ⟨i.val,h⟩ else x⟩

theorem append_length (s : Sequence κ X) (hκ : Cardinal.aleph0 ≤ κ) (x : X) :
    (s.append hκ x).length.toOrd.val = Order.succ s.length.toOrd.val :=
  congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)

theorem lt_append_length_iff (s : Sequence κ X) (hκ : Cardinal.aleph0 ≤ κ) (x : X) (i : κ.ord.ToType) :
    i < (s.append hκ x).length ↔ i ≤ s.length := by
  rw [← (Ordinal.ToType.mk (o := κ.ord)).symm.lt_iff_lt,
    ← (Ordinal.ToType.mk (o := κ.ord)).symm.le_iff_le]
  change i.toOrd.val < (s.append hκ x).length.toOrd.val ↔ i.toOrd.val ≤ s.length.toOrd.val
  rw [append_length, Order.lt_succ_iff]

theorem append_le (s : Sequence κ X) (hκ : Cardinal.aleph0 ≤ κ) (x : X) : s.append hκ x ≤ s := by
  exact (le_iff _ _).mpr ⟨((s.lt_append_length_iff hκ x _).mpr le_rfl).le, fun i => by
    simp only [append, dif_pos (show i.val < s.length from i.property)]⟩

theorem append_at (s : Sequence κ X) (hκ : Cardinal.aleph0 ≤ κ) (x : X) :
    (s.append hκ x).letter ⟨s.length, (s.lt_append_length_iff hκ x _).mpr le_rfl⟩ = x := by simp [append]

theorem exists_cover_of_isGLB {L : Type u} (f : L → Sequence κ X) (s : Sequence κ X)
    (hs : IsGLB (Set.range f) s) (i : Set.Iio s.length) : ∃ l, i.val < (f l).length := by
  classical
  by_contra! h
  have hlo : s.take i.val i.property.le ∈ lowerBounds (Set.range f) := by
    rintro _ ⟨j, rfl⟩
    have hsj := (le_iff s (f j)).mp (hs.1 (Set.mem_range_self j))
    exact (le_iff _ _).mpr ⟨h j, fun v => hsj.choose_spec v⟩
  have hlen := ((le_iff _ _).mp (hs.2 hlo)).choose
  exact (not_le_of_gt i.property) hlen

theorem toCondition_isGLB_iff {L : Type u} (f : L → Sequence κ X) (s : Sequence κ X) :
    IsGLB (Set.range (fun l => (f l).toCondition)) s.toCondition ↔ IsGLB (Set.range f) s := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rintro _ ⟨l,rfl⟩
      exact h.1 (Set.mem_range_self l)
    · intro t ht
      apply h.2
      rintro _ ⟨l,rfl⟩
      exact ht (Set.mem_range_self l)
  · intro h
    refine ⟨?_, ?_⟩
    · rintro _ ⟨l,rfl⟩
      exact h.1 (Set.mem_range_self l)
    · intro q hq
      apply Collapse.le_iff.mpr
      rintro _ ⟨i,rfl⟩
      obtain ⟨l,hi⟩ := exists_cover_of_isGLB f s h i
      obtain ⟨_,he⟩ := (le_iff s (f l)).mp (h.1 (Set.mem_range_self l))
      have he' : s.letter i = (f l).letter ⟨i.val,hi⟩ := he ⟨i.val,hi⟩
      change (i.val, s.letter i) ∈ q.graph
      rw [he']
      exact Collapse.le_iff.mp (hq (Set.mem_range_self l)) (mem_toCondition (f l) ⟨i.val,hi⟩)

theorem exists_toCondition (p : ordinalDomain κ X) : ∃ s : Sequence κ X, s.toCondition = p.val := by
  classical
  obtain ⟨l, hl⟩ := p.property
  have hm (i : Set.Iio l) : ∃ x, (i.val, x) ∈ p.val.graph := by
    have hi := (Set.ext_iff.mp hl i.val).mpr i.property
    obtain ⟨⟨j,x⟩, hx, he⟩ := hi
    exact ⟨x,(show j = i.val from he) ▸ hx⟩
  choose f hf using hm
  refine ⟨⟨l,f⟩, graph_injective (Set.ext fun v => ?_)⟩
  constructor
  · rintro ⟨i, rfl⟩
    exact hf i
  · intro hv
    have hi : v.1 ∈ Set.Iio l := hl ▸ Set.mem_image_of_mem Prod.fst hv
    exact ⟨⟨v.1,hi⟩, Prod.ext rfl (p.val.functional (hf _) hv)⟩

def orderIso : Sequence κ X ≃o ordinalDomain κ X where
  toEquiv := Equiv.ofBijective (fun s => ⟨s.toCondition, s.length, s.dom_toCondition⟩)
    ⟨fun _ _ h => toCondition_injective (congrArg Subtype.val h),
      fun p => (exists_toCondition p).imp (fun _ h => Subtype.ext h)⟩
  map_rel_iff' := Iff.rfl

end Sequence

variable {κ : Cardinal.{u}} {X : Type u}

theorem ordinalDomain_dense [Nonempty X] (hκ : κ.IsRegular) (p : Condition κ X) :
    ∃ q ∈ ordinalDomain κ X, q ≤ p := by
  classical
  let D := Prod.fst '' p.graph
  have hsmall : Cardinal.mk D < κ := Cardinal.mk_image_le.trans_lt p.small
  have hn : ¬ IsCofinal D := by
    intro h
    have hh := Order.cof_le h
    rw [Ordinal.cof_toType, hκ.cof_ord] at hh
    exact hsmall.not_ge hh
  obtain ⟨l, hl⟩ : ∃ l : κ.ord.ToType, ∀ i ∈ D, i < l := by
    by_contra! hc
    exact hn hc
  let f (i : Set.Iio l) := Classical.epsilon (fun x : X => (i.val, x) ∈ p.graph)
  let s : Sequence κ X := ⟨l, f⟩
  refine ⟨s.toCondition, ⟨l, s.dom_toCondition⟩, ?_⟩
  rintro ⟨i,x⟩ hx
  let v : Set.Iio l := ⟨i, hl i (Set.mem_image_of_mem Prod.fst hx)⟩
  have hf : (i, f v) ∈ p.graph := Classical.epsilon_spec (p := fun y => (i,y) ∈ p.graph) ⟨x,hx⟩
  exact ⟨v, Prod.ext rfl (p.functional hf hx)⟩

theorem ordinalDomain_closed {L : Type u} (f : L → ordinalDomain κ X) (p : Condition κ X)
    (hp : IsGLB (Set.range (fun l => (f l).val)) p) : p ∈ ordinalDomain κ X := by
  classical
  let G := ⋃ l : L, (f l).val.graph
  have hGp : G ⊆ p.graph := Set.iUnion_subset fun l => le_iff.mp (hp.1 (Set.mem_range_self l))
  let q : Condition κ X := ⟨G, fun hx hy => p.functional (hGp hx) (hGp hy),
    (Cardinal.mk_le_mk_of_subset hGp).trans_lt p.small⟩
  have hq : q ∈ lowerBounds (Set.range (fun l => (f l).val)) := by
    rintro _ ⟨l,rfl⟩
    exact le_iff.mpr (Set.subset_iUnion (fun j => (f j).val.graph) l)
  have hpG : p.graph ⊆ G := le_iff.mp (hp.2 hq)
  let D := Prod.fst '' p.graph
  have hdown : IsLowerSet D := by
    rintro _ _ hij ⟨v, hx, he⟩
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp (hpG hx)
    obtain ⟨k,hk⟩ := (f l).property
    have hj : v.1 ∈ Set.Iio k := (Set.ext_iff.mp hk _).mp (Set.mem_image_of_mem Prod.fst hl)
    have hi := hij.trans_lt (he ▸ hj)
    exact (Set.image_mono (le_iff.mp (hp.1 (Set.mem_range_self l)))) ((Set.ext_iff.mp hk _).mpr hi)
  have hm : (Dᶜ).Nonempty := by
    obtain ⟨i,hi⟩ := exists_fresh p
    exact ⟨i, fun ⟨⟨_,x⟩,hx,he⟩ => hi x (he ▸ hx)⟩
  let l := wellFounded_lt.min (Dᶜ) hm
  have hmiss : l ∉ D := wellFounded_lt.min_mem (Dᶜ) hm
  refine ⟨l, Set.ext fun i => ?_⟩
  constructor
  · intro hi
    exact lt_of_not_ge (fun h => hmiss (hdown h hi))
  · intro hi
    by_contra hni
    exact (not_le_of_gt hi) (wellFounded_lt.min_le (s := Dᶜ) hni)

theorem Sequence.shortInfima (hκ : κ.IsRegular) : ShortInfima κ (Sequence κ X) := by
  intro L _ _ hL f hf
  let g (l : L) : ordinalDomain κ X := ⟨(f l).toCondition, (f l).length, (f l).dom_toCondition⟩
  obtain ⟨p,hp⟩ := Collapse.shortInfima (α := X) hκ L hL (fun l => (g l).val)
    (fun _ _ h => hf h)
  obtain ⟨s,hs⟩ := Sequence.exists_toCondition ⟨p, ordinalDomain_closed g p hp⟩
  refine ⟨s, (Sequence.toCondition_isGLB_iff f s).mp ?_⟩
  simpa only [hs] using hp

end Erdos1172Shioya.Collapse
