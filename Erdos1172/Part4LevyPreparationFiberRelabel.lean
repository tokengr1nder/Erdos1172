/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyInitialEmbeddingCodes

@[expose] public section

/-! # Relabeling a finite Lévy condition along an arbitrary ordinal embedding -/

set_option autoImplicit false
noncomputable section
open scoped Erdos1172LevyCollapse
universe u
namespace Erdos1172LevyCollapse.Preparation
variable {κ θ : Cardinal.{u}}
local notation "K" => κ.ord.ToType
local notation "L" => θ.ord.ToType

def letter (f : K ↪o L) (i : K) : Set.Iio i ↪ Set.Iio (f i) :=
  ⟨fun x => ⟨f x.val,f.strictMono x.property⟩,fun _ _ h => Subtype.ext (f.injective (congrArg Subtype.val h))⟩

theorem exists_relabel (f : K ↪o L) (p : BelowCondition κ) :
    ∃ q : BelowCondition θ, (∀ i, (q (f i)).entries = (p i).entries.map (letter f i)) ∧
      ∀ y ∉ Set.range f, q y = ⊤ := by
  classical
  let V (i : K) : Erdos1172Collapse.Condition (Set.Iio (f i)) := ⟨(p i).entries.map (letter f i)⟩
  have extend (s : Finset K) : ∃ r : BelowCondition θ, (∀ i ∈ s, r (f i) = V i) ∧
      ∀ y, (∀ i ∈ s, f i ≠ y) → r y = ⊤ := by
    induction s using Finset.induction_on with
    | empty => exact ⟨⊤,by simp,fun _ _ => rfl⟩
    | @insert i s hi ih =>
      obtain ⟨r,hr,off⟩ := ih
      refine ⟨r.update (f i) (V i),?_,?_⟩
      · intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · simp only [DFinsupp.coe_update,Function.update_self]
        · have ne : f k ≠ f i := fun h => hi (f.injective h ▸ hk)
          simpa only [DFinsupp.coe_update,Function.update_of_ne ne] using hr k hk
      · intro y hy
        rw [DFinsupp.coe_update,Function.update_of_ne (hy i (Finset.mem_insert_self _ _)).symm]
        exact off y (fun k hk => hy k (Finset.mem_insert_of_mem hk))
  obtain ⟨q,hq,off⟩ := extend p.support
  refine ⟨q,fun i => ?_,fun y hy => off y (fun k _ hk => hy ⟨k,hk⟩)⟩
  by_cases hi : i ∈ p.support
  · exact congrArg Erdos1172Collapse.Condition.entries (hq i hi)
  · rw [off (f i) (fun k hk h => hi (f.injective h ▸ hk)),DFinsupp.notMem_support_iff.mp hi]
    rfl

def relabel (f : K ↪o L) (p : BelowCondition κ) : BelowCondition θ := (exists_relabel f p).choose
theorem relabel_entries (f : K ↪o L) (p : BelowCondition κ) (i : K) :
    ((relabel f p) (f i)).entries = (p i).entries.map (letter f i) := (exists_relabel f p).choose_spec.1 i
theorem relabel_off (f : K ↪o L) (p : BelowCondition κ) {y : L} (hy : y ∉ Set.range f) :
    relabel f p y = ⊤ := (exists_relabel f p).choose_spec.2 y hy

theorem relabel_le_iff (f : K ↪o L) (p q : BelowCondition κ) : relabel f p ≤ relabel f q ↔ p ≤ q := by
  constructor
  · intro h i
    have pre := (le_iff_prefixes.mp h) (f i)
    rw [relabel_entries,relabel_entries] at pre
    exact (List.prefix_map_iff_of_injective (letter f i).injective).mp pre
  · intro h y
    by_cases hy : y ∈ Set.range f
    · obtain ⟨i,rfl⟩ := hy
      rw [Erdos1172Collapse.le_iff_prefix,relabel_entries,relabel_entries]
      exact ((le_iff_prefixes.mp h) i).map _
    · rw [relabel_off f q hy]
      exact le_top

/-- Both the occupied coordinates and every ordinal written into those coordinates. -/
def labels {κ : Cardinal.{u}} (p : BelowCondition κ) : Finset κ.ord.ToType := by
  classical
  exact p.support.biUnion fun i => insert i ((p i).entries.map Subtype.val).toFinset

theorem support_mem_labels (p : BelowCondition κ) {i : K} (h : i ∈ p.support) : i ∈ labels p := by
  classical
  exact Finset.mem_biUnion.mpr ⟨i,h,Finset.mem_insert_self _ _⟩

theorem letter_mem_labels (p : BelowCondition κ) {i : K} (x : Set.Iio i) (h : x ∈ (p i).entries) :
    x.val ∈ labels p := by
  classical
  have hi : i ∈ p.support := DFinsupp.mem_support_iff.mpr (fun he => by rw [he] at h; exact List.not_mem_nil h)
  exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_insert_of_mem
    (List.mem_toFinset.mpr (List.mem_map.mpr ⟨x,h,rfl⟩))⟩

theorem relabel_labels (f : K ↪o L) (p : BelowCondition κ) :
    (labels (relabel f p) : Set L) ⊆ Set.range f := by
  classical
  intro y hy
  obtain ⟨k,hk,h⟩ := Finset.mem_biUnion.mp (show y ∈ labels (relabel f p) from hy)
  have kr : k ∈ Set.range f := by
    by_contra hn
    exact (DFinsupp.mem_support_iff.mp hk) (relabel_off f p hn)
  obtain ⟨i,rfl⟩ := kr
  rcases Finset.mem_insert.mp h with rfl | hm
  · exact ⟨i,rfl⟩
  · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
    rw [relabel_entries] at hx
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hx
    exact ⟨v.val,rfl⟩

theorem exists_relabel_eq (f : K ↪o L) (q : BelowCondition θ) (hq : (labels q : Set L) ⊆ Set.range f) :
    ∃ p : BelowCondition κ, relabel f p = q := by
  classical
  have pre (i : K) (x : {x // x ∈ (q (f i)).entries}) : ∃ v : Set.Iio i, letter f i v = x.val := by
    obtain ⟨v,hv⟩ := hq (letter_mem_labels q _ x.property)
    exact ⟨⟨v,f.lt_iff_lt.mp (hv ▸ x.val.property)⟩,Subtype.ext hv⟩
  let word (i : K) : Erdos1172Collapse.Condition (Set.Iio i) :=
    ⟨(q (f i)).entries.attach.map (fun x => (pre i x).choose)⟩
  have mapped (i : K) : (word i).entries.map (letter f i) = (q (f i)).entries := by
    simp only [word,List.map_map]
    exact (List.map_congr_left fun x _ => (pre i x).choose_spec).trans (List.attach_map_subtype_val _)
  let s := q.support.preimage f f.injective.injOn
  let p : BelowCondition κ := DFinsupp.mk s (fun i => word i.val)
  have atPoint (i : K) : p i = word i := by
    change (DFinsupp.mk s _ : BelowCondition κ) i = _
    rw [DFinsupp.mk_apply]
    split
    · rfl
    next hi =>
      have hq' : q (f i) = 0 := DFinsupp.notMem_support_iff.mp (by simpa only [s,Finset.mem_preimage] using hi)
      apply Erdos1172Collapse.Condition.ext
      have hempty := mapped i
      rw [hq'] at hempty
      exact (List.map_eq_nil_iff.mp hempty).symm
  refine ⟨p,DFinsupp.ext fun y => ?_⟩
  by_cases hy : y ∈ Set.range f
  · obtain ⟨i,rfl⟩ := hy
    apply Erdos1172Collapse.Condition.ext
    rw [relabel_entries,atPoint,mapped]
  · rw [relabel_off f p hy]
    exact (DFinsupp.notMem_support_iff.mp (fun h => hy (hq (support_mem_labels q h)))).symm

end Erdos1172LevyCollapse.Preparation
