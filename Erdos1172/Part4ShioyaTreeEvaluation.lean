/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ClosedPartialProjection

@[expose] public section

/-! # Evaluating a collapse path in a completely closed poset

Read each letter of a path if it strengthens every previously read letter.
The selected letters descend, so their infimum exists at all small stages.
Appending any strengthening realizes it exactly. At a union of paths, the
evaluation is the infimum of the earlier evaluations.
-/

set_option autoImplicit false
noncomputable section
universe u
namespace Erdos1172Shioya.Collapse
namespace Path

variable {κ : Cardinal.{u}} {P : Type u} [PartialOrder P]
variable {I : Type u} [LinearOrder I] [WellFoundedLT I]

def accepted (f : I → P) : I → Prop :=
  wellFounded_lt.fix fun i earlier => ∀ j, (h : j < i) → earlier j h → f i ≤ f j

theorem accepted_iff (f : I → P) (i : I) :
    accepted f i ↔ ∀ j < i, accepted f j → f i ≤ f j := by
  unfold accepted
  rw [WellFounded.fix_eq]

theorem accepted_congr {f g : I → P} (i : I) (h : ∀ j ≤ i, f j = g j) :
    accepted f i ↔ accepted g i := by
  induction i using (wellFounded_lt : WellFounded ((· < ·) : I → I → Prop)).induction with
  | h i ih =>
    rw [accepted_iff, accepted_iff]
    constructor <;> intro ha j hj hprior
    · rw [← h i le_rfl, ← h j hj.le]
      exact ha j hj ((ih j hj (fun k hk => h k (hk.trans hj.le))).mpr hprior)
    · rw [h i le_rfl, h j hj.le]
      exact ha j hj ((ih j hj (fun k hk => h k (hk.trans hj.le))).mp hprior)

def selected (f : I → P) (l : I) : Set P :=
  {p | ∃ i < l, accepted f i ∧ f i = p}

theorem selected_mono {f g : I → P} {l m : I} (hl : l ≤ m)
    (h : ∀ i < l, f i = g i) : selected f l ⊆ selected g m := by
  rintro _ ⟨i, hi, ha, rfl⟩
  exact ⟨i, hi.trans_le hl, (accepted_congr i (fun j hj => h j (hj.trans_lt hi))).mp ha,
    (h i hi).symm⟩

theorem selected_hasGLB (hP : ShortInfima κ P) (f : I → P) (l : I)
    (hl : Cardinal.mk (Set.Iio l) < κ) : ∃ p, IsGLB (selected f l) p := by
  let J := {i : I // i < l ∧ accepted f i}
  have hJ : Cardinal.mk J < κ := (Cardinal.mk_le_of_injective
    (f := fun i : J => (⟨i.val, i.property.1⟩ : Set.Iio l))
    (fun _ _ h => Subtype.ext (congrArg (fun j : Set.Iio l => j.val) h))).trans_lt hl
  have hf : Antitone (fun i : J => f i.val) := by
    intro i j hij
    rcases lt_or_eq_of_le hij with hij | rfl
    · exact (accepted_iff f j.val).mp j.property.2 i.val hij i.property.2
    · exact le_rfl
  obtain ⟨p, hp⟩ := hP J hJ _ hf
  have he : Set.range (fun i : J => f i.val) = selected f l :=
    Set.ext fun _ => ⟨fun ⟨i,hi⟩ => ⟨i.val,i.property.1,i.property.2,hi⟩,
      fun ⟨i,hi,ha,he⟩ => ⟨⟨i,hi,ha⟩,he⟩⟩
  exact ⟨p, he ▸ hp⟩

def value (hP : ShortInfima κ P) (f : I → P) (l : I) (hl : Cardinal.mk (Set.Iio l) < κ) : P :=
  (selected_hasGLB hP f l hl).choose

theorem value_glb (hP : ShortInfima κ P) (f : I → P) (l : I) (hl : Cardinal.mk (Set.Iio l) < κ) :
    IsGLB (selected f l) (value hP f l hl) :=
  (selected_hasGLB hP f l hl).choose_spec

theorem value_extension (hP : ShortInfima κ P) {f g : I → P} {l m : I}
    (hl : Cardinal.mk (Set.Iio l) < κ) (hm : Cardinal.mk (Set.Iio m) < κ)
    (hle : l ≤ m) (h : ∀ i < l, f i = g i) : value hP g m hm ≤ value hP f l hl :=
  (value_glb hP f l hl).2 fun _ hx => (value_glb hP g m hm).1 (selected_mono hle h hx)

theorem value_successor (hP : ShortInfima κ P) {f g : I → P} {l m : I}
    (hl : Cardinal.mk (Set.Iio l) < κ) (hm : Cardinal.mk (Set.Iio m) < κ)
    (hs : ∀ i, i < m ↔ i ≤ l) (h : ∀ i < l, f i = g i)
    (hg : g l ≤ value hP f l hl) : value hP g m hm = g l := by
  have hlow (i : I) (hi : i < l) (ha : accepted g i) : g l ≤ g i := by
    have ha' := (accepted_congr i (fun j hj => h j (hj.trans_lt hi))).mpr ha
    exact (hg.trans ((value_glb hP f l hl).1 ⟨i,hi,ha',rfl⟩)).trans_eq (h i hi)
  have ha := (accepted_iff g l).mpr hlow
  refine le_antisymm ((value_glb hP g m hm).1 ⟨l,(hs l).mpr le_rfl,ha,rfl⟩)
    ((value_glb hP g m hm).2 ?_)
  rintro _ ⟨i,hi,hai,rfl⟩
  rcases lt_or_eq_of_le ((hs i).mp hi) with hi | rfl
  · exact hlow i hi hai
  · exact le_rfl

theorem value_union {L : Type u} (hP : ShortInfima κ P) (fs : L → I → P) (ls : L → I)
    (hs : ∀ t, Cardinal.mk (Set.Iio (ls t)) < κ) (f : I → P) (l : I) (hl : Cardinal.mk (Set.Iio l) < κ)
    (hle : ∀ t, ls t ≤ l) (h : ∀ t i, i < ls t → fs t i = f i)
    (hcover : ∀ i < l, ∃ t, i < ls t) :
    IsGLB (Set.range (fun t => value hP (fs t) (ls t) (hs t))) (value hP f l hl) := by
  refine ⟨Set.forall_mem_range.mpr (fun t => value_extension hP (hs t) hl (hle t) (h t)), ?_⟩
  intro q hq
  apply (value_glb hP f l hl).2
  rintro _ ⟨i,hi,hai,rfl⟩
  obtain ⟨t,ht⟩ := hcover i hi
  have hat := (accepted_congr i (fun j hj => h t j (hj.trans_lt ht))).mpr hai
  exact (hq (Set.mem_range_self t)).trans ((value_glb hP (fs t) (ls t) (hs t)).1
    ⟨i,ht,hat,h t i ht⟩)

end Path
end Erdos1172Shioya.Collapse
