/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaCollapseTreeProjection

@[expose] public section

/-! # Collapse paths read over a specified projection

A base point that decides the projected letters of a path can be
strengthened without changing its reading of those letters. The extended
path may then record any strengthening whose projection is the new base.
-/

set_option autoImplicit false
noncomputable section
universe u
namespace Erdos1172Shioya
namespace SynchronizedPath

open Collapse
variable {κ : Cardinal.{u}} {X Q P : Type u} [PartialOrder Q] [PartialOrder P]
variable (π : PartialProjection κ Q P) (d : X → π.dom) (t : π.dom)

def Decides (p : P) (s : Sequence κ X) : Prop :=
  ∀ i : Set.Iio s.length, p ≤ π.proj (d (s.letter i)) ∨
    ¬ ∃ r : P, r ≤ p ∧ r ≤ π.proj (d (s.letter i))

def label (p : P) (s : Sequence κ X) (i : κ.ord.ToType) : π.dom := by
  classical
  exact if h : i < s.length then
    if p ≤ π.proj (d (s.letter ⟨i,h⟩)) then d (s.letter ⟨i,h⟩) else t
    else t

theorem label_agree {p r : P} (hr : r ≤ p) {s v : Sequence κ X} (hv : v ≤ s)
    (hd : Decides π d p s) {i : κ.ord.ToType} (hi : i < s.length) :
    label π d t p s i = label π d t r v i := by
  classical
  obtain ⟨hl, hf⟩ := (Sequence.le_iff v s).mp hv
  simp only [label, dif_pos hi, dif_pos (hi.trans_le hl), hf ⟨i,hi⟩]
  rcases hd ⟨i,hi⟩ with h | h
  · simp only [if_pos h, if_pos (hr.trans h)]
  · have h₁ : ¬ p ≤ π.proj (d (s.letter ⟨i,hi⟩)) := fun hp => h ⟨p,le_rfl,hp⟩
    have h₂ : ¬ r ≤ π.proj (d (s.letter ⟨i,hi⟩)) := fun hp => h ⟨r,hr,hp⟩
    simp only [if_neg h₁, if_neg h₂]

theorem small (s : Sequence κ X) : Cardinal.mk (Set.Iio s.length) < κ := by
  simpa using Cardinal.mk_Iio_lt s.length (by simp)

variable (hD : ShortInfima κ π.dom)

def value (p : P) (s : Sequence κ X) : π.dom :=
  Path.value hD (label π d t p s) s.length (small s)

theorem value_mono {p r : P} (hr : r ≤ p) {s v : Sequence κ X} (hv : v ≤ s)
    (hd : Decides π d p s) : value π d t hD r v ≤ value π d t hD p s :=
  Path.value_extension hD (small s) (small v) ((Sequence.le_iff v s).mp hv).choose
    (fun _ hi => label_agree π d t hr hv hd hi)

theorem append_decides {p r : P} (hr : r ≤ p) (s : Sequence κ X) (hd : Decides π d p s)
    (hκ : Cardinal.aleph0 ≤ κ) (x : X) (hx : r ≤ π.proj (d x)) :
    Decides π d r (s.append hκ x) := by
  intro i
  have hl := (s.lt_append_length_iff hκ x i.val).mp i.property
  rcases lt_or_eq_of_le hl with hi | hi
  · have hf := ((Sequence.le_iff _ _).mp (s.append_le hκ x)).choose_spec ⟨i.val,hi⟩
    rw [show (s.append hκ x).letter i = s.letter ⟨i.val,hi⟩ from hf]
    rcases hd ⟨i.val,hi⟩ with h | h
    · exact Or.inl (hr.trans h)
    · exact Or.inr (fun ⟨q,hq,ha⟩ => h ⟨q,hq.trans hr,ha⟩)
  · have he : i = ⟨s.length, (s.lt_append_length_iff hκ x _).mpr le_rfl⟩ := Subtype.ext hi
    rw [he, s.append_at]
    exact Or.inl hx

theorem value_append {p r : P} (hr : r ≤ p) (s : Sequence κ X) (hd : Decides π d p s)
    (hκ : Cardinal.aleph0 ≤ κ) (x : X) (hx : r ≤ π.proj (d x)) (hq : d x ≤ value π d t hD p s) :
    value π d t hD r (s.append hκ x) = d x := by
  classical
  have ha : label π d t r (s.append hκ x) s.length = d x := by
    simp only [label, dif_pos ((s.lt_append_length_iff hκ x _).mpr le_rfl), s.append_at, if_pos hx]
  exact (Path.value_successor hD (small s) (small _) (s.lt_append_length_iff hκ x)
    (fun _ hi => label_agree π d t hr (s.append_le hκ x) hd hi) (ha.le.trans hq)).trans ha

theorem value_union {L : Type u} (ps : L → P) (ss : L → Sequence κ X) (p : P) (s : Sequence κ X)
    (hp : ∀ l, p ≤ ps l) (hs : IsGLB (Set.range ss) s) (hd : ∀ l, Decides π d (ps l) (ss l)) :
    IsGLB (Set.range (fun l => value π d t hD (ps l) (ss l))) (value π d t hD p s) :=
  Path.value_union hD (fun l => label π d t (ps l) (ss l)) (fun l => (ss l).length) (fun l => small (ss l))
    (label π d t p s) s.length (small s)
    (fun l => ((Sequence.le_iff s (ss l)).mp (hs.1 (Set.mem_range_self l))).choose)
    (fun l _ hi => label_agree π d t (hp l) (hs.1 (Set.mem_range_self l)) (hd l) hi)
    (fun i hi => Sequence.exists_cover_of_isGLB ss s hs ⟨i,hi⟩)

end SynchronizedPath
end Erdos1172Shioya
