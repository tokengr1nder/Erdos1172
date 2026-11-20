/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaSynchronizedPath
public import Erdos1172.Part4ShioyaProjectedPath
public import Erdos1172.Part4ShioyaSimultaneousDecision

@[expose] public section

/-! # A relative projection commuting with a prescribed base

For a projection from Q to P, a pair consisting of a base point and a collapse
path is synchronized when the base decides all the projected letters and is
the exact projection of the path value. Such pairs form a closed dense domain.
On it, the decoded Q-condition projects back to the original first coordinate.
-/

set_option autoImplicit false
noncomputable section
universe u
namespace Erdos1172Shioya.SynchronizedPath
open Collapse
variable {κ : Cardinal.{u}} {X Q P : Type u} [PartialOrder Q] [PartialOrder P]
variable (π : PartialProjection κ Q P) (d : X → π.dom) (t : π.dom)
variable (hQ : ShortInfima κ Q)

def domain : Set (P × Sequence κ X) :=
  {z | Decides π d z.1 z.2 ∧ π.proj (value π d t (π.domShortInfima hQ) z.1 z.2) = z.1}

theorem below_reading (ht : ∀ p : P, p ≤ π.proj t) (p : P) (s : Sequence κ X) :
    p ≤ π.proj (value π d t (π.domShortInfima hQ) p s) := by
  classical
  apply π.le_proj_pathValue hQ
  intro i hi _
  by_cases he : p ≤ π.proj (d (s.letter ⟨i,hi⟩))
  · simpa only [label, dif_pos hi, if_pos he] using he
  · simpa only [label, dif_pos hi, if_neg he] using ht p

private theorem coordinates_glb {L : Type u} (f : L → P × Sequence κ X) (z : P × Sequence κ X)
    (h : IsGLB (Set.range f) z) :
    IsGLB (Set.range (fun i => (f i).1)) z.1 ∧ IsGLB (Set.range (fun i => (f i).2)) z.2 := by
  have h₁ (i : L) := (h.1 (Set.mem_range_self i)).1
  have h₂ (i : L) := (h.1 (Set.mem_range_self i)).2
  refine ⟨⟨Set.forall_mem_range.mpr h₁, ?_⟩, ⟨Set.forall_mem_range.mpr h₂, ?_⟩⟩
  · intro p hp
    have hle : (p,z.2) ≤ z := h.2 (Set.forall_mem_range.mpr (fun i => ⟨hp (Set.mem_range_self i), h₂ i⟩))
    exact hle.1
  · intro s hs
    have hle : (z.1,s) ≤ z := h.2 (Set.forall_mem_range.mpr (fun i => ⟨h₁ i, hs (Set.mem_range_self i)⟩))
    exact hle.2

private theorem decides_union {L : Type u} (ps : L → P) (ss : L → Sequence κ X) (p : P)
    (s : Sequence κ X) (hp : ∀ i, p ≤ ps i) (hs : IsGLB (Set.range ss) s)
    (hd : ∀ i, Decides π d (ps i) (ss i)) : Decides π d p s := by
  intro i
  obtain ⟨j,hj⟩ := Sequence.exists_cover_of_isGLB ss s hs i
  have ha := ((Sequence.le_iff _ _).mp (hs.1 (Set.mem_range_self j))).choose_spec ⟨i.val,hj⟩
  rw [show s.letter i = (ss j).letter ⟨i.val,hj⟩ from ha]
  rcases hd j ⟨i.val,hj⟩ with h | h
  · exact Or.inl ((hp j).trans h)
  · exact Or.inr (fun ⟨q,hq,hr⟩ => h ⟨q,hq.trans (hp j),hr⟩)

theorem closeDomain {L : Type u} [LinearOrder L] [WellFoundedLT L] (hl : Cardinal.mk L < κ)
    (f : L → domain π d t hQ) (hf : Antitone f) (z : P × Sequence κ X)
    (hz : IsGLB (Set.range (fun i => (f i).val)) z) :
    z ∈ domain π d t hQ ∧ IsGLB (Set.range (fun i => (value π d t (π.domShortInfima hQ) (f i).val.1 (f i).val.2).val))
      (value π d t (π.domShortInfima hQ) z.1 z.2).val := by
  let g (i : L) := value π d t (π.domShortInfima hQ) (f i).val.1 (f i).val.2
  obtain ⟨hp, hs⟩ := coordinates_glb (fun i => (f i).val) z hz
  have hpg (i : L) := hp.1 (Set.mem_range_self i)
  have hd (i : L) := (f i).property.1
  have hv := value_union π d t (π.domShortInfima hQ) (fun i => (f i).val.1) (fun i => (f i).val.2)
    z.1 z.2 hpg hs hd
  have hanti : Antitone g := fun i j hij => value_mono π d t (π.domShortInfima hQ) (hf hij).1 (hf hij).2 (hd i)
  have him := π.proj_isGLB hQ hl g hanti _ hv
  have he : (fun i => π.proj (g i)) = fun i => (f i).val.1 := funext (fun i => (f i).property.2)
  rw [he] at him
  exact ⟨⟨decides_union π d _ _ _ _ hpg hs hd, him.unique hp⟩, π.val_isGLB hQ hl g hanti _ hv⟩

/-- The closure and lifting statements include all well-ordered chains of size below κ. -/
def relativeTree (hd : Function.Surjective d) (ht : ∀ p : P, p ≤ π.proj t)
    (hP : ShortInfima κ P) (hκ : Cardinal.aleph0 ≤ κ) : PartialProjection κ (P × Sequence κ X) Q := by
  let V := value π d t (π.domShortInfima hQ)
  refine { dom := domain π d t hQ
           dense := fun z => ?_
           proj := ⟨fun z => (V z.val.1 z.val.2).val, fun _ b h =>
             value_mono π d t (π.domShortInfima hQ) h.1 h.2 b.property.1⟩
           reaches := fun q => ?_
           lifts := fun z q hq => ?_
           closed := fun _ _ _ hl f hf z hz => (closeDomain π d t hQ hl f hf z hz).1
           continuous := fun _ _ _ hl f hf z hz => (closeDomain π d t hQ hl f hf z.val hz).2 }
  · obtain ⟨p,hp,hdec⟩ := exists_simultaneous_decision_below hP z.2.length
      (fun i => π.proj (d (z.2.letter i))) z.1
    obtain ⟨q,hq,hbase⟩ := π.lifts (V p z.2) p (below_reading π d t hQ ht p z.2)
    obtain ⟨x,hx⟩ := hd q
    let s := z.2.append hκ x
    have hv : V (π.proj q) s = q := (value_append π d t (π.domShortInfima hQ) hbase z.2 hdec hκ x
      (hx ▸ le_rfl) (hx ▸ hq)).trans hx
    exact ⟨⟨(π.proj q,s), append_decides π d hbase z.2 hdec hκ x (hx ▸ le_rfl), congrArg π.proj hv⟩,
      hbase.trans hp, z.2.append_le hκ x⟩
  · obtain ⟨a,ha⟩ := π.dense q
    obtain ⟨x,hx⟩ := hd a
    let s : Sequence κ X := Sequence.empty (Cardinal.aleph0_pos.trans_le hκ)
    have hempty {i : κ.ord.ToType} (hi : i < s.length) : False := by
      have hh : i.toOrd.val < s.length.toOrd.val := Ordinal.ToType.mk.symm.strictMono hi
      rw [show s.length.toOrd.val = 0 from Sequence.empty_length _] at hh
      exact (not_lt_of_ge (bot_le : (0 : Ordinal.{u}) ≤ i.toOrd.val) hh)
    have hdec : Decides π d (π.proj a) s := fun i => (hempty i.property).elim
    have htop : a ≤ V (π.proj a) s := (Path.value_glb _ _ _ _).2 (fun _ ⟨_,hl,_,_⟩ => (hempty hl).elim)
    have hv : V (π.proj a) (s.append hκ x) = a := (value_append π d t (π.domShortInfima hQ)
      le_rfl s hdec hκ x (hx ▸ le_rfl) (hx ▸ htop)).trans hx
    exact ⟨⟨(π.proj a,s.append hκ x), append_decides π d le_rfl s hdec hκ x (hx ▸ le_rfl),
      congrArg π.proj hv⟩, (congrArg Subtype.val hv).le.trans ha⟩
  · obtain ⟨a,ha⟩ := π.dense q
    have hav : a ≤ V z.val.1 z.val.2 := ha.trans hq
    have hab := (π.proj.monotone hav).trans_eq z.property.2
    obtain ⟨x,hx⟩ := hd a
    have hv := (value_append π d t (π.domShortInfima hQ) hab z.val.2 z.property.1 hκ x
      (hx ▸ le_rfl) (hx ▸ hav)).trans hx
    refine ⟨⟨(π.proj a,z.val.2.append hκ x), append_decides π d hab z.val.2 z.property.1 hκ x (hx ▸ le_rfl),
      congrArg π.proj hv⟩, ⟨hab,z.val.2.append_le hκ x⟩, (congrArg Subtype.val hv).le.trans ha⟩

theorem relativeTree_base (hd : Function.Surjective d) (ht : ∀ p : P, p ≤ π.proj t)
    (hP : ShortInfima κ P) (hκ : Cardinal.aleph0 ≤ κ)
    (z : (relativeTree π d t hQ hd ht hP hκ).dom) :
    ∃ h : (relativeTree π d t hQ hd ht hP hκ).proj z ∈ π.dom,
      π.proj ⟨(relativeTree π d t hQ hd ht hP hκ).proj z,h⟩ = z.val.1 :=
  ⟨(value π d t (π.domShortInfima hQ) z.val.1 z.val.2).property, z.property.2⟩

end Erdos1172Shioya.SynchronizedPath
