/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaTreeEvaluation

@[expose] public section

/-! # Evaluating paths in the domain of a continuous projection

The projected evaluation is the infimum of the images of the letters accepted
in the domain. This also gives its value on the empty path and its continuity
at a short descending family of path evaluations.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Erdos1172Shioya.PartialProjection
open Collapse

variable {κ : Cardinal.{u}} {P Q : Type u} [PartialOrder P] [PartialOrder Q]
variable (π : PartialProjection κ Q P)

private theorem dom_isGLB_of_val {L : Type u} (f : L → π.dom) (x : π.dom)
    (hx : IsGLB (Set.range (fun i => (f i).val)) x.val) : IsGLB (Set.range f) x := by
  refine ⟨Set.forall_mem_range.mpr (fun i => hx.1 (Set.mem_range_self i)), ?_⟩
  intro y hy
  exact hx.2 (Set.forall_mem_range.mpr (fun i => hy (Set.mem_range_self i)))

theorem domShortInfima (hQ : ShortInfima κ Q) : ShortInfima κ π.dom := by
  intro L _ _ hL f hf
  obtain ⟨x, hx⟩ := hQ L hL (fun i => (f i).val) hf
  let z : π.dom := ⟨x, π.closed L hL f hf x hx⟩
  exact ⟨z, π.dom_isGLB_of_val f z hx⟩

variable {L : Type u} [LinearOrder L] [WellFoundedLT L]

theorem val_isGLB (hQ : ShortInfima κ Q) (hL : Cardinal.mk L < κ)
    (f : L → π.dom) (hf : Antitone f) (x : π.dom) (hx : IsGLB (Set.range f) x) :
    IsGLB (Set.range (fun i => (f i).val)) x.val := by
  obtain ⟨y, hy⟩ := hQ L hL (fun i => (f i).val) hf
  let z : π.dom := ⟨y, π.closed L hL f hf y hy⟩
  have he : x = z := hx.unique (π.dom_isGLB_of_val f z hy)
  exact he.symm ▸ hy

theorem proj_isGLB (hQ : ShortInfima κ Q) (hL : Cardinal.mk L < κ)
    (f : L → π.dom) (hf : Antitone f) (x : π.dom) (hx : IsGLB (Set.range f) x) :
    IsGLB (Set.range (fun i => π.proj (f i))) (π.proj x) :=
  π.continuous L hL f hf x (π.val_isGLB hQ hL f hf x hx)

variable {I : Type u} [LinearOrder I] [WellFoundedLT I]

private theorem map_pathValue_isGLB {R : Type u} [PartialOrder R] (a : π.dom → R)
    (hmap : ∀ (J : Type u) [LinearOrder J] [WellFoundedLT J], Cardinal.mk J < κ →
      ∀ (g : J → π.dom), Antitone g → ∀ x, IsGLB (Set.range g) x →
        IsGLB (Set.range (fun i => a (g i))) (a x))
    (hQ : ShortInfima κ Q) (f : I → π.dom) (l : I) (hl : Cardinal.mk (Set.Iio l) < κ) :
    IsGLB (a '' Path.selected f l) (a (Path.value (π.domShortInfima hQ) f l hl)) := by
  let J := {i : I // i < l ∧ Path.accepted f i}
  let g (i : J) := f i.val
  have hJ : Cardinal.mk J < κ := (Cardinal.mk_le_of_injective
    (f := fun i : J => (⟨i.val, i.property.1⟩ : Set.Iio l))
    (fun _ _ h => Subtype.ext (congrArg (fun j : Set.Iio l => j.val) h))).trans_lt hl
  have hg : Antitone g := by
    intro i j hij
    rcases lt_or_eq_of_le hij with hij | rfl
    · exact (Path.accepted_iff f j.val).mp j.property.2 i.val hij i.property.2
    · exact le_rfl
  have hr : Set.range g = Path.selected f l :=
    Set.ext fun _ => ⟨fun ⟨i, hi⟩ => ⟨i.val, i.property.1, i.property.2, hi⟩,
      fun ⟨i, hi, ha, he⟩ => ⟨⟨i, hi, ha⟩, he⟩⟩
  have hv := Path.value_glb (π.domShortInfima hQ) f l hl
  rw [← hr] at hv ⊢
  rw [← Set.range_comp]
  exact hmap J hJ g hg _ hv

theorem proj_pathValue_isGLB (hQ : ShortInfima κ Q) (f : I → π.dom) (l : I)
    (hl : Cardinal.mk (Set.Iio l) < κ) :
    IsGLB (π.proj '' Path.selected f l) (π.proj (Path.value (π.domShortInfima hQ) f l hl)) :=
  π.map_pathValue_isGLB π.proj (fun _ _ _ => π.proj_isGLB hQ) hQ f l hl

theorem accepted_val (f : I → π.dom) (i : I) :
    Path.accepted (fun j => (f j).val) i ↔ Path.accepted f i := by
  induction i using (wellFounded_lt : WellFounded ((· < ·) : I → I → Prop)).induction with
  | h i ih =>
    rw [Path.accepted_iff, Path.accepted_iff]
    exact ⟨fun h j hj ha => h j hj ((ih j hj).mpr ha), fun h j hj ha => h j hj ((ih j hj).mp ha)⟩

theorem val_pathValue (hQ : ShortInfima κ Q) (f : I → π.dom) (l : I)
    (hl : Cardinal.mk (Set.Iio l) < κ) :
    (Path.value (π.domShortInfima hQ) f l hl).val = Path.value hQ (fun i => (f i).val) l hl := by
  have hv := π.map_pathValue_isGLB Subtype.val (fun _ _ _ => π.val_isGLB hQ) hQ f l hl
  have he : Subtype.val '' Path.selected f l = Path.selected (fun i => (f i).val) l := by
    ext q
    constructor
    · rintro ⟨_, ⟨i, hi, ha, rfl⟩, rfl⟩
      exact ⟨i, hi, (π.accepted_val f i).mpr ha, rfl⟩
    · rintro ⟨i, hi, ha, rfl⟩
      exact ⟨f i, ⟨i, hi, (π.accepted_val f i).mp ha, rfl⟩, rfl⟩
  rw [he] at hv
  exact hv.unique (Path.value_glb hQ _ l hl)

theorem le_proj_pathValue (hQ : ShortInfima κ Q) (f : I → π.dom) (l : I)
    (hl : Cardinal.mk (Set.Iio l) < κ) (p : P)
    (hp : ∀ i < l, Path.accepted f i → p ≤ π.proj (f i)) :
    p ≤ π.proj (Path.value (π.domShortInfima hQ) f l hl) := by
  apply (π.proj_pathValue_isGLB hQ f l hl).2
  rintro _ ⟨_, ⟨i, hi, ha, rfl⟩, rfl⟩
  exact hp i hi ha

theorem pathValue_empty_isGreatest (hQ : ShortInfima κ Q) (f : I → π.dom) (l : I)
    (hl : Cardinal.mk (Set.Iio l) < κ) (hempty : ∀ i, ¬ i < l) :
    IsGreatest Set.univ (Path.value (π.domShortInfima hQ) f l hl) ∧
      IsGreatest Set.univ (π.proj (Path.value (π.domShortInfima hQ) f l hl)) := by
  refine ⟨⟨Set.mem_univ _, fun _ _ => (Path.value_glb (π.domShortInfima hQ) f l hl).2 ?_⟩,
    ⟨Set.mem_univ _, fun p _ => π.le_proj_pathValue hQ f l hl p (fun i hi _ => (hempty i hi).elim)⟩⟩
  rintro _ ⟨i, hi, _, _⟩
  exact (hempty i hi).elim

theorem proj_pathValue_family_isGLB (hQ : ShortInfima κ Q) (hL : Cardinal.mk L < κ)
    (fs : L → I → π.dom) (ls : L → I) (hs : ∀ t, Cardinal.mk (Set.Iio (ls t)) < κ)
    (f : I → π.dom) (l : I) (hl : Cardinal.mk (Set.Iio l) < κ)
    (hdesc : Antitone (fun t => Path.value (π.domShortInfima hQ) (fs t) (ls t) (hs t)))
    (hglb : IsGLB (Set.range (fun t => Path.value (π.domShortInfima hQ) (fs t) (ls t) (hs t)))
      (Path.value (π.domShortInfima hQ) f l hl)) :
    IsGLB (Set.range (fun t => π.proj (Path.value (π.domShortInfima hQ) (fs t) (ls t) (hs t))))
      (π.proj (Path.value (π.domShortInfima hQ) f l hl)) :=
  π.proj_isGLB hQ hL _ hdesc _ hglb

end Erdos1172Shioya.PartialProjection
