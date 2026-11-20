/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaCollapseTree
public import Erdos1172.Part4ShioyaTreeEvaluation
public import Mathlib.Order.Bounds.OrderIso

@[expose] public section

/-! # A continuous projection from the collapse onto a completely closed poset

On the ordinal-domain dense subset, decode the sequence of letters in the
target partial order. Any strengthening of the decoded condition can be
realized exactly by appending one letter. Continuity follows because each
coordinate of an infimum already occurs in a path in the family.
-/

set_option autoImplicit false
noncomputable section
universe u
namespace Erdos1172Shioya.Collapse

variable {κ : Cardinal.{u}} {X P : Type u}

namespace Sequence

variable (d : X → P) (p₀ : P)

def labels (s : Sequence κ X) (i : κ.ord.ToType) : P :=
  if h : i < s.length then d (s.letter ⟨i,h⟩) else p₀

private theorem labels_at (s : Sequence κ X) {i : κ.ord.ToType} (h : i < s.length) :
    labels d p₀ s i = d (s.letter ⟨i,h⟩) := dif_pos h

private theorem labels_agree {s t : Sequence κ X} (hst : s ≤ t) {i : κ.ord.ToType} (hi : i < t.length) :
    labels d p₀ t i = labels d p₀ s i := by
  obtain ⟨h, ha⟩ := (le_iff s t).mp hst
  rw [labels_at d p₀ t hi, labels_at d p₀ s (hi.trans_le h), ha ⟨i,hi⟩]

theorem length_small (s : Sequence κ X) : Cardinal.mk (Set.Iio s.length) < κ := by
  simpa using Cardinal.mk_Iio_lt s.length (by simp)

variable [PartialOrder P] (hP : ShortInfima κ P)

def evaluation (s : Sequence κ X) : P :=
  Path.value hP (labels d p₀ s) s.length (length_small s)

theorem evaluation_mono : Monotone (evaluation (κ := κ) d p₀ hP) :=
  fun s t h => Path.value_extension hP (length_small t) (length_small s)
    ((le_iff s t).mp h).choose (fun _ hi => labels_agree d p₀ h hi)

theorem evaluation_append (s : Sequence κ X) (hκ : Cardinal.aleph0 ≤ κ) (x : X)
    (hx : d x ≤ evaluation d p₀ hP s) : evaluation d p₀ hP (s.append hκ x) = d x := by
  have ha : labels d p₀ (s.append hκ x) s.length = d x := by
    rw [labels_at d p₀ _ ((s.lt_append_length_iff hκ x _).mpr le_rfl), s.append_at]
  exact (Path.value_successor hP (length_small s) (length_small _)
    (s.lt_append_length_iff hκ x) (fun _ hi => labels_agree d p₀ (s.append_le hκ x) hi)
    (ha.le.trans hx)).trans ha

theorem le_evaluation_empty (hκ : 0 < κ) (p : P) : p ≤ evaluation d p₀ hP (empty hκ) := by
  apply (Path.value_glb hP _ _ _).2
  rintro _ ⟨i,hi,_,_⟩
  have hlt : i.toOrd.val < (empty (X := X) hκ).length.toOrd.val := Ordinal.ToType.mk.symm.strictMono hi
  rw [empty_length] at hlt
  exact (not_lt_of_ge (bot_le : (0 : Ordinal.{u}) ≤ i.toOrd.val) hlt).elim

theorem evaluation_isGLB {L : Type u} (f : L → Sequence κ X) (s : Sequence κ X)
    (hs : IsGLB (Set.range f) s) : IsGLB (Set.range (fun t => evaluation d p₀ hP (f t))) (evaluation d p₀ hP s) :=
  Path.value_union hP (fun t => labels d p₀ (f t)) (fun t => (f t).length) (fun t => length_small (f t))
    (labels d p₀ s) s.length (length_small s) (fun t => ((le_iff _ _).mp (hs.1 (Set.mem_range_self t))).choose)
    (fun t _ hi => labels_agree d p₀ (hs.1 (Set.mem_range_self t)) hi)
    (fun i hi => exists_cover_of_isGLB f s hs ⟨i,hi⟩)

end Sequence

variable [PartialOrder P]

/-- The domain is the actual set of ordinal-domain partial assignments in the collapse. -/
def treeProjection [Nonempty X] (hκ : κ.IsRegular) (hP : ShortInfima κ P)
    (d : X → P) (hd : Function.Surjective d) (p₀ : P) : PartialProjection κ (Condition κ X) P := by
  let e : ordinalDomain κ X ≃o Sequence κ X := Sequence.orderIso.symm
  let g := Sequence.evaluation d p₀ hP
  have hmono := Sequence.evaluation_mono d p₀ hP
  have hω := hκ.aleph0_le
  have hpos := Cardinal.aleph0_pos.trans_le hω
  refine { dom := ordinalDomain κ X
           dense := fun p => ?_
           proj := ⟨fun p => g (e p), hmono.comp e.monotone⟩
           reaches := fun p => ?_
           lifts := fun p q h => ?_
           closed := fun _ _ _ _ f _ p hp => ordinalDomain_closed f p hp
           continuous := fun L _ _ _ f _ p hp => ?_ }
  · obtain ⟨q,hq,hle⟩ := ordinalDomain_dense hκ p
    exact ⟨⟨q,hq⟩,hle⟩
  · obtain ⟨x,rfl⟩ := hd p
    let s : Sequence κ X := Sequence.empty hpos
    refine ⟨e.symm (s.append hω x), ?_⟩
    change g (e (e.symm _)) ≤ _
    rw [e.apply_symm_apply]
    exact (s.evaluation_append d p₀ hP hω x (Sequence.le_evaluation_empty d p₀ hP hpos _)).le
  · obtain ⟨x,rfl⟩ := hd q
    refine ⟨e.symm ((e p).append hω x), e.symm_apply_le.mpr ((e p).append_le hω x), ?_⟩
    change g (e (e.symm _)) ≤ _
    rw [e.apply_symm_apply]
    exact ((e p).evaluation_append d p₀ hP hω x h).le
  · have hp' : IsGLB (Set.range f) p := by
      refine ⟨Set.forall_mem_range.mpr (fun i => hp.1 (Set.mem_range_self i)), ?_⟩
      intro q hq
      exact hp.2 (Set.forall_mem_range.mpr (fun i => hq (Set.mem_range_self i)))
    have he : IsGLB (Set.range (fun i => e (f i))) (e p) := by
      change IsGLB (Set.range (e ∘ f)) (e p)
      rwa [Set.range_comp, e.isGLB_image']
    exact Sequence.evaluation_isGLB d p₀ hP _ _ he

end Erdos1172Shioya.Collapse
