/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.Tactic.NormNum.Ordinal
public import Erdos1172.ForMathlib.SetTheory.Cardinal.GCHConsequences1172
public import Erdos1172.ForMathlib.SetTheory.Ordinal.CliqueExtension
public import Erdos1172.ForMathlib.SetTheory.Ordinal.DushnikMillerCountable

@[expose] public section

open Cardinal Ordinal Set Function

/-!
# The asymmetric Erdős--Rado relation under GCH

This file proves the classical relation `ω₃ → (ω₃, ω₂ + 1)²` from the
Generalized Continuum Hypothesis.  The proof constructs barrier seeds of
cardinality at most `ℵ₁` on a
stationary set of points of cofinality `ω₂`, uniformizes them using GCH, and
extracts a complementary clique of type `ω₃`.
-/

namespace ErdosRadoGCHAsym

abbrev W2 : Type := (ω_ 2 : Ordinal.{0}).ToType
abbrev W3 : Type := (ω_ 3 : Ordinal.{0}).ToType

/-- A point which is the supremum of a strictly increasing `ω₂`-sequence. -/
def IsOmegaTwoSup (top : W3) : Prop :=
  ∃ seq : W2 → W3, StrictMono seq ∧ IsLUB (Set.range seq) top

private theorem exists_mem_gt_previous
    (C : Set W3) (hC : IsCofinal C) (i : W2)
    (previous : ∀ j, j < i → W3) :
    ∃ x ∈ C, ∀ j (hj : j < i), previous j hj < x := by
  let prior : Set W3 := Set.range fun j : Set.Iio i ↦ previous j.1 j.2
  have hi : #(Set.Iio i) ≤ ℵ_ 1 := by
    apply Order.lt_succ_iff.mp
    rw [show Order.succ (ℵ_ 1 : Cardinal.{0}) = ℵ_ 2 by
      rw [Cardinal.succ_aleph]
      norm_num]
    simpa only [W2, Cardinal.mk_toType, Ordinal.card_omega] using
      Cardinal.mk_Iio_lt i (by simp [W2])
  have hprior : #prior ≤ ℵ_ 1 := by
    calc
      #prior ≤ #(Set.Iio i) := by
        simpa only [prior, Cardinal.lift_id] using
          (Cardinal.mk_range_le_lift
            (f := fun j : Set.Iio i ↦ previous j.1 j.2))
      _ ≤ ℵ_ 1 := hi
  have hnot : ¬ IsCofinal prior := by
    intro hcof
    have hle : Order.cof W3 ≤ #prior := Order.cof_le hcof
    have hcofW3 : Order.cof W3 = ℵ_ 3 := by
      calc
        Order.cof W3 = (ω_ 3 : Ordinal.{0}).cof := by
          exact Ordinal.cof_toType (ω_ 3 : Ordinal.{0})
        _ = ℵ_ 3 := by
          have hreg : (ℵ_ 3 : Cardinal.{0}).IsRegular := by
            rw [show (3 : Ordinal.{0}) = 2 + 1 by norm_num]
            exact Cardinal.isRegular_aleph_add_one 2
          simpa only [Cardinal.ord_aleph] using hreg.cof_ord
    rw [hcofW3] at hle
    have h02 : (ℵ_ 1 : Cardinal.{0}) < ℵ_ 3 :=
      Cardinal.aleph_lt_aleph.mpr (by norm_num)
    exact (not_le_of_gt h02) (hle.trans hprior)
  obtain ⟨bound, hbound⟩ := not_isCofinal_iff.mp hnot
  obtain ⟨x, hxC, hboundx⟩ := hC bound
  refine ⟨x, hxC, fun j hj ↦ ?_⟩
  exact (hbound _ ⟨⟨j, hj⟩, rfl⟩).trans_le hboundx

private noncomputable def clubSeqStep
    (C : Set W3) (hC : IsCofinal C) (i : W2)
    (previous : ∀ j, j < i → W3) : W3 :=
  Classical.choose (exists_mem_gt_previous C hC i previous)

private noncomputable def clubSeq
    (C : Set W3) (hC : IsCofinal C) : W2 → W3 :=
  WellFoundedLT.fix (clubSeqStep C hC)

private theorem clubSeq_eq_step (C : Set W3) (hC : IsCofinal C) (i : W2) :
    clubSeq C hC i =
      clubSeqStep C hC i (fun j _ ↦ clubSeq C hC j) := by
  change WellFoundedLT.fix (clubSeqStep C hC) i =
    clubSeqStep C hC i
      (fun j _ ↦ WellFoundedLT.fix (clubSeqStep C hC) j)
  rw [WellFoundedLT.fix_eq]

private theorem clubSeq_mem (C : Set W3) (hC : IsCofinal C) (i : W2) :
    clubSeq C hC i ∈ C := by
  rw [clubSeq_eq_step]
  exact (Classical.choose_spec (exists_mem_gt_previous C hC i
    (fun j _ ↦ clubSeq C hC j))).1

private theorem clubSeq_lt (C : Set W3) (hC : IsCofinal C)
    {i j : W2} (hij : i < j) : clubSeq C hC i < clubSeq C hC j := by
  rw [clubSeq_eq_step C hC j]
  exact (Classical.choose_spec (exists_mem_gt_previous C hC j
    (fun k _ ↦ clubSeq C hC k))).2 i hij

private theorem clubSeq_strictMono (C : Set W3) (hC : IsCofinal C) :
    StrictMono (clubSeq C hC) :=
  fun _ _ ↦ clubSeq_lt C hC

/-- The points which are `ω₂`-suprema form a stationary subset of `ω₃`. -/
theorem isStationary_isOmegaTwoSup_omegaThree :
    IsStationary {top : W3 | IsOmegaTwoSup top} := by
  classical
  let _ : Nonempty W2 := by
    change Nonempty ((ω_ 2 : Ordinal.{0}).ToType)
    rw [← Cardinal.ord_aleph]
    exact Cardinal.nonempty_ord_toType
      (Cardinal.aleph0_pos.trans_le (Cardinal.aleph0_le_aleph 2)).ne'
  let _ : Nonempty W3 := by
    change Nonempty ((ω_ 3 : Ordinal.{0}).ToType)
    rw [← Cardinal.ord_aleph]
    exact Cardinal.nonempty_ord_toType
      (Cardinal.aleph0_pos.trans_le (Cardinal.aleph0_le_aleph 3)).ne'
  let _ : OrderBot W3 := WellFoundedLT.toOrderBot W3
  let _ : ConditionallyCompleteLinearOrderBot W3 :=
    WellFoundedLT.conditionallyCompleteLinearOrderBot W3
  intro C hC
  let seq : W2 → W3 := clubSeq C hC.isCofinal
  have hseq : StrictMono seq := clubSeq_strictMono C hC.isCofinal
  have hseqMem : Set.range seq ⊆ C := by
    rintro _ ⟨i, rfl⟩
    exact clubSeq_mem C hC.isCofinal i
  have hseqCard : #(Set.range seq) = ℵ_ 2 := by
    rw [Cardinal.mk_range_eq seq hseq.injective]
    simp only [W2, Cardinal.mk_toType, Ordinal.card_omega]
  have hnotCofinal : ¬ IsCofinal (Set.range seq) := by
    intro hcof
    have hle : Order.cof W3 ≤ #(Set.range seq) := Order.cof_le hcof
    have hcofW3 : Order.cof W3 = ℵ_ 3 := by
      calc
        Order.cof W3 = (ω_ 3 : Ordinal.{0}).cof := by
          exact Ordinal.cof_toType (ω_ 3 : Ordinal.{0})
        _ = ℵ_ 3 := by
          have hreg : (ℵ_ 3 : Cardinal.{0}).IsRegular := by
            rw [show (3 : Ordinal.{0}) = 2 + 1 by norm_num]
            exact Cardinal.isRegular_aleph_add_one 2
          simpa only [Cardinal.ord_aleph] using hreg.cof_ord
    rw [hcofW3, hseqCard] at hle
    have h12 : (ℵ_ 2 : Cardinal.{0}) < ℵ_ 3 :=
      Cardinal.aleph_lt_aleph.mpr (by norm_num)
    exact (not_le_of_gt h12) hle
  have hbounded : BddAbove (Set.range seq) :=
    BddAbove.of_not_isCofinal hnotCofinal
  let top : W3 := sSup (Set.range seq)
  have htop : IsLUB (Set.range seq) top :=
    isLUB_csSup (Set.range_nonempty seq) hbounded
  have htopMem : top ∈ C :=
    hC.isLUB_mem hseqMem (Set.range_nonempty seq) htop
  exact ⟨top, ⟨seq, hseq, htop⟩, htopMem⟩

/-- Tops which minimally extend a seed of cardinality at most `ℵ₁`. -/
def smallBarrierCore (blue : SimpleGraph W3) (seed : Set W3) : Set W3 :=
  {top | (∀ y ∈ seed, y < top) ∧
    blue.IsClique (seed ∪ {top}) ∧
    ∀ middle, middle ∉ seed → middle < top →
      ¬ blue.IsClique (seed ∪ {middle, top})}

theorem mem_smallBarrierCore_iff
    {blue : SimpleGraph W3} {seed : Set W3} {top : W3} :
    top ∈ smallBarrierCore blue seed ↔
      (∀ y ∈ seed, y < top) ∧
      blue.IsClique (seed ∪ {top}) ∧
      ∀ middle, middle ∉ seed → middle < top →
        ¬ blue.IsClique (seed ∪ {middle, top}) :=
  Iff.rfl

theorem exists_new_clique_of_not_mem_smallBarrierCore
    {blue : SimpleGraph W3} {seed : Set W3} {top : W3}
    (hseed : ∀ y ∈ seed, y < top)
    (hclique : blue.IsClique (seed ∪ {top}))
    (hnot : top ∉ smallBarrierCore blue seed) :
    ∃ middle, middle ∉ seed ∧ middle < top ∧
      blue.IsClique (seed ∪ {middle, top}) := by
  rw [mem_smallBarrierCore_iff, not_and_or, not_and_or] at hnot
  rcases hnot with h | h | h
  · exact (h hseed).elim
  · exact (h hclique).elim
  · push Not at h
    exact h

private def priorSet (i : W2) (previous : ∀ j, j < i → W3) : Set W3 :=
  Set.range fun j : Set.Iio i ↦ previous j.1 j.2

private def IsCandidate (blue : SimpleGraph W3) (top : W3) (i : W2)
    (previous : ∀ j, j < i → W3) (x : W3) : Prop :=
  x ∉ priorSet i previous ∧ x < top ∧
    blue.IsClique (priorSet i previous ∪ {x, top})

private noncomputable def nextPoint (blue : SimpleGraph W3) (top : W3) (i : W2)
    (previous : ∀ j, j < i → W3) : W3 := by
  classical
  exact if h : Set.Nonempty {x | IsCandidate blue top i previous x} then
    Classical.choose h
  else top

private noncomputable def branch (blue : SimpleGraph W3) (top : W3) : W2 → W3 :=
  WellFoundedLT.fix (nextPoint blue top)

private theorem branch_eq_nextPoint (blue : SimpleGraph W3) (top : W3) (i : W2) :
    branch blue top i = nextPoint blue top i (fun j _ ↦ branch blue top j) := by
  change WellFoundedLT.fix (nextPoint blue top) i =
    nextPoint blue top i (fun j _ ↦ WellFoundedLT.fix (nextPoint blue top) j)
  rw [WellFoundedLT.fix_eq]

private theorem branch_candidate_of_exists
    {blue : SimpleGraph W3} {top : W3} {i : W2}
    (h : Set.Nonempty
      {x | IsCandidate blue top i (fun j _ ↦ branch blue top j) x}) :
    IsCandidate blue top i (fun j _ ↦ branch blue top j) (branch blue top i) := by
  classical
  rw [branch_eq_nextPoint]
  simp only [nextPoint, dif_pos h]
  exact Classical.choose_spec h

private theorem priorSet_mk_le_alephOne
    (i : W2) (previous : ∀ j, j < i → W3) :
    #(priorSet i previous) ≤ ℵ_ 1 := by
  have hi : #(Set.Iio i) ≤ ℵ_ 1 := by
    apply Order.lt_succ_iff.mp
    rw [show Order.succ (ℵ_ 1 : Cardinal.{0}) = ℵ_ 2 by
      rw [Cardinal.succ_aleph]
      norm_num]
    simpa only [W2, Cardinal.mk_toType, Ordinal.card_omega] using
      Cardinal.mk_Iio_lt i (by simp [W2])
  calc
    #(priorSet i previous) ≤ #(Set.Iio i) := by
      simpa only [priorSet, Cardinal.lift_id] using
        (Cardinal.mk_range_le_lift
          (f := fun j : Set.Iio i ↦ previous j.1 j.2))
    _ ≤ ℵ_ 1 := hi

private theorem branch_candidate_of_no_small_barrier
    (blue : SimpleGraph W3) (top : W3)
    (hbarrier : ∀ seed : Set W3, #seed ≤ ℵ_ 1 →
      top ∉ smallBarrierCore blue seed) :
    ∀ i : W2,
      IsCandidate blue top i (fun j _ ↦ branch blue top j)
        (branch blue top i) := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
      let seed := priorSet i (fun j _ ↦ branch blue top j)
      have hseedCard : #seed ≤ ℵ_ 1 :=
        priorSet_mk_le_alephOne i (fun j _ ↦ branch blue top j)
      have hseed_lt : ∀ y ∈ seed, y < top := by
        rintro _ ⟨j, rfl⟩
        exact (ih j j.2).2.1
      have hseedClique : blue.IsClique (seed ∪ {top}) := by
        intro x hx y hy hxy
        rcases hx with ⟨j, rfl⟩ | rfl <;>
          rcases hy with ⟨k, rfl⟩ | rfl
        · rcases lt_trichotomy j.1 k.1 with hjk | hjk | hkj
          · exact (ih k.1 k.2).2.2
              (by exact Or.inl ⟨⟨j.1, hjk⟩, rfl⟩)
              (by simp) hxy
          · have hjkeq : j = k := Subtype.ext hjk
            subst k
            exact (hxy rfl).elim
          · exact ((ih j.1 j.2).2.2
              (by exact Or.inl ⟨⟨k.1, hkj⟩, rfl⟩)
              (by simp) hxy.symm).symm
        · exact (ih j.1 j.2).2.2 (by simp) (by simp) hxy
        · exact (ih k.1 k.2).2.2 (by simp) (by simp) hxy
        · exact (hxy rfl).elim
      obtain ⟨middle, hmiddleNew, hmiddleTop, hmiddleClique⟩ :=
        exists_new_clique_of_not_mem_smallBarrierCore
          hseed_lt hseedClique (hbarrier seed hseedCard)
      apply branch_candidate_of_exists
      exact ⟨middle, hmiddleNew, hmiddleTop, hmiddleClique⟩

/-- If there is no blue clique of type `ω₂ + 1`, every top belongs to
the barrier core of a blue seed of cardinality at most `ℵ₁`. -/
theorem exists_smallBarrierCore_at_of_no_clique_type_omegaTwo_add_one
    (blue : SimpleGraph W3) (top : W3)
    (hno : ¬ ∃ B : Set W3, blue.IsClique B ∧ typeLT B = ω_ 2 + 1) :
    ∃ seed : Set W3, #seed ≤ ℵ_ 1 ∧
      top ∈ smallBarrierCore blue seed := by
  classical
  by_contra hresult
  push Not at hresult
  have hcandidate :=
    branch_candidate_of_no_small_barrier blue top hresult
  let seq : W2 → W3 := branch blue top
  have hseq_ne {i j : W2} (hij : i < j) : seq i ≠ seq j := by
    intro heq
    exact (hcandidate j).1 ⟨⟨i, hij⟩, heq⟩
  have hseqInjective : Injective seq := by
    intro i j hij
    rcases lt_trichotomy i j with hij' | hij' | hji'
    · exact (hseq_ne hij' hij).elim
    · exact hij'
    · exact (hseq_ne hji' hij.symm).elim
  have hseqTopClique : blue.IsClique (Set.range seq ∪ {top}) := by
    intro x hx y hy hxy
    rcases hx with ⟨i, rfl⟩ | rfl <;>
      rcases hy with ⟨j, rfl⟩ | rfl
    · rcases lt_trichotomy i j with hij | hij | hji
      · exact (hcandidate j).2.2
          (by exact Or.inl ⟨⟨i, hij⟩, rfl⟩)
          (Or.inr (Or.inl rfl)) hxy
      · subst j
        exact (hxy rfl).elim
      · exact ((hcandidate i).2.2
          (by exact Or.inl ⟨⟨j, hji⟩, rfl⟩)
          (Or.inr (Or.inl rfl)) hxy.symm).symm
    · exact (hcandidate i).2.2 (Or.inr (Or.inl rfl))
        (Or.inr (Or.inr rfl)) hxy
    · exact (hcandidate j).2.2 (Or.inr (Or.inr rfl))
        (Or.inr (Or.inl rfl)) hxy
    · exact (hxy rfl).elim
  have hseqCard : #(Set.range seq) = ℵ_ 2 := by
    rw [Cardinal.mk_range_eq seq hseqInjective]
    simp only [W2, Cardinal.mk_toType, Ordinal.card_omega]
  have homegaTwo_le : (ω_ 2 : Ordinal.{0}) ≤ typeLT (Set.range seq) := by
    simpa only [hseqCard, Cardinal.ord_aleph] using
      (Cardinal.ord_le_type
        ((· < ·) : Set.range seq → Set.range seq → Prop))
  obtain ⟨s, hsSub, hsType⟩ :=
    Ordinal.exists_subset_typeLT_eq (Set.range seq) homegaTwo_le
  have hsClique : blue.IsClique s :=
    hseqTopClique.subset (hsSub.trans (Set.subset_union_left))
  have hsLater : ∀ x ∈ s, x < top := by
    rintro x hx
    obtain ⟨i, rfl⟩ := hsSub hx
    exact (hcandidate i).2.1
  have hsAdj : ∀ x ∈ s, blue.Adj x top := by
    intro x hx
    exact hseqTopClique (Or.inl (hsSub hx)) (Or.inr rfl)
      (hsLater x hx).ne
  obtain ⟨z, hzClique, hzType⟩ :=
    blue.exists_clique_type_add_one_of_common_later
      hsClique hsType hsLater hsAdj
  exact hno ⟨z, hzClique, hzType⟩

/-- Two distinct tops in the same small barrier core have a red edge. -/
theorem not_adj_of_mem_smallBarrierCore
    {blue : SimpleGraph W3} {seed : Set W3} {x y : W3}
    (hx : x ∈ smallBarrierCore blue seed)
    (hy : y ∈ smallBarrierCore blue seed)
    (hxy : x ≠ y) : ¬ blue.Adj x y := by
  wlog hlt : x < y generalizing x y
  · exact fun hblue ↦ this hy hx hxy.symm
      (lt_of_le_of_ne (le_of_not_gt hlt) hxy.symm) hblue.symm
  intro hblue
  apply hy.2.2 x
  · exact fun hxSeed ↦ (lt_irrefl x) (hx.1 x hxSeed)
  · exact hlt
  · rw [show seed ∪ {x, y} = insert x (seed ∪ {y}) by ext; simp]
    apply hy.2.1.insert
    intro q hq hxq
    rcases hq with hqSeed | rfl
    · exact hx.2.1 (Or.inr rfl) (Or.inl hqSeed) hxq
    · exact hblue

/-- Every small barrier core is a clique in the complementary graph. -/
theorem compl_isClique_smallBarrierCore
    (blue : SimpleGraph W3) (seed : Set W3) :
    blueᶜ.IsClique (smallBarrierCore blue seed) := by
  intro x hx y hy hxy
  rw [SimpleGraph.compl_adj]
  exact ⟨hxy, not_adj_of_mem_smallBarrierCore hx hy hxy⟩

/-- A set of cardinality at most `ℵ₁` below an `ω₂`-supremum has a strict upper bound
which is still below that supremum. -/
theorem exists_strict_bound_of_small_of_IsOmegaTwoSup
    {top : W3} (htop : IsOmegaTwoSup top) {seed : Set W3}
    (hseedCard : #seed ≤ ℵ_ 1) (hseedTop : ∀ y ∈ seed, y < top) :
    ∃ cutoff : W3, cutoff < top ∧ ∀ y ∈ seed, y < cutoff := by
  classical
  obtain ⟨seq, hseq, htopLUB⟩ := htop
  have habove (y : seed) : ∃ i : W2, y.1 < seq i := by
    by_contra hnone
    push Not at hnone
    have htopLe : top ≤ y.1 := htopLUB.2 (by
      rintro _ ⟨i, rfl⟩
      exact hnone i)
    exact (not_le_of_gt (hseedTop y.1 y.2)) htopLe
  let index : seed → W2 := fun y ↦ Classical.choose (habove y)
  have hindexAbove (y : seed) : y.1 < seq (index y) :=
    Classical.choose_spec (habove y)
  have hindexCard : #(Set.range index) ≤ ℵ_ 1 := by
    exact Cardinal.mk_range_le.trans hseedCard
  have hindexNotCofinal : ¬ IsCofinal (Set.range index) := by
    intro hcof
    have hle : Order.cof W2 ≤ #(Set.range index) := Order.cof_le hcof
    have hcofW2 : Order.cof W2 = ℵ_ 2 := by
      calc
        Order.cof W2 = (ω_ 2 : Ordinal.{0}).cof := by
          exact Ordinal.cof_toType (ω_ 2 : Ordinal.{0})
        _ = ℵ_ 2 := by
          have hreg : (ℵ_ 2 : Cardinal.{0}).IsRegular := by
            rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num]
            exact Cardinal.isRegular_aleph_add_one 1
          simpa only [Cardinal.ord_aleph] using hreg.cof_ord
    rw [hcofW2] at hle
    exact (not_le_of_gt (Cardinal.aleph_lt_aleph.mpr (by norm_num)))
      (hle.trans hindexCard)
  obtain ⟨i, hi⟩ := not_isCofinal_iff.mp hindexNotCofinal
  let _ : NoMaxOrder W2 := by
    change NoMaxOrder ((ω_ 2 : Ordinal.{0}).ToType)
    rw [← Cardinal.ord_aleph]
    exact Cardinal.noMaxOrder (Cardinal.aleph0_le_aleph 2)
  obtain ⟨j, hij⟩ := exists_gt i
  refine ⟨seq i, ?_, ?_⟩
  · exact (hseq hij).trans_le (htopLUB.1 ⟨j, rfl⟩)
  · intro y hy
    let ys : seed := ⟨y, hy⟩
    exact (hindexAbove ys).trans (hseq (hi _ ⟨ys, rfl⟩))

/-- Under GCH, the small seeds can be uniformized on a stationary set,
so one small barrier core is stationary. -/
theorem exists_stationary_smallBarrierCore
    (hGCH : GCH) (blue : SimpleGraph W3)
    (hno : ¬ ∃ B : Set W3, blue.IsClique B ∧ typeLT B = ω_ 2 + 1) :
    ∃ seed : Set W3, #seed ≤ ℵ_ 1 ∧
      IsStationary (smallBarrierCore blue seed) := by
  classical
  let suprema : Set W3 := {top | IsOmegaTwoSup top}
  have hsuprema : IsStationary suprema :=
    isStationary_isOmegaTwoSup_omegaThree
  choose seed hseedCard hseedBarrier using fun x : suprema ↦
    exists_smallBarrierCore_at_of_no_clique_type_omegaTwo_add_one
      blue x.1 hno
  have hboundExists (x : suprema) :
      ∃ cutoff : W3, cutoff < x.1 ∧ ∀ y ∈ seed x, y < cutoff :=
    exists_strict_bound_of_small_of_IsOmegaTwoSup x.2 (hseedCard x)
      (hseedBarrier x).1
  choose cutoff hcutoff hseedBelow using hboundExists
  let cutoffAll (x : W3) : W3 :=
    if hx : x ∈ suprema then cutoff ⟨x, hx⟩ else x
  have hcutoffReg : ∀ x ∈ suprema, cutoffAll x < x := by
    intro x hx
    simpa only [cutoffAll, dif_pos hx] using hcutoff ⟨x, hx⟩
  have hpress : StationaryPressingDown W3 := by
    change StationaryPressingDown ((ω_ 3 : Ordinal.{0}).ToType)
    rw [← Cardinal.ord_aleph]
    have hreg : (ℵ_ 3 : Cardinal.{0}).IsRegular := by
      rw [show (3 : Ordinal.{0}) = 2 + 1 by norm_num]
      exact Cardinal.isRegular_aleph_add_one 2
    exact Set.stationaryPressingDown_ord (ℵ_ 3) hreg
      (Cardinal.aleph0_lt_aleph.mpr (by norm_num))
  obtain ⟨value, hvalue⟩ :=
    hpress suprema cutoffAll hsuprema hcutoffReg
  let fiber : Set W3 :=
    {x | x ∈ suprema ∧ cutoffAll x = value}
  have hfiber : IsStationary fiber := hvalue
  let seedAll (x : W3) : Set W3 :=
    if hx : x ∈ suprema then seed ⟨x, hx⟩ else ∅
  have hseedAllCard : ∀ x ∈ fiber, #(seedAll x) ≤ ℵ_ 1 := by
    intro x hx
    simpa only [seedAll, dif_pos hx.1] using hseedCard ⟨x, hx.1⟩
  have hseedAllSub : ∀ x ∈ fiber, seedAll x ⊆ Set.Iio value := by
    intro x hx y hy
    have hy' : y ∈ seed ⟨x, hx.1⟩ := by
      simpa only [seedAll, dif_pos hx.1] using hy
    have hyCutoff := hseedBelow ⟨x, hx.1⟩ y hy'
    change y < value
    rw [← hx.2]
    simpa only [cutoffAll, dif_pos hx.1] using hyCutoff
  let BoundedSeeds :=
    {t : Set W3 // t ⊆ Set.Iio value ∧ #t ≤ ℵ_ 1}
  let seedCode (x : W3) : BoundedSeeds :=
    if hx : x ∈ fiber then
      ⟨seedAll x, hseedAllSub x hx, hseedAllCard x hx⟩
    else ⟨∅, Set.empty_subset _, by simp⟩
  let piece (b : BoundedSeeds) : Set W3 :=
    {x | x ∈ fiber ∧ seedCode x = b}
  have hunion : (⋃ b : BoundedSeeds, piece b) = fiber := by
    ext x
    constructor
    · simp only [Set.mem_iUnion]
      rintro ⟨b, hx⟩
      exact hx.1
    · intro hx
      exact Set.mem_iUnion.2 ⟨seedCode x, hx, rfl⟩
  have hIioLt : #(Set.Iio value) < ℵ_ 3 := by
    simpa only [W3, Cardinal.mk_toType, Ordinal.card_omega] using
      Cardinal.mk_Iio_lt value (by simp [W3])
  have hsucc : Order.succ (ℵ_ 2 : Cardinal.{0}) = ℵ_ 3 := by
    calc
      Order.succ (ℵ_ 2 : Cardinal.{0}) = ℵ_ ((2 : Ordinal.{0}) + 1) :=
        Cardinal.succ_aleph 2
      _ = ℵ_ 3 := by norm_num
  have hIioLe : #(Set.Iio value) ≤ ℵ_ 2 := by
    rw [← hsucc] at hIioLt
    exact Order.lt_succ_iff.mp hIioLt
  have hBoundedSeeds : #BoundedSeeds ≤ ℵ_ 2 := by
    calc
      #BoundedSeeds ≤
          max #(Set.Iio value) ℵ₀ ^ (ℵ_ 1 : Cardinal.{0}) :=
        Cardinal.mk_bounded_subset_le (Set.Iio value) (ℵ_ 1)
      _ ≤ (ℵ_ 2 : Cardinal.{0}) ^ ℵ_ 1 :=
        Cardinal.power_le_power_right
          (max_le hIioLe (Cardinal.aleph0_le_aleph 2))
      _ = ℵ_ 2 := hGCH.aleph_two_power_aleph_one
  have hcofW3 : Order.cof W3 = ℵ_ 3 := by
    calc
      Order.cof W3 = (ω_ 3 : Ordinal.{0}).cof := by
        exact Ordinal.cof_toType (ω_ 3 : Ordinal.{0})
      _ = ℵ_ 3 := by
        have hreg : (ℵ_ 3 : Cardinal.{0}).IsRegular := by
          rw [show (3 : Ordinal.{0}) = 2 + 1 by norm_num]
          exact Cardinal.isRegular_aleph_add_one 2
        simpa only [Cardinal.ord_aleph] using hreg.cof_ord
  have hBoundedLtCof : #BoundedSeeds < Order.cof W3 := by
    rw [hcofW3]
    exact hBoundedSeeds.trans_lt
      (Cardinal.aleph_lt_aleph.mpr (by norm_num))
  have hcofNe : Order.cof W3 ≠ ℵ₀ := by
    rw [hcofW3]
    exact (Cardinal.aleph0_lt_aleph.mpr (by norm_num)).ne'
  have hstationaryUnion : IsStationary (⋃ b : BoundedSeeds, piece b) := by
    rw [hunion]
    exact hfiber
  obtain ⟨b, hb⟩ :=
    (isStationary_iUnion_iff hcofNe (by
      simpa only [Cardinal.lift_id] using hBoundedLtCof)).mp hstationaryUnion
  refine ⟨b.1, b.2.2, hb.mono fun x hx ↦ ?_⟩
  have hxFiber : x ∈ fiber := hx.1
  have hcode : seedAll x = b.1 := by
    have := congrArg Subtype.val hx.2
    simpa only [seedCode, dif_pos hxFiber] using this
  have hxBarrier : x ∈ smallBarrierCore blue (seedAll x) := by
    simpa only [seedAll, dif_pos hxFiber.1] using
      hseedBarrier ⟨x, hxFiber.1⟩
  simpa only [hcode] using hxBarrier

/-- The classical asymmetric Erdős--Rado relation under GCH:
`ω₃ → (ω₃, ω₂ + 1)²`. -/
theorem ordinalRamsey_omegaThree_omegaThree_omegaTwo_add_one
    (hGCH : GCH) :
    OrdinalRamsey (ω_ 3 : Ordinal.{0}) (ω_ 3) (ω_ 2 + 1) := by
  intro red blue hcompl
  by_cases hblue : ∃ B : Set W3,
      blue.IsClique B ∧ typeLT B = ω_ 2 + 1
  · exact Or.inr hblue
  · obtain ⟨seed, -, hstationary⟩ :=
      exists_stationary_smallBarrierCore hGCH blue hblue
    have hred : red.IsClique (smallBarrierCore blue seed) := by
      have hcomp := compl_isClique_smallBarrierCore blue seed
      rwa [hcompl.symm.compl_eq] at hcomp
    let _ : IsRegularCardinalOrder W3 := ⟨by
      rw [Ordinal.type_toType, Ordinal.cof_toType]
      have hreg : (ℵ_ 3 : Cardinal.{0}).IsRegular := by
        rw [show (3 : Ordinal.{0}) = 2 + 1 by norm_num]
        exact Cardinal.isRegular_aleph_add_one 2
      have hcof : (ω_ 3 : Ordinal.{0}).cof = ℵ_ 3 := by
        simpa only [Cardinal.ord_aleph] using hreg.cof_ord
      rw [hcof, Cardinal.ord_aleph]⟩
    have htype : typeLT (smallBarrierCore blue seed) = ω_ 3 := by
      simpa only [W3, Ordinal.type_toType] using
        Order.type_eq_of_isCofinal hstationary.isCofinal
    exact Or.inl ⟨smallBarrierCore blue seed, hred, htype⟩

end ErdosRadoGCHAsym
