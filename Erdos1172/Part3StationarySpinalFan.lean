/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3TransfiniteSpinalFan

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3StationarySpinalFan

open Erdos1172Part3Failure Erdos1172Part3FiniteStars
  Erdos1172Part3TransfiniteTransversal

/-- Every strict final segment of the initial ordinal `ω₂` is stationary.
This small wrapper supplies the exact stationary domain used by the spinal
pressing-down argument. -/
private theorem isStationary_Ioi_omegaTwo (anchor : W2) :
    IsStationary (Set.Ioi anchor) := by
  have htailCard : #(Set.Ioi anchor) = ℵ_ 2 :=
    mk_Ioi_omegaTwo_eq anchor
  have htailNonempty : (Set.Ioi anchor).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    rw [hempty] at htailCard
    have hzero : (0 : Cardinal) = ℵ_ 2 := by simpa using htailCard
    exact (Cardinal.aleph_pos 2).ne' hzero.symm
  obtain ⟨upper, hupper⟩ := htailNonempty
  apply IsStationary.of_not_isCofinal_compl
  rw [not_isCofinal_iff]
  refine ⟨upper, ?_⟩
  intro y hy
  rw [compl_Ioi] at hy
  exact hy.trans_lt hupper

/-- Pressing down upgrades the cardinal spinal failure fiber to a stationary
one.  Each point of the blue base is first coded by its unique spine index.
For a later spine index `b`, the chosen red failure witness has code below
the base maximum's index and hence below `b`.  Fodor's lemma makes this
regressive witness code constant on a stationary set. -/
theorem exists_stationary_red_failure_fiber_on_strict_spine
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (spine : W2 → W2) (hspine : StrictMono spine)
    {base : Set W2} (hbaseSub : base ⊆ Set.range spine)
    (hbase : blue.IsClique base) (hbaseType : typeLT base = ω_ 1 + 1)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) :
    ∃ (anchor centerIndex : W2) (fiber : Set W2),
      spine anchor ∈ base ∧
      (∀ y ∈ base, y ≤ spine anchor) ∧
      spine centerIndex ∈ base ∧
      IsStationary fiber ∧ #fiber = ℵ_ 2 ∧
      typeLT fiber = ω_ 2 ∧
      fiber ⊆ Set.Ioi anchor ∧
      ∀ b ∈ fiber,
        centerIndex < b ∧ red.Adj (spine centerIndex) (spine b) := by
  classical
  obtain ⟨maximum, hmaximum⟩ :=
    exists_max_of_type_omegaOne_add_one hbaseType
  obtain ⟨anchor, hanchor⟩ := hbaseSub maximum.property
  have hanchorMem : spine anchor ∈ base := hanchor.symm ▸ maximum.property
  have hanchorMax (y : W2) (hy : y ∈ base) : y ≤ spine anchor := by
    have hle : (⟨y, hy⟩ : base) ≤ maximum :=
      le_of_not_gt ((isMax_iff_forall_not_lt.mp hmaximum) ⟨y, hy⟩)
    change y ≤ (maximum : W2) at hle
    exact hle.trans_eq hanchor.symm
  have hlater (b : Set.Ioi anchor) :
      ∀ y ∈ base, y < spine b := by
    intro y hy
    exact (hanchorMax y hy).trans_lt (hspine b.property)
  have hwitness (b : Set.Ioi anchor) :
      ∃ y : base, red.Adj y (spine b) := by
    by_contra hnone
    have hblueAdj : ∀ y ∈ base, blue.Adj y (spine b) := by
      intro y hy
      rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
      refine ⟨(hlater b y hy).ne, ?_⟩
      intro hred
      exact hnone ⟨⟨y, hy⟩, hred⟩
    obtain ⟨t, ht, httype⟩ :=
      blue.exists_clique_type_add_one_of_common_later
        hbase hbaseType (hlater b) hblueAdj
    apply hnoBlue
    refine ⟨t, ht, ?_⟩
    calc
      typeLT t = (ω_ 1 + 1) + 1 := httype
      _ = ω_ 1 + 2 := by norm_num [add_assoc]
  let failure (b : Set.Ioi anchor) : base :=
    Classical.choose (hwitness b)
  have hfailure (b : Set.Ioi anchor) :
      red.Adj (failure b) (spine b) :=
    Classical.choose_spec (hwitness b)
  have hfailureIndexExists (b : Set.Ioi anchor) :
      ∃ a : W2, spine a = failure b :=
    hbaseSub (failure b).property
  let failureIndex (b : Set.Ioi anchor) : W2 :=
    Classical.choose (hfailureIndexExists b)
  have hfailureIndexSpine (b : Set.Ioi anchor) :
      spine (failureIndex b) = failure b :=
    Classical.choose_spec (hfailureIndexExists b)
  have hfailureIndexRegressive (b : Set.Ioi anchor) :
      failureIndex b < b := by
    have hspineLe : spine (failureIndex b) ≤ spine anchor := by
      rw [hfailureIndexSpine]
      exact hanchorMax (failure b) (failure b).property
    exact (hspine.le_iff_le.mp hspineLe).trans_lt b.property
  let failureIndexAll (b : W2) : W2 :=
    if hb : b ∈ Set.Ioi anchor then failureIndex ⟨b, hb⟩ else b
  have hfailureIndexAllRegressive :
      ∀ b ∈ Set.Ioi anchor, failureIndexAll b < b := by
    intro b hb
    simpa only [failureIndexAll, dif_pos hb] using
      hfailureIndexRegressive ⟨b, hb⟩
  have hreg : (ℵ_ 2 : Cardinal.{0}).IsRegular := by
    rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num]
    exact Cardinal.isRegular_aleph_add_one 1
  have hpress : StationaryPressingDown W2 := by
    change StationaryPressingDown ((ω_ 2 : Ordinal.{0}).ToType)
    rw [← Cardinal.ord_aleph]
    exact Set.stationaryPressingDown_ord (ℵ_ 2) hreg
      (Cardinal.aleph0_lt_aleph.mpr (by norm_num))
  obtain ⟨centerIndex, hstationaryFiber⟩ :=
    hpress (Set.Ioi anchor) failureIndexAll
      (isStationary_Ioi_omegaTwo anchor) hfailureIndexAllRegressive
  let fiber : Set W2 :=
    {b | b ∈ Set.Ioi anchor ∧ failureIndexAll b = centerIndex}
  have hfiberStationary : IsStationary fiber := hstationaryFiber
  have hfiberCard : #fiber = ℵ_ 2 := by
    apply le_antisymm
    · calc
        #fiber ≤ #W2 := Cardinal.mk_set_le fiber
        _ = ℵ_ 2 := by
          simp only [W2, Cardinal.mk_toType, Ordinal.card_omega]
    · have hcofW2 : Order.cof W2 = ℵ_ 2 := by
        calc
          Order.cof W2 = (ω_ 2 : Ordinal.{0}).cof :=
            Ordinal.cof_toType (ω_ 2 : Ordinal.{0})
          _ = ℵ_ 2 := by
            simpa only [Cardinal.ord_aleph] using hreg.cof_ord
      rw [← hcofW2]
      exact Order.cof_le hfiberStationary.isCofinal
  have hfiberType : typeLT fiber = ω_ 2 :=
    typeLT_eq_omegaTwo_of_mk_eq hfiberCard
  have hcenterMem : spine centerIndex ∈ base := by
    obtain ⟨b, hb⟩ := hfiberStationary.nonempty
    have hindexEq : failureIndex ⟨b, hb.1⟩ = centerIndex := by
      simpa only [failureIndexAll, dif_pos hb.1] using hb.2
    rw [← hindexEq, hfailureIndexSpine]
    exact (failure ⟨b, hb.1⟩).property
  refine ⟨anchor, centerIndex, fiber, hanchorMem, hanchorMax,
    hcenterMem, hfiberStationary, hfiberCard, hfiberType, ?_, ?_⟩
  · exact fun _ hb ↦ hb.1
  · intro b hb
    have hindexEq : failureIndex ⟨b, hb.1⟩ = centerIndex := by
      simpa only [failureIndexAll, dif_pos hb.1] using hb.2
    refine ⟨hindexEq ▸ hfailureIndexRegressive ⟨b, hb.1⟩, ?_⟩
    simpa only [← hindexEq, hfailureIndexSpine] using
      hfailure ⟨b, hb.1⟩

/-- Stationary strengthening of the spinal-fan obstruction.  One fixed
earlier spine point is red-adjacent to every spine point indexed by a
stationary subset of `ω₂`; a blue `ω₁ + 1` fan is retained inside that
stationary image. -/
def StationarySpinalFan (red blue : SimpleGraph W2) : Prop :=
  ∃ (spine : W2 → W2) (base : Set W2) (anchor centerIndex : W2)
      (fiber fan : Set W2),
    StrictMono spine ∧ typeLT (Set.range spine) = ω_ 2 ∧
    base ⊆ Set.range spine ∧ blue.IsClique base ∧
    typeLT base = ω_ 1 + 1 ∧ spine anchor ∈ base ∧
    (∀ y ∈ base, y ≤ spine anchor) ∧ spine centerIndex ∈ base ∧
    IsStationary fiber ∧ #fiber = ℵ_ 2 ∧
    typeLT fiber = ω_ 2 ∧
    fiber ⊆ Set.Ioi anchor ∧
    (∀ b ∈ fiber,
      centerIndex < b ∧ red.Adj (spine centerIndex) (spine b)) ∧
    fan ⊆ spine '' fiber ∧ blue.IsClique fan ∧
    typeLT fan = ω_ 1 + 1 ∧
    ∀ x ∈ fan, spine anchor < x ∧ red.Adj (spine centerIndex) x

/-- A full transversal split yields the exact red target, or a stationary
spinal fan. -/
theorem fullOmegaTwoTransversalSplit_redTarget_or_stationarySpinalFan
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (hsplit : FullOmegaTwoTransversalSplit red blue) :
    OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      StationarySpinalFan red blue := by
  classical
  obtain ⟨indexedArms, representatives, transversal,
    hrepresentativesStrict, hrepresentativesType, harms,
    hrepresentativeMem, hrepresentativeMax, htransversalSub,
    htransversalBlue, htransversalType, hcrossSplit⟩ := hsplit
  obtain ⟨anchor, centerIndex, fiber, hanchorMem, hanchorMax,
      hcenterMem, hfiberStationary, hfiberCard, hfiberType, hfiberTail,
      hredFiber⟩ :=
    exists_stationary_red_failure_fiber_on_strict_spine
      red blue hcompl representatives hrepresentativesStrict
      htransversalSub htransversalBlue htransversalType hnoBlue
  have himageCard : #(representatives '' fiber) = ℵ_ 2 := by
    calc
      #(representatives '' fiber) = #fiber :=
        Cardinal.mk_image_eq hrepresentativesStrict.injective
      _ = ℵ_ 2 := hfiberCard
  by_cases hred : OrdinalRamsey.HasCliqueOfType red RedTarget
  · exact Or.inl hred
  · right
    obtain ⟨fan, hfanSub, hfanBlue, hfanType⟩ :=
      Erdos1172Part3CHAsymmetric.exists_blue_omegaOne_add_one_in_every_alephTwo_set
        hCH red blue hcompl hred himageCard
    refine ⟨representatives, transversal, anchor, centerIndex, fiber, fan,
      hrepresentativesStrict, hrepresentativesType, htransversalSub,
      htransversalBlue, htransversalType, hanchorMem, hanchorMax,
      hcenterMem, hfiberStationary, hfiberCard, hfiberType, hfiberTail,
      hredFiber, hfanSub, hfanBlue, hfanType, ?_⟩
    intro x hx
    obtain ⟨b, hb, rfl⟩ := hfanSub hx
    exact ⟨hrepresentativesStrict (hfiberTail hb), (hredFiber b hb).2⟩

/-- Global exact-target-or-stationary-spinal-fan normal form under CH. -/
theorem part3_exact_or_stationarySpinalFan
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      StationarySpinalFan red blue := by
  by_cases htarget :
      OrdinalRamsey.HasCliqueOfType red RedTarget ∨
        OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)
  · exact Or.inl htarget
  · right
    have hnone := not_or.mp htarget
    obtain hexact | hsplit :=
      part3_exact_or_fullOmegaTwoTransversalSplit hCH red blue hcompl
    · exact (htarget hexact).elim
    · obtain hred | hfan :=
        fullOmegaTwoTransversalSplit_redTarget_or_stationarySpinalFan
          hCH red blue hcompl hnone.2 hsplit
      · exact (hnone.1 hred).elim
      · exact hfan

end Erdos1172Part3StationarySpinalFan
