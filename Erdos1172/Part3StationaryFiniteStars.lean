/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3StationaryCombinedFan

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3StationaryFiniteStars

open Erdos1172Part3Failure Erdos1172Part3FiniteStars
  Erdos1172Part3StationaryCountablePredecessors
  Erdos1172Part3StationaryCombinedFan

/-- A stationary subset of the initial ordinal `ω₂` has cardinality
`ℵ₂`. -/
theorem mk_eq_alephTwo_of_isStationary {s : Set W2}
    (hs : IsStationary s) : #s = ℵ_ 2 := by
  have hreg : (ℵ_ 2 : Cardinal.{0}).IsRegular := by
    rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num]
    exact Cardinal.isRegular_aleph_add_one 1
  apply le_antisymm
  · calc
      #s ≤ #W2 := Cardinal.mk_set_le s
      _ = ℵ_ 2 := by
        simp only [W2, Cardinal.mk_toType, Ordinal.card_omega]
  · have hcofW2 : Order.cof W2 = ℵ_ 2 := by
      calc
        Order.cof W2 = (ω_ 2 : Ordinal.{0}).cof :=
          Ordinal.cof_toType (ω_ 2 : Ordinal.{0})
        _ = ℵ_ 2 := by
          simpa only [Cardinal.ord_aleph] using hreg.cof_ord
    rw [← hcofW2]
    exact Order.cof_le hs.isCofinal

/-- One stationary finite-star extension step.  The points of the current
stationary spine fiber having no fresh red neighbour in the blue base form
a nonstationary set: their spine images inject into the small
`unwitnessed` set.  On the stationary remainder, the index of a chosen
fresh red neighbour is regressive.  Pressing down freezes that neighbour
while preserving stationarity. -/
theorem exists_fresh_base_center_stationary_spine_fiber
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (spine : W2 → W2) (hspine : StrictMono spine)
    {base : Set W2} (hbaseSub : base ⊆ Set.range spine)
    {anchor : W2} (hanchorMem : spine anchor ∈ base)
    (hanchorMax : ∀ y ∈ base, y ≤ spine anchor)
    (hbaseBlue : blue.IsClique base)
    (hbaseType : typeLT base = ω_ 1 + 1)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (centers : Finset W2) (_hcentersBase : (centers : Set W2) ⊆ base)
    {fiber : Set W2} (hfiberStationary : IsStationary fiber)
    (hfiberTail : fiber ⊆ Set.Ioi anchor)
    (hstar : ∀ y ∈ centers, ∀ b ∈ fiber,
      red.Adj y (spine b)) :
    ∃ (newCenter : W2) (newFiber : Set W2),
      newCenter ∈ base ∧ newCenter ∉ centers ∧
      IsStationary newFiber ∧ newFiber ⊆ fiber ∧
      ∀ y ∈ insert newCenter centers, ∀ b ∈ newFiber,
        red.Adj y (spine b) := by
  classical
  let reservoir : Set W2 := spine '' fiber
  have hreservoirTail : reservoir ⊆ Set.Ioi (spine anchor) := by
    rintro _ ⟨b, hb, rfl⟩
    exact hspine (hfiberTail hb)
  have hanchorIsMax : IsMax (⟨spine anchor, hanchorMem⟩ : base) := by
    rw [isMax_iff_forall_not_lt]
    intro y hy
    exact (not_lt_of_ge (hanchorMax y y.property)) hy
  let unwitnessed : Set W2 :=
    {x | x ∈ reservoir ∧
      ∀ y ∈ base \ (centers : Set W2), blue.Adj y x}
  have hunwitnessedSmall : #unwitnessed < ℵ_ 2 := by
    simpa only [unwitnessed] using
      mk_unwitnessed_lt_alephTwo red blue hcompl hanchorMem
        hanchorIsMax hbaseBlue hbaseType hreservoirTail hnoRed hnoBlue
        centers
  let bad : Set W2 :=
    {b | b ∈ fiber ∧
      ∀ y ∈ base \ (centers : Set W2), blue.Adj y (spine b)}
  let badEmbedding : bad ↪ unwitnessed :=
    { toFun := fun b ↦ ⟨spine b, by
        have hb : (b : W2) ∈ fiber ∧
            ∀ y ∈ base \ (centers : Set W2), blue.Adj y (spine b) :=
          b.property
        exact ⟨⟨b, hb.1, rfl⟩, hb.2⟩⟩
      inj' := by
        intro a b hab
        apply Subtype.ext
        exact hspine.injective (congrArg Subtype.val hab) }
  have hbadSmall : #bad < ℵ_ 2 :=
    badEmbedding.cardinal_le.trans_lt hunwitnessedSmall
  have hbadNonstationary : ¬ IsStationary bad := by
    intro hbadStationary
    exact hbadSmall.ne (mk_eq_alephTwo_of_isStationary hbadStationary)
  let good : Set W2 := fiber \ bad
  have hbadUnionGood : bad ∪ good = fiber := by
    ext b
    simp only [bad, good, mem_union, mem_ofPred_eq, mem_sdiff]
    tauto
  have hcof : Order.cof W2 ≠ ℵ₀ := by
    have hreg : (ℵ_ 2 : Cardinal.{0}).IsRegular := by
      rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num]
      exact Cardinal.isRegular_aleph_add_one 1
    have hcofEq : Order.cof W2 = ℵ_ 2 := by
      calc
        Order.cof W2 = (ω_ 2 : Ordinal.{0}).cof :=
          Ordinal.cof_toType (ω_ 2 : Ordinal.{0})
        _ = ℵ_ 2 := by
          simpa only [Cardinal.ord_aleph] using hreg.cof_ord
    rw [hcofEq]
    exact (Cardinal.aleph0_lt_aleph.mpr (by norm_num)).ne'
  have hgoodStationary : IsStationary good := by
    have hunionStationary : IsStationary (bad ∪ good) := by
      simpa only [hbadUnionGood] using hfiberStationary
    rcases (isStationary_union_iff hcof).mp hunionStationary with
      hbad | hgood
    · exact (hbadNonstationary hbad).elim
    · exact hgood
  have hwitness (b : good) :
      ∃ y : (base \ (centers : Set W2) : Set W2),
        red.Adj y (spine b) := by
    have hb : (b : W2) ∈ fiber ∧ (b : W2) ∉ bad := b.property
    have hnotall :
        ¬ ∀ y ∈ base \ (centers : Set W2), blue.Adj y (spine b) := by
      intro hall
      apply hb.2
      exact ⟨hb.1, hall⟩
    push Not at hnotall
    obtain ⟨y, hy, hnotBlue⟩ := hnotall
    refine ⟨⟨y, hy⟩, ?_⟩
    rw [← hcompl.symm.compl_eq, SimpleGraph.compl_adj]
    refine ⟨?_, hnotBlue⟩
    exact ((hanchorMax y hy.1).trans_lt
      (hspine (hfiberTail hb.1))).ne
  let failure : good → (base \ (centers : Set W2) : Set W2) :=
    fun b ↦ Classical.choose (hwitness b)
  have hfailure (b : good) : red.Adj (failure b) (spine b) :=
    Classical.choose_spec (hwitness b)
  have hfailureIndexExists (b : good) :
      ∃ a : W2, spine a = failure b :=
    hbaseSub (failure b).property.1
  let failureIndex (b : good) : W2 :=
    Classical.choose (hfailureIndexExists b)
  have hfailureIndexSpine (b : good) :
      spine (failureIndex b) = failure b :=
    Classical.choose_spec (hfailureIndexExists b)
  have hfailureIndexRegressive (b : good) : failureIndex b < b := by
    have hbFiber : (b : W2) ∈ fiber := b.property.1
    have hspineLe : spine (failureIndex b) ≤ spine anchor := by
      rw [hfailureIndexSpine]
      exact hanchorMax (failure b) (failure b).property.1
    exact (hspine.le_iff_le.mp hspineLe).trans_lt (hfiberTail hbFiber)
  let failureIndexAll (b : W2) : W2 :=
    if hb : b ∈ good then failureIndex ⟨b, hb⟩ else b
  have hfailureIndexAllRegressive :
      ∀ b ∈ good, failureIndexAll b < b := by
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
  obtain ⟨value, hstationaryValueFiber⟩ :=
    hpress good failureIndexAll hgoodStationary
      hfailureIndexAllRegressive
  let newFiber : Set W2 :=
    {b | b ∈ good ∧ failureIndexAll b = value}
  have hnewFiberStationary : IsStationary newFiber :=
    hstationaryValueFiber
  obtain ⟨sample, hsample⟩ := hnewFiberStationary.nonempty
  let newCenter : W2 := spine value
  have hsampleIndex : failureIndex ⟨sample, hsample.1⟩ = value := by
    simpa only [failureIndexAll, dif_pos hsample.1] using hsample.2
  have hnewCenterMem : newCenter ∈ base := by
    change spine value ∈ base
    rw [← hsampleIndex, hfailureIndexSpine]
    exact (failure ⟨sample, hsample.1⟩).property.1
  have hnewCenterFresh : newCenter ∉ centers := by
    change spine value ∉ centers
    rw [← hsampleIndex, hfailureIndexSpine]
    exact (failure ⟨sample, hsample.1⟩).property.2
  have hnewFiberSub : newFiber ⊆ fiber := by
    intro b hb
    exact hb.1.1
  refine ⟨newCenter, newFiber, hnewCenterMem, hnewCenterFresh,
    hnewFiberStationary, hnewFiberSub, ?_⟩
  intro y hy b hb
  rw [Finset.mem_insert] at hy
  rcases hy with rfl | hy
  · have hindex : failureIndex ⟨b, hb.1⟩ = value := by
      simpa only [failureIndexAll, dif_pos hb.1] using hb.2
    have hcenterEq : (failure ⟨b, hb.1⟩ : W2) = newCenter := by
      change (failure ⟨b, hb.1⟩ : W2) = spine value
      exact (hfailureIndexSpine ⟨b, hb.1⟩).symm.trans
        (congrArg spine hindex)
    rw [← hcenterEq]
    exact hfailure ⟨b, hb.1⟩
  · exact hstar y hy b (hnewFiberSub hb)

/-- Iterating the stationary extension step gives blue base stars of every
finite size, while retaining a stationary subset of the original spine
fiber as their common red neighbourhood. -/
theorem exists_arbitrarily_large_finite_stationary_spine_stars
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (spine : W2 → W2) (hspine : StrictMono spine)
    {base : Set W2} (hbaseSub : base ⊆ Set.range spine)
    {anchor : W2} (hanchorMem : spine anchor ∈ base)
    (hanchorMax : ∀ y ∈ base, y ≤ spine anchor)
    (hbaseBlue : blue.IsClique base)
    (hbaseType : typeLT base = ω_ 1 + 1)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    {initialFiber : Set W2}
    (hinitialStationary : IsStationary initialFiber)
    (hinitialTail : initialFiber ⊆ Set.Ioi anchor) :
    ∀ n : ℕ, ∃ (centers : Finset W2) (fiber : Set W2),
      centers.card = n ∧ (centers : Set W2) ⊆ base ∧
      blue.IsClique (centers : Set W2) ∧ IsStationary fiber ∧
      fiber ⊆ initialFiber ∧
      ∀ y ∈ centers, ∀ b ∈ fiber, red.Adj y (spine b) := by
  classical
  intro n
  induction n with
  | zero =>
      refine ⟨∅, initialFiber, by simp, by simp, ?_,
        hinitialStationary, Subset.rfl, ?_⟩
      · exact hbaseBlue.subset (by simp)
      · simp
  | succ n ih =>
      obtain ⟨centers, fiber, hcard, hcentersBase, hcentersBlue,
        hfiberStationary, hfiberSub, hstar⟩ := ih
      obtain ⟨newCenter, newFiber, hnewCenterBase, hnewCenterFresh,
          hnewFiberStationary, hnewFiberSub, hnewStar⟩ :=
        exists_fresh_base_center_stationary_spine_fiber
          red blue hcompl spine hspine hbaseSub hanchorMem hanchorMax
          hbaseBlue hbaseType hnoRed hnoBlue centers hcentersBase
          hfiberStationary (hfiberSub.trans hinitialTail) hstar
      refine ⟨insert newCenter centers, newFiber, ?_, ?_, ?_,
        hnewFiberStationary, hnewFiberSub.trans hfiberSub, hnewStar⟩
      · rw [Finset.card_insert_of_notMem hnewCenterFresh, hcard]
      · intro x hx
        rw [Finset.mem_coe, Finset.mem_insert] at hx
        exact hx.elim (fun h ↦ h ▸ hnewCenterBase) (hcentersBase ·)
      · apply hbaseBlue.subset
        intro x hx
        rw [Finset.mem_coe, Finset.mem_insert] at hx
        exact hx.elim (fun h ↦ h ▸ hnewCenterBase) (hcentersBase ·)

/-- Arbitrarily large finite blue subsets of one blue `ω₁ + 1` spine
base have a common red neighbourhood indexed by a stationary subset of
`ω₂`.  Each stationary image contains a blue `ω₁ + 1` fan under CH, and
the countable homogeneous predecessor tuple from the combined fan remains
red-joined to the same refined fiber. -/
def StationaryFiniteBaseStarsWithCountablePredecessors
    (red blue : SimpleGraph W2) : Prop :=
  ∃ (spine : W2 → W2) (base : Set W2) (anchor : W2)
      (centerArms : ℕ → Set W2) (countableCenters : ℕ → W2),
    StrictMono spine ∧ typeLT (Set.range spine) = ω_ 2 ∧
    base ⊆ Set.range spine ∧ blue.IsClique base ∧
    typeLT base = ω_ 1 + 1 ∧ spine anchor ∈ base ∧
    (∀ y ∈ base, y ≤ spine anchor) ∧
    (∀ n, blue.IsClique (centerArms n) ∧
      typeLT (centerArms n) = ω_ 1 + 1) ∧
    (∀ n, countableCenters n ∈ centerArms n) ∧
    (∀ i j, i < j → ∀ x ∈ centerArms i,
      ∀ y ∈ centerArms j, x < y) ∧
    StrictMono countableCenters ∧
    typeLT (Set.range countableCenters) = ω ∧
    (red.IsClique (Set.range countableCenters) ∨
      blue.IsClique (Set.range countableCenters)) ∧
    ∀ n : ℕ, ∃ (finiteCenters : Finset W2)
        (indexFiber representativeFiber fan : Set W2),
      finiteCenters.card = n ∧ (finiteCenters : Set W2) ⊆ base ∧
      blue.IsClique (finiteCenters : Set W2) ∧
      IsStationary indexFiber ∧ #indexFiber = ℵ_ 2 ∧
      typeLT indexFiber = ω_ 2 ∧
      indexFiber ⊆ Set.Ioi anchor ∩ Set.Ioi omegaOneCutoff ∧
      representativeFiber = spine '' indexFiber ∧
      #representativeFiber = ℵ_ 2 ∧
      typeLT representativeFiber = ω_ 2 ∧
      fan ⊆ representativeFiber ∧ blue.IsClique fan ∧
      typeLT fan = ω_ 1 + 1 ∧
      (∀ y ∈ finiteCenters, ∀ b ∈ indexFiber,
        y < spine b ∧ red.Adj y (spine b)) ∧
      ∀ k, ∀ b ∈ indexFiber,
        countableCenters k < spine b ∧
          red.Adj (countableCenters k) (spine b)

/-- The combined stationary fan can be refined to stationary common
fibers for every finite blue base star.  Refinement preserves the complete
countable predecessor tuple, and CH supplies a fresh blue `ω₁ + 1` fan in
each refined spine image. -/
theorem StationaryCombinedSpinalFan.to_finiteBaseStarsWithCountablePredecessors
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (hcombined : StationaryCombinedSpinalFan red blue) :
    StationaryFiniteBaseStarsWithCountablePredecessors red blue := by
  classical
  obtain ⟨spine, base, anchor, _baseCenter, centerArms,
      countableCenters, initialFiber, _representativeFiber, _initialFan,
      hspine, hspineType, hbaseSub, hbaseBlue, hbaseType,
      hanchorMem, hanchorMax, _hbaseCenterMem, hcenterArms,
      hcountableCentersMem, hcenterArmsOrdered, hcountableCentersStrict,
      hcountableCentersType, hcountableCentersHomogeneous,
      hinitialStationary, _hinitialCard, _hinitialType, hinitialTail,
      _hrepresentativeEq, _hrepresentativeCard, _hrepresentativeType,
      _hinitialFanSub, _hinitialFanBlue, _hinitialFanType,
      _hbaseCenterCross, hcountableCentersCross⟩ := hcombined
  refine ⟨spine, base, anchor, centerArms, countableCenters,
    hspine, hspineType, hbaseSub, hbaseBlue, hbaseType,
    hanchorMem, hanchorMax, hcenterArms, hcountableCentersMem,
    hcenterArmsOrdered, hcountableCentersStrict, hcountableCentersType,
    hcountableCentersHomogeneous, fun n ↦ ?_⟩
  obtain ⟨finiteCenters, indexFiber, hfiniteCard, hfiniteBase,
      hfiniteBlue, hindexStationary, hindexSub, hfiniteCross⟩ :=
    exists_arbitrarily_large_finite_stationary_spine_stars
      red blue hcompl spine hspine hbaseSub hanchorMem hanchorMax
      hbaseBlue hbaseType hnoRed hnoBlue hinitialStationary
      (fun _ hb ↦ (hinitialTail hb).1) n
  have hindexCard : #indexFiber = ℵ_ 2 :=
    mk_eq_alephTwo_of_isStationary hindexStationary
  have hindexType : typeLT indexFiber = ω_ 2 :=
    typeLT_eq_omegaTwo_of_mk_eq hindexCard
  have hindexTail :
      indexFiber ⊆ Set.Ioi anchor ∩ Set.Ioi omegaOneCutoff :=
    hindexSub.trans hinitialTail
  let representativeFiber : Set W2 := spine '' indexFiber
  have hrepresentativeCard : #representativeFiber = ℵ_ 2 := by
    calc
      #representativeFiber = #indexFiber :=
        Cardinal.mk_image_eq hspine.injective
      _ = ℵ_ 2 := hindexCard
  have hrepresentativeType : typeLT representativeFiber = ω_ 2 :=
    typeLT_eq_omegaTwo_of_mk_eq hrepresentativeCard
  obtain ⟨fan, hfanSub, hfanRed, hfanType⟩ |
      ⟨fan, hfanSub, hfanBlue, hfanType⟩ :=
    OrdinalRamsey.on_set_of_type
      (Erdos1172Part3CHAsymmetric.red_target_or_blue_omegaOne_add_one hCH)
      red blue hcompl representativeFiber hrepresentativeType
  · exact (hnoRed ⟨fan, hfanRed, hfanType⟩).elim
  · refine ⟨finiteCenters, indexFiber, representativeFiber, fan,
      hfiniteCard, hfiniteBase, hfiniteBlue, hindexStationary,
      hindexCard, hindexType, hindexTail, rfl, hrepresentativeCard,
      hrepresentativeType, hfanSub, hfanBlue, hfanType, ?_, ?_⟩
    · intro y hy b hb
      have hyBase : y ∈ base := hfiniteBase (by simpa using hy)
      exact ⟨(hanchorMax y hyBase).trans_lt (hspine (hindexTail hb).1),
        hfiniteCross y hy b hb⟩
    · intro k b hb
      exact hcountableCentersCross k b (hindexSub hb)

/-- Global exact-target-or-stationary-finite-stars normal form under CH. -/
theorem part3_exact_or_stationaryFiniteBaseStarsWithCountablePredecessors
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      StationaryFiniteBaseStarsWithCountablePredecessors red blue := by
  by_cases htarget :
      OrdinalRamsey.HasCliqueOfType red RedTarget ∨
        OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)
  · exact Or.inl htarget
  · right
    have hnone := not_or.mp htarget
    obtain hexact | hcombined :=
      part3_exact_or_stationaryCombinedSpinalFan hCH red blue hcompl
    · exact (htarget hexact).elim
    · exact
        StationaryCombinedSpinalFan.to_finiteBaseStarsWithCountablePredecessors
          hCH red blue hcompl hnone.1 hnone.2 hcombined

end Erdos1172Part3StationaryFiniteStars
