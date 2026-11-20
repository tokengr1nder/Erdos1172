/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3StationaryCountablePredecessors

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3StationaryCombinedFan

open Erdos1172Part3Failure Erdos1172Part3FiniteStars
  Erdos1172Part3TransfiniteIncidence
  Erdos1172Part3HomogeneousFailureLadder
  Erdos1172Part3StationaryCountablePredecessors

/-- Restricting a stationary subset of `ω₂` above one more point preserves
stationarity. -/
theorem IsStationary.inter_Ioi_omegaTwo {s : Set W2}
    (hs : IsStationary s) (anchor : W2) :
    IsStationary {b | b ∈ s ∧ anchor < b} := by
  have htailCard : #(Set.Ioi anchor) = ℵ_ 2 :=
    mk_Ioi_omegaTwo_eq anchor
  have htailNonempty : (Set.Ioi anchor).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    rw [hempty] at htailCard
    have hzero : (0 : Cardinal) = ℵ_ 2 := by simpa using htailCard
    exact (Cardinal.aleph_pos 2).ne' hzero.symm
  obtain ⟨upper, hupper⟩ := htailNonempty
  have htailClosed : DirSupClosed (Set.Ici upper) := by
    intro d hd hne _ top htop
    obtain ⟨x, hx⟩ := hne
    exact (hd hx).trans (htop.1 hx)
  have htailClub : IsClub (Set.Ici upper) :=
    ⟨htailClosed,
      fun x ↦ ⟨max upper x, Set.mem_Ici.mpr (le_max_left _ _), le_max_right _ _⟩⟩
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
  intro C hC
  obtain ⟨b, hb, hbC⟩ := hs (hC.inter hcof htailClub)
  exact ⟨b, ⟨hb, hupper.trans_le hbC.2⟩, hbC.1⟩

/-- One shared stationary fiber simultaneously freezes a red witness from
the blue `ω₁ + 1` spine base and countably many red predecessors from
strictly ordered blue `ω₁ + 1` arms. -/
def StationaryCombinedSpinalFan
    (red blue : SimpleGraph W2) : Prop :=
  ∃ (spine : W2 → W2) (base : Set W2) (anchor baseCenter : W2)
      (centerArms : ℕ → Set W2) (centers : ℕ → W2)
      (indexFiber representativeFiber fan : Set W2),
    StrictMono spine ∧ typeLT (Set.range spine) = ω_ 2 ∧
    base ⊆ Set.range spine ∧ blue.IsClique base ∧
    typeLT base = ω_ 1 + 1 ∧ spine anchor ∈ base ∧
    (∀ y ∈ base, y ≤ spine anchor) ∧ baseCenter ∈ base ∧
    (∀ n, blue.IsClique (centerArms n) ∧
      typeLT (centerArms n) = ω_ 1 + 1) ∧
    (∀ n, centers n ∈ centerArms n) ∧
    (∀ i j, i < j → ∀ x ∈ centerArms i,
      ∀ y ∈ centerArms j, x < y) ∧
    StrictMono centers ∧ typeLT (Set.range centers) = ω ∧
    (red.IsClique (Set.range centers) ∨
      blue.IsClique (Set.range centers)) ∧
    IsStationary indexFiber ∧ #indexFiber = ℵ_ 2 ∧
    typeLT indexFiber = ω_ 2 ∧
    indexFiber ⊆ Set.Ioi anchor ∩ Set.Ioi omegaOneCutoff ∧
    representativeFiber = spine '' indexFiber ∧
    #representativeFiber = ℵ_ 2 ∧
    typeLT representativeFiber = ω_ 2 ∧
    fan ⊆ representativeFiber ∧ blue.IsClique fan ∧
    typeLT fan = ω_ 1 + 1 ∧
    (∀ b ∈ indexFiber,
      baseCenter < spine b ∧ red.Adj baseCenter (spine b)) ∧
    ∀ n, ∀ b ∈ indexFiber,
      centers n < spine b ∧ red.Adj (centers n) (spine b)

/-- The full incidence obstruction yields the exact red target, or one
stationary spine fiber on which both the base-failure witness and the
entire first-`ω` arm-predecessor tuple are fixed. -/
theorem fullOmegaTwoIncidence_redTarget_or_stationaryCombinedSpinalFan
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (hobs : FullOmegaTwoIncidenceObstruction red blue) :
    OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      StationaryCombinedSpinalFan red blue := by
  classical
  obtain ⟨arms, harms, hordered, -, hincidence⟩ := hobs
  let stage : W2 → ArmIndex := fun a ↦ ⟨(a : Ordinal), a.toOrd.2⟩
  have hstageStrict : StrictMono stage := by
    intro a b hab
    change (a : Ordinal) < (b : Ordinal)
    rw [← Ordinal.ToType.mk.apply_symm_apply a,
      ← Ordinal.ToType.mk.apply_symm_apply b] at hab
    exact (Ordinal.ToType.mk.lt_iff_lt).mp hab
  have hrepresentativeExists (a : W2) : ∃ x : arms (stage a), True := by
    obtain ⟨m, -⟩ :=
      exists_max_of_type_omegaOne_add_one (harms (stage a)).2
    exact ⟨m, trivial⟩
  let representative (a : W2) : arms (stage a) :=
    Classical.choose (hrepresentativeExists a)
  let spine : W2 → W2 := fun a ↦ representative a
  have hspineStrict : StrictMono spine := by
    intro a b hab
    exact hordered (stage a) (stage b) (hstageStrict hab)
      (representative a) (representative a).property
      (representative b) (representative b).property
  have hspineType : typeLT (Set.range spine) = ω_ 2 := by
    have htype :=
      ((hspineStrict.strictMonoOn Set.univ).orderIso
        spine Set.univ).ordinalType_congr
    have himageRange :
        typeLT (spine '' Set.univ) = typeLT (Set.range spine) :=
      (OrderIso.setCongr (spine '' Set.univ) (Set.range spine)
        Set.image_univ).ordinalType_congr
    calc
      typeLT (Set.range spine) = typeLT (spine '' Set.univ) :=
        himageRange.symm
      _ = typeLT (Set.univ : Set W2) := htype.symm
      _ = typeLT W2 := OrderIso.Set.univ.ordinalType_congr
      _ = ω_ 2 := by
        simpa only [W2] using Ordinal.type_toType (ω_ 2 : Ordinal.{0})
  obtain ⟨base, hbaseSub, hbaseRed, hbaseType⟩ |
      ⟨base, hbaseSub, hbaseBlue, hbaseType⟩ :=
    OrdinalRamsey.on_set_of_type
      (Erdos1172Part3CHAsymmetric.red_target_or_blue_omegaOne_add_one hCH)
      red blue hcompl (Set.range spine) hspineType
  · exact Or.inl ⟨base, hbaseRed, hbaseType⟩
  · obtain ⟨maximum, hmaximum⟩ :=
      exists_max_of_type_omegaOne_add_one hbaseType
    obtain ⟨anchor, hanchorEq⟩ := hbaseSub maximum.property
    have hanchorMem : spine anchor ∈ base :=
      hanchorEq.symm ▸ maximum.property
    have hanchorMax (y : W2) (hy : y ∈ base) : y ≤ spine anchor := by
      have hle : (⟨y, hy⟩ : base) ≤ maximum :=
        le_of_not_gt ((isMax_iff_forall_not_lt.mp hmaximum) ⟨y, hy⟩)
      change y ≤ (maximum : W2) at hle
      exact hle.trans_eq hanchorEq.symm
    have hbaseFailureExists (b : W2) (hb : b ∈ Set.Ioi anchor) :
        ∃ y : base, red.Adj y (spine b) := by
      by_contra hnone
      have hblueAdj : ∀ y ∈ base, blue.Adj y (spine b) := by
        intro y hy
        rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
        refine ⟨((hanchorMax y hy).trans_lt (hspineStrict hb)).ne, ?_⟩
        intro hred
        exact hnone ⟨⟨y, hy⟩, hred⟩
      obtain ⟨t, ht, httype⟩ :=
        blue.exists_clique_type_add_one_of_common_later
          hbaseBlue hbaseType
          (fun y hy ↦ (hanchorMax y hy).trans_lt (hspineStrict hb))
          hblueAdj
      apply hnoBlue
      refine ⟨t, ht, ?_⟩
      calc
        typeLT t = (ω_ 1 + 1) + 1 := httype
        _ = ω_ 1 + 2 := by norm_num [add_assoc]
    let baseFailure (b : W2) (hb : b ∈ Set.Ioi anchor) : base :=
      Classical.choose (hbaseFailureExists b hb)
    have hbaseFailureRed (b : W2) (hb : b ∈ Set.Ioi anchor) :
        red.Adj (baseFailure b hb) (spine b) :=
      Classical.choose_spec (hbaseFailureExists b hb)
    have homegaLt : (ω : Ordinal.{0}) < ω_ 2 := by
      simpa only [Ordinal.omega_zero] using
        (Ordinal.omega_lt_omega.mpr
          (show (0 : Ordinal.{0}) < 2 by norm_num))
    let earlyPoint (n : ℕ) : W2 :=
      Ordinal.ToType.mk ⟨(n : Ordinal),
        (Ordinal.natCast_lt_omega0 n).trans homegaLt⟩
    let early (n : ℕ) : ArmIndex := stage (earlyPoint n)
    have hearlyPointStrict : StrictMono earlyPoint := by
      intro i j hij
      apply Ordinal.ToType.mk.lt_iff_lt.mpr
      change (i : Ordinal) < (j : Ordinal)
      exact_mod_cast hij
    have hearlyStrict : StrictMono early :=
      hstageStrict.comp hearlyPointStrict
    have hearlyPointLtCutoff (n : ℕ) :
        earlyPoint n < omegaOneCutoff := by
      apply Ordinal.ToType.mk.lt_iff_lt.mpr
      change (n : Ordinal) < ω_ 1
      have homegaOne : (ω : Ordinal.{0}) < ω_ 1 := by
        simpa only [Ordinal.omega_zero] using
          (Ordinal.omega_lt_omega.mpr
            (show (0 : Ordinal.{0}) < 1 by norm_num))
      exact (Ordinal.natCast_lt_omega0 n).trans homegaOne
    have hearlyBeforeTail (n : ℕ) (b : W2)
        (hb : b ∈ Set.Ioi omegaOneCutoff) :
        early n < stage b :=
      hstageStrict ((hearlyPointLtCutoff n).trans hb)
    have hdefaultArmExists (n : ℕ) : ∃ x : arms (early n), True := by
      obtain ⟨m, -⟩ :=
        exists_max_of_type_omegaOne_add_one (harms (early n)).2
      exact ⟨m, trivial⟩
    have harmPredecessorExists (b : W2)
        (hb : b ∈ Set.Ioi omegaOneCutoff) (n : ℕ) :
        ∃ x : arms (early n), red.Adj x (representative b) := by
      obtain ⟨x, hx, hred⟩ :=
        hincidence (early n) (stage b) (hearlyBeforeTail n b hb)
          (representative b) (representative b).property
      exact ⟨⟨x, hx⟩, hred⟩
    let armPredecessor (b : W2)
        (hb : b ∈ Set.Ioi omegaOneCutoff) (n : ℕ) : arms (early n) :=
      Classical.choose (harmPredecessorExists b hb n)
    have harmPredecessorRed (b : W2)
        (hb : b ∈ Set.Ioi omegaOneCutoff) (n : ℕ) :
        red.Adj (armPredecessor b hb n) (spine b) :=
      Classical.choose_spec (harmPredecessorExists b hb n)
    let Coord : ℕ → Type := fun k ↦ match k with
      | 0 => base
      | n + 1 => arms (early n)
    have hbaseCard : #base = ℵ_ 1 := by
      have hc := congrArg Ordinal.card hbaseType
      simpa only [Ordinal.card_type, Cardinal.card_omega_one_add_one] using hc
    have harmsCard (n : ℕ) : #(arms (early n)) = ℵ_ 1 := by
      have hc := congrArg Ordinal.card (harms (early n)).2
      simpa only [Ordinal.card_type, Cardinal.card_omega_one_add_one] using hc
    have hCoordCard (k : ℕ) : #(Coord k) = ℵ_ 1 := by
      cases k with
      | zero => simpa only [Coord] using hbaseCard
      | succ n => simpa only [Coord] using harmsCard n
    let combinedProfile (b : W2) : ∀ k : ℕ, Coord k :=
      fun k ↦ match k with
      | 0 => if hb : b ∈ Set.Ioi anchor then
          baseFailure b hb else maximum
      | n + 1 => if hb : b ∈ Set.Ioi omegaOneCutoff then
          armPredecessor b hb n else Classical.choose (hdefaultArmExists n)
    obtain ⟨fixedProfile, rawFiber, hrawFiberStationary,
        hrawFiberCard, hrawFiberType, hrawFiberTail,
        hprofileConstant⟩ :=
      exists_stationary_fiber_of_countable_alephOne_profile
        hCH Coord hCoordCard combinedProfile
    let indexFiber : Set W2 :=
      {b | b ∈ rawFiber ∧ anchor < b}
    have hindexFiberStationary : IsStationary indexFiber :=
      Erdos1172Part3StationaryCombinedFan.IsStationary.inter_Ioi_omegaTwo
        hrawFiberStationary anchor
    have hreg : (ℵ_ 2 : Cardinal.{0}).IsRegular := by
      rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num]
      exact Cardinal.isRegular_aleph_add_one 1
    have hindexFiberCard : #indexFiber = ℵ_ 2 := by
      apply le_antisymm
      · calc
          #indexFiber ≤ #W2 := Cardinal.mk_set_le indexFiber
          _ = ℵ_ 2 := by
            simp only [W2, Cardinal.mk_toType, Ordinal.card_omega]
      · have hcofW2 : Order.cof W2 = ℵ_ 2 := by
          calc
            Order.cof W2 = (ω_ 2 : Ordinal.{0}).cof :=
              Ordinal.cof_toType (ω_ 2 : Ordinal.{0})
            _ = ℵ_ 2 := by
              simpa only [Cardinal.ord_aleph] using hreg.cof_ord
        rw [← hcofW2]
        exact Order.cof_le hindexFiberStationary.isCofinal
    have hindexFiberType : typeLT indexFiber = ω_ 2 :=
      typeLT_eq_omegaTwo_of_mk_eq hindexFiberCard
    have hindexFiberTail :
        indexFiber ⊆ Set.Ioi anchor ∩ Set.Ioi omegaOneCutoff := by
      intro b hb
      exact ⟨hb.2, hrawFiberTail hb.1⟩
    have hfixedBaseCenterMem : (fixedProfile 0 : W2) ∈ base :=
      (fixedProfile 0).property
    let baseCenter : W2 := fixedProfile 0
    have hbaseCenterCross (b : W2) (hb : b ∈ indexFiber) :
        baseCenter < spine b ∧ red.Adj baseCenter (spine b) := by
      have hbAnchor : b ∈ Set.Ioi anchor := by exact hb.2
      have hprofileEq : combinedProfile b = fixedProfile :=
        hprofileConstant b hb.1
      have hcoordinateEq :
          baseFailure b hbAnchor = fixedProfile 0 := by
        have h := congrFun hprofileEq 0
        change (if hba : b ∈ Set.Ioi anchor then
          baseFailure b hba else maximum) = fixedProfile 0 at h
        simp only [dif_pos hbAnchor] at h
        exact h
      refine ⟨(hanchorMax baseCenter hfixedBaseCenterMem).trans_lt
        (hspineStrict hbAnchor), ?_⟩
      simpa only [baseCenter, hcoordinateEq] using
        hbaseFailureRed b hbAnchor
    let rawCenters : ℕ → W2 := fun n ↦ fixedProfile (n + 1)
    have hrawCentersMem (n : ℕ) : rawCenters n ∈ arms (early n) :=
      (fixedProfile (n + 1)).property
    have hrawCentersStrict : StrictMono rawCenters := by
      intro i j hij
      exact hordered (early i) (early j) (hearlyStrict hij)
        (rawCenters i) (hrawCentersMem i)
        (rawCenters j) (hrawCentersMem j)
    have hrawCentersCross (n : ℕ) (b : W2) (hb : b ∈ indexFiber) :
        rawCenters n < spine b ∧ red.Adj (rawCenters n) (spine b) := by
      have htail : b ∈ Set.Ioi omegaOneCutoff := hrawFiberTail hb.1
      have hprofileEq : combinedProfile b = fixedProfile :=
        hprofileConstant b hb.1
      have hcoordinateEq :
          armPredecessor b htail n = fixedProfile (n + 1) := by
        have h := congrFun hprofileEq (n + 1)
        change (if hbt : b ∈ Set.Ioi omegaOneCutoff then
          armPredecessor b hbt n else
            Classical.choose (hdefaultArmExists n)) =
          fixedProfile (n + 1) at h
        rw [dif_pos htail] at h
        exact h
      refine ⟨hordered (early n) (stage b) (hearlyBeforeTail n b htail)
        (rawCenters n) (hrawCentersMem n)
        (representative b) (representative b).property, ?_⟩
      simpa only [rawCenters, spine, hcoordinateEq] using
        harmPredecessorRed b htail n
    obtain ⟨indices, hindicesStrict, hcentersType,
        hcentersHomogeneous⟩ :=
      exists_homogeneous_strict_subsequence red blue hcompl
        rawCenters hrawCentersStrict
    let centers : ℕ → W2 := rawCenters ∘ indices
    let centerArms : ℕ → Set W2 := fun n ↦ arms (early (indices n))
    have hcentersStrict : StrictMono centers :=
      hrawCentersStrict.comp hindicesStrict
    have hcenterArms (n : ℕ) :
        blue.IsClique (centerArms n) ∧
          typeLT (centerArms n) = ω_ 1 + 1 :=
      harms (early (indices n))
    have hcentersMem (n : ℕ) : centers n ∈ centerArms n :=
      hrawCentersMem (indices n)
    have hcenterArmsOrdered (i j : ℕ) (hij : i < j) :
        ∀ x ∈ centerArms i, ∀ y ∈ centerArms j, x < y := by
      exact hordered (early (indices i)) (early (indices j))
        (hearlyStrict (hindicesStrict hij))
    let representativeFiber : Set W2 := spine '' indexFiber
    have hrepresentativeFiberCard : #representativeFiber = ℵ_ 2 := by
      calc
        #representativeFiber = #indexFiber :=
          Cardinal.mk_image_eq hspineStrict.injective
        _ = ℵ_ 2 := hindexFiberCard
    have hrepresentativeFiberType :
        typeLT representativeFiber = ω_ 2 :=
      typeLT_eq_omegaTwo_of_mk_eq hrepresentativeFiberCard
    obtain ⟨fan, hfanSub, hfanRed, hfanType⟩ |
        ⟨fan, hfanSub, hfanBlue, hfanType⟩ :=
      OrdinalRamsey.on_set_of_type
        (Erdos1172Part3CHAsymmetric.red_target_or_blue_omegaOne_add_one hCH)
        red blue hcompl representativeFiber hrepresentativeFiberType
    · exact Or.inl ⟨fan, hfanRed, hfanType⟩
    · right
      refine ⟨spine, base, anchor, baseCenter, centerArms, centers,
        indexFiber, representativeFiber, fan, hspineStrict, hspineType,
        hbaseSub, hbaseBlue, hbaseType, hanchorMem, hanchorMax,
        hfixedBaseCenterMem, hcenterArms, hcentersMem,
        hcenterArmsOrdered, hcentersStrict, ?_, ?_,
        hindexFiberStationary, hindexFiberCard, hindexFiberType,
        hindexFiberTail, rfl, hrepresentativeFiberCard,
        hrepresentativeFiberType, hfanSub, hfanBlue, hfanType,
        hbaseCenterCross, ?_⟩
      · simpa only [centers] using hcentersType
      · simpa only [centers] using hcentersHomogeneous
      · intro n b hb
        exact hrawCentersCross (indices n) b hb

/-- Global exact-target-or-shared-stationary-combined-fan normal form
under CH. -/
theorem part3_exact_or_stationaryCombinedSpinalFan
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      StationaryCombinedSpinalFan red blue := by
  by_cases htarget :
      OrdinalRamsey.HasCliqueOfType red RedTarget ∨
        OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)
  · exact Or.inl htarget
  · right
    have hnone := not_or.mp htarget
    obtain hexact | hobs :=
      part3_exact_or_fullOmegaTwoIncidenceObstruction hCH red blue hcompl
    · exact (htarget hexact).elim
    · obtain hred | hfan :=
        fullOmegaTwoIncidence_redTarget_or_stationaryCombinedSpinalFan
          hCH red blue hcompl hnone.2 hobs
      · exact (hnone.1 hred).elim
      · exact hfan

end Erdos1172Part3StationaryCombinedFan
