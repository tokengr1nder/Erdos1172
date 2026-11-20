/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3TransversalPredecessorPattern
public import Erdos1172.Part3StationarySpinalFan

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3StationaryCountablePredecessors

open Erdos1172Part3Failure Erdos1172Part3TransfiniteIncidence
  Erdos1172Part3HomogeneousFailureLadder
  Erdos1172Part3TransversalPredecessorPattern

/-- The initial ordinal `ω₁`, used as the code space for countable
`ℵ₁`-valued predecessor profiles. -/
abbrev W1 : Type := (ω_ 1 : Ordinal.{0}).ToType

theorem omegaOne_lt_omegaTwo :
    (ω_ 1 : Ordinal.{0}) < ω_ 2 :=
  Ordinal.omega_lt_omega.mpr one_lt_two

/-- The canonical `ω₁` cutoff inside the initial ordinal `ω₂`. -/
noncomputable def omegaOneCutoff : W2 :=
  Ordinal.ToType.mk ⟨ω_ 1, omegaOne_lt_omegaTwo⟩

/-- The final segment above the canonical `ω₁` cutoff is stationary in
`ω₂`. -/
theorem isStationary_Ioi_omegaOneCutoff :
    IsStationary (Set.Ioi omegaOneCutoff) := by
  have htailCard : #(Set.Ioi omegaOneCutoff) = ℵ_ 2 :=
    mk_Ioi_omegaTwo_eq omegaOneCutoff
  have htailNonempty : (Set.Ioi omegaOneCutoff).Nonempty := by
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

/-- Under CH, the countable dependent product of `ℵ₁`-sized coordinate
types has cardinality at most `ℵ₁`. -/
theorem mk_countable_alephOne_profile_le
    (hCH : CH) (A : ℕ → Type) (hA : ∀ n, #(A n) = ℵ_ 1) :
    #(∀ n : ℕ, A n) ≤ ℵ_ 1 := by
  rw [Cardinal.mk_pi]
  calc
    Cardinal.prod (fun n : ℕ ↦ #(A n)) ≤
        Cardinal.prod (fun _ : ℕ ↦ (ℵ_ 1 : Cardinal.{0})) :=
      Cardinal.prod_le_prod _ _ (fun n ↦ (hA n).le)
    _ = (ℵ_ 1 : Cardinal.{0}) ^ #ℕ := Cardinal.prod_const' ℕ (ℵ_ 1)
    _ = (ℵ_ 1 : Cardinal.{0}) ^ ℵ₀ := by simp
    _ = ℵ_ 1 := hCH.aleph_one_power_aleph_zero

/-- Stationary version of countable dependent-profile concentration.
Encode the whole profile injectively into `W1`, embed that code below the
canonical `ω₁` point of `W2`, and press the resulting regressive map down
on the stationary tail.  Thus the complete countable tuple, not merely one
coordinate, is constant on a stationary fiber. -/
theorem exists_stationary_fiber_of_countable_alephOne_profile
    (hCH : CH) (A : ℕ → Type) (hA : ∀ n, #(A n) = ℵ_ 1)
    (profile : W2 → ∀ n, A n) :
    ∃ (fixedProfile : ∀ n, A n) (fiber : Set W2),
      IsStationary fiber ∧ #fiber = ℵ_ 2 ∧
      typeLT fiber = ω_ 2 ∧ fiber ⊆ Set.Ioi omegaOneCutoff ∧
      ∀ b ∈ fiber, profile b = fixedProfile := by
  classical
  let Profile := ∀ n : ℕ, A n
  have hW1Card : #W1 = ℵ_ 1 := by
    simp only [W1, Cardinal.mk_toType, Ordinal.card_omega]
  have hprofileW1 : #Profile ≤ #W1 := by
    rw [hW1Card]
    exact mk_countable_alephOne_profile_le hCH A hA
  let profileCode : Profile ↪ W1 :=
    Classical.choice ((Cardinal.le_def Profile W1).mp hprofileW1)
  let w1ToW2 : W1 → W2 := fun a ↦
    Ordinal.ToType.mk ⟨(a : Ordinal), by
      change (a : Ordinal) < ω_ 2
      exact a.toOrd.2.trans omegaOne_lt_omegaTwo⟩
  have hw1ToW2Strict : StrictMono w1ToW2 := by
    intro a b hab
    apply Ordinal.ToType.mk.lt_iff_lt.mpr
    change (a : Ordinal) < (b : Ordinal)
    rw [← Ordinal.ToType.mk.apply_symm_apply a,
      ← Ordinal.ToType.mk.apply_symm_apply b] at hab
    exact (Ordinal.ToType.mk.lt_iff_lt).mp hab
  have hcodeBelow (p : Profile) :
      w1ToW2 (profileCode p) < omegaOneCutoff := by
    apply Ordinal.ToType.mk.lt_iff_lt.mpr
    exact (profileCode p).toOrd.2
  let codeAll (b : W2) : W2 :=
    if hb : b ∈ Set.Ioi omegaOneCutoff then
      w1ToW2 (profileCode (profile b)) else b
  have hcodeRegressive :
      ∀ b ∈ Set.Ioi omegaOneCutoff, codeAll b < b := by
    intro b hb
    simpa only [codeAll, dif_pos hb] using
      (hcodeBelow (profile b)).trans hb
  have hreg : (ℵ_ 2 : Cardinal.{0}).IsRegular := by
    rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num]
    exact Cardinal.isRegular_aleph_add_one 1
  have hpress : StationaryPressingDown W2 := by
    change StationaryPressingDown ((ω_ 2 : Ordinal.{0}).ToType)
    rw [← Cardinal.ord_aleph]
    exact Set.stationaryPressingDown_ord (ℵ_ 2) hreg
      (Cardinal.aleph0_lt_aleph.mpr (by norm_num))
  obtain ⟨value, hstationaryCodeFiber⟩ :=
    hpress (Set.Ioi omegaOneCutoff) codeAll
      isStationary_Ioi_omegaOneCutoff hcodeRegressive
  let codeFiber : Set W2 :=
    {b | b ∈ Set.Ioi omegaOneCutoff ∧ codeAll b = value}
  have hcodeFiberStationary : IsStationary codeFiber :=
    hstationaryCodeFiber
  obtain ⟨sample, hsample⟩ := hcodeFiberStationary.nonempty
  let fixedProfile : Profile := profile sample
  have hprofileConstant (b : W2) (hb : b ∈ codeFiber) :
      profile b = fixedProfile := by
    have hbCode : w1ToW2 (profileCode (profile b)) = value := by
      simpa only [codeAll, dif_pos hb.1] using hb.2
    have hsampleCode :
        w1ToW2 (profileCode fixedProfile) = value := by
      simpa only [fixedProfile, codeAll, dif_pos hsample.1] using hsample.2
    exact profileCode.injective
      (hw1ToW2Strict.injective (hbCode.trans hsampleCode.symm))
  have hcodeFiberCard : #codeFiber = ℵ_ 2 := by
    apply le_antisymm
    · calc
        #codeFiber ≤ #W2 := Cardinal.mk_set_le codeFiber
        _ = ℵ_ 2 := by
          simp only [W2, Cardinal.mk_toType, Ordinal.card_omega]
    · have hcofW2 : Order.cof W2 = ℵ_ 2 := by
        calc
          Order.cof W2 = (ω_ 2 : Ordinal.{0}).cof :=
            Ordinal.cof_toType (ω_ 2 : Ordinal.{0})
          _ = ℵ_ 2 := by
            simpa only [Cardinal.ord_aleph] using hreg.cof_ord
      rw [← hcofW2]
      exact Order.cof_le hcodeFiberStationary.isCofinal
  exact ⟨fixedProfile, codeFiber, hcodeFiberStationary,
    hcodeFiberCard, typeLT_eq_omegaTwo_of_mk_eq hcodeFiberCard,
    fun _ hb ↦ hb.1, hprofileConstant⟩

/-- Stationary simultaneous predecessor concentration.  Countably many
fixed predecessors lie in countably many strictly ordered blue `ω₁ + 1`
arms and are all red-adjacent to every point of a stationary `ω₂` spine
fiber.  After ordinary infinite Ramsey the predecessors are homogeneous;
after the CH asymmetric theorem the stationary spine image retains a blue
transversal of exact type `ω₁ + 1`. -/
def StationaryCountablyConcentratedPredecessorPattern
    (red blue : SimpleGraph W2) : Prop :=
  ∃ (centerArms : ℕ → Set W2) (centers : ℕ → W2)
      (spineFull : W2 → W2) (indexFiber representativeFiber transversal : Set W2),
    (∀ n, blue.IsClique (centerArms n) ∧
      typeLT (centerArms n) = ω_ 1 + 1) ∧
    (∀ n, centers n ∈ centerArms n) ∧
    (∀ i j, i < j → ∀ x ∈ centerArms i,
      ∀ y ∈ centerArms j, x < y) ∧
    StrictMono centers ∧ typeLT (Set.range centers) = ω ∧
    (red.IsClique (Set.range centers) ∨
      blue.IsClique (Set.range centers)) ∧
    StrictMono spineFull ∧ typeLT (Set.range spineFull) = ω_ 2 ∧
    IsStationary indexFiber ∧ #indexFiber = ℵ_ 2 ∧
    typeLT indexFiber = ω_ 2 ∧
    representativeFiber = spineFull '' indexFiber ∧
    #representativeFiber = ℵ_ 2 ∧
    typeLT representativeFiber = ω_ 2 ∧
    transversal ⊆ representativeFiber ∧
    blue.IsClique transversal ∧ typeLT transversal = ω_ 1 + 1 ∧
    ∀ n, ∀ b ∈ indexFiber,
      centers n < spineFull b ∧ red.Adj (centers n) (spineFull b)

/-- Blue-center branch of the stationary countable predecessor pattern:
an exact blue `ω` sequence is completely red-joined to a stationary
`ω₂` spine fiber, whose image contains a blue `ω₁ + 1` transversal. -/
def StationaryBluePredecessorRectangle
    (red blue : SimpleGraph W2) : Prop :=
  ∃ (centers : ℕ → W2) (spine : W2 → W2)
      (indexFiber transversal : Set W2),
    StrictMono centers ∧ typeLT (Set.range centers) = ω ∧
    blue.IsClique (Set.range centers) ∧
    StrictMono spine ∧ typeLT (Set.range spine) = ω_ 2 ∧
    IsStationary indexFiber ∧ #indexFiber = ℵ_ 2 ∧
    typeLT indexFiber = ω_ 2 ∧
    transversal ⊆ spine '' indexFiber ∧
    blue.IsClique transversal ∧ typeLT transversal = ω_ 1 + 1 ∧
    ∀ n, ∀ b ∈ indexFiber,
      centers n < spine b ∧ red.Adj (centers n) (spine b)

/-- Homogeneous split of the stationary pattern.  A red predecessor
sequence extends with any stationary-fiber spine point to exact type
`ω + 1`; otherwise the stationary blue predecessor rectangle remains. -/
theorem StationaryCountablyConcentratedPredecessorPattern.redOmegaAddOne_or_stationaryBlueRectangle
    {red blue : SimpleGraph W2}
    (hpattern : StationaryCountablyConcentratedPredecessorPattern red blue) :
    OrdinalRamsey.HasCliqueOfType red (ω + 1) ∨
      StationaryBluePredecessorRectangle red blue := by
  obtain ⟨centerArms, centers, spine, indexFiber,
    representativeFiber, transversal, -, -, -, hcentersStrict,
    hcentersType, hcentersRed | hcentersBlue,
    hspineStrict, hspineType, hfiberStationary, hfiberCard,
    hfiberType, hrepresentativeFiber, -, -, htransversalSub,
    htransversalBlue, htransversalType, hcross⟩ := hpattern
  · left
    obtain ⟨b, hb⟩ := hfiberStationary.nonempty
    obtain ⟨clique, hclique, hcliqueType⟩ :=
      red.exists_clique_type_add_one_of_common_later
        hcentersRed hcentersType
        (fun y hy ↦ by
          obtain ⟨n, rfl⟩ := hy
          exact (hcross n b hb).1)
        (fun y hy ↦ by
          obtain ⟨n, rfl⟩ := hy
          exact (hcross n b hb).2)
    exact ⟨clique, hclique, hcliqueType⟩
  · right
    refine ⟨centers, spine, indexFiber, transversal,
      hcentersStrict, hcentersType, hcentersBlue,
      hspineStrict, hspineType, hfiberStationary, hfiberCard,
      hfiberType, ?_, htransversalBlue, htransversalType, hcross⟩
    rw [← hrepresentativeFiber]
    exact htransversalSub

/-- A full incidence obstruction yields the exact red target, or a
stationary fiber on which the entire first-`ω` predecessor tuple is fixed. -/
theorem fullOmegaTwoIncidence_redTarget_or_stationaryCountablyConcentratedPattern
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (hobs : FullOmegaTwoIncidenceObstruction red blue) :
    OrdinalRamsey.HasCliqueOfType red
        Erdos1172Part3FiniteStars.RedTarget ∨
      StationaryCountablyConcentratedPredecessorPattern red blue := by
  classical
  obtain ⟨arms, harms, hordered, -, hincidence⟩ := hobs
  let stage : W2 → ArmIndex := fun a ↦ ⟨(a : Ordinal), a.toOrd.2⟩
  have hstageStrict : StrictMono stage := by
    intro a b hab
    change (a : Ordinal) < (b : Ordinal)
    rw [← Ordinal.ToType.mk.apply_symm_apply a,
      ← Ordinal.ToType.mk.apply_symm_apply b] at hab
    exact (Ordinal.ToType.mk.lt_iff_lt).mp hab
  have homegaLt : (ω : Ordinal.{0}) < ω_ 2 := by
    simpa only [Ordinal.omega_zero] using
      (Ordinal.omega_lt_omega.mpr (show (0 : Ordinal.{0}) < 2 by norm_num))
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
  have hrepresentativeExists (a : W2) : ∃ x : arms (stage a), True := by
    obtain ⟨m, -⟩ :=
      exists_max_of_type_omegaOne_add_one (harms (stage a)).2
    exact ⟨m, trivial⟩
  let representative (a : W2) : arms (stage a) :=
    Classical.choose (hrepresentativeExists a)
  let spineFull : W2 → W2 := fun a ↦ representative a
  have hspineFullStrict : StrictMono spineFull := by
    intro a b hab
    exact hordered (stage a) (stage b) (hstageStrict hab)
      (representative a) (representative a).property
      (representative b) (representative b).property
  have hspineFullType : typeLT (Set.range spineFull) = ω_ 2 := by
    have htype :=
      ((hspineFullStrict.strictMonoOn Set.univ).orderIso
        spineFull Set.univ).ordinalType_congr
    have himageRange :
        typeLT (spineFull '' Set.univ) = typeLT (Set.range spineFull) :=
      (OrderIso.setCongr (spineFull '' Set.univ) (Set.range spineFull)
        Set.image_univ).ordinalType_congr
    calc
      typeLT (Set.range spineFull) = typeLT (spineFull '' Set.univ) :=
        himageRange.symm
      _ = typeLT (Set.univ : Set W2) := htype.symm
      _ = typeLT W2 := OrderIso.Set.univ.ordinalType_congr
      _ = ω_ 2 := by
        simpa only [W2] using Ordinal.type_toType (ω_ 2 : Ordinal.{0})
  have hdefaultExists (n : ℕ) : ∃ x : arms (early n), True := by
    obtain ⟨m, -⟩ :=
      exists_max_of_type_omegaOne_add_one (harms (early n)).2
    exact ⟨m, trivial⟩
  have hpredecessorExists (b : W2)
      (hb : b ∈ Set.Ioi omegaOneCutoff) (n : ℕ) :
      ∃ x : arms (early n), red.Adj x (representative b) := by
    obtain ⟨x, hx, hred⟩ :=
      hincidence (early n) (stage b) (hearlyBeforeTail n b hb)
        (representative b) (representative b).property
    exact ⟨⟨x, hx⟩, hred⟩
  let predecessorProfile (b : W2) : ∀ n : ℕ, arms (early n) :=
    fun n ↦ if hb : b ∈ Set.Ioi omegaOneCutoff then
      Classical.choose (hpredecessorExists b hb n)
    else Classical.choose (hdefaultExists n)
  have hpredecessorRed (b : W2)
      (hb : b ∈ Set.Ioi omegaOneCutoff) (n : ℕ) :
      red.Adj (predecessorProfile b n) (representative b) := by
    simpa only [predecessorProfile, dif_pos hb] using
      Classical.choose_spec (hpredecessorExists b hb n)
  have harmsCard (n : ℕ) : #(arms (early n)) = ℵ_ 1 := by
    have hc := congrArg Ordinal.card (harms (early n)).2
    simpa only [Ordinal.card_type, Cardinal.card_omega_one_add_one] using hc
  obtain ⟨fixedProfile, indexFiber, hindexFiberStationary,
      hindexFiberCard, hindexFiberType, hindexFiberTail,
      hprofileConstant⟩ :=
    exists_stationary_fiber_of_countable_alephOne_profile
      hCH (fun n ↦ arms (early n)) harmsCard predecessorProfile
  let rawCenters : ℕ → W2 := fun n ↦ fixedProfile n
  have hrawCentersMem (n : ℕ) : rawCenters n ∈ arms (early n) :=
    (fixedProfile n).property
  have hrawCentersStrict : StrictMono rawCenters := by
    intro i j hij
    exact hordered (early i) (early j) (hearlyStrict hij)
      (rawCenters i) (hrawCentersMem i)
      (rawCenters j) (hrawCentersMem j)
  have hrawCentersCross (n : ℕ) (b : W2) (hb : b ∈ indexFiber) :
      rawCenters n < spineFull b ∧ red.Adj (rawCenters n) (spineFull b) := by
    have htail : b ∈ Set.Ioi omegaOneCutoff := hindexFiberTail hb
    have hprofileEq : predecessorProfile b = fixedProfile :=
      hprofileConstant b hb
    refine ⟨hordered (early n) (stage b) (hearlyBeforeTail n b htail)
      (rawCenters n) (hrawCentersMem n)
      (representative b) (representative b).property, ?_⟩
    simpa only [rawCenters, spineFull, hprofileEq] using
      hpredecessorRed b htail n
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
  let representativeFiber : Set W2 := spineFull '' indexFiber
  have hrepresentativeFiberCard : #representativeFiber = ℵ_ 2 := by
    calc
      #representativeFiber = #indexFiber :=
        Cardinal.mk_image_eq hspineFullStrict.injective
      _ = ℵ_ 2 := hindexFiberCard
  have hrepresentativeFiberType :
      typeLT representativeFiber = ω_ 2 :=
    typeLT_eq_omegaTwo_of_mk_eq hrepresentativeFiberCard
  obtain ⟨transversal, htransversalSub, htransversalRed,
      htransversalType⟩ |
      ⟨transversal, htransversalSub, htransversalBlue,
        htransversalType⟩ :=
    OrdinalRamsey.on_set_of_type
      (Erdos1172Part3CHAsymmetric.red_target_or_blue_omegaOne_add_one hCH)
      red blue hcompl representativeFiber hrepresentativeFiberType
  · exact Or.inl ⟨transversal, htransversalRed, htransversalType⟩
  · right
    refine ⟨centerArms, centers, spineFull, indexFiber,
      representativeFiber, transversal, hcenterArms, hcentersMem,
      hcenterArmsOrdered, hcentersStrict, ?_, ?_,
      hspineFullStrict, hspineFullType, hindexFiberStationary,
      hindexFiberCard, hindexFiberType, rfl,
      hrepresentativeFiberCard, hrepresentativeFiberType,
      htransversalSub, htransversalBlue, htransversalType, ?_⟩
    · simpa only [centers] using hcentersType
    · simpa only [centers] using hcentersHomogeneous
    · intro n b hb
      exact hrawCentersCross (indices n) b hb

/-- Global exact-target-or-stationary-countable-predecessor normal form
under CH. -/
theorem part3_exact_or_stationaryCountablyConcentratedPredecessorPattern
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red
        Erdos1172Part3FiniteStars.RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      StationaryCountablyConcentratedPredecessorPattern red blue := by
  obtain htarget | hobs :=
    part3_exact_or_fullOmegaTwoIncidenceObstruction hCH red blue hcompl
  · exact Or.inl htarget
  · obtain hred | hpattern :=
      fullOmegaTwoIncidence_redTarget_or_stationaryCountablyConcentratedPattern
        hCH red blue hcompl hobs
    · exact Or.inl (Or.inl hred)
    · exact Or.inr hpattern

end Erdos1172Part3StationaryCountablePredecessors
