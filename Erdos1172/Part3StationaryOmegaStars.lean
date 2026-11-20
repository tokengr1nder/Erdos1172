/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.Order.WellQuasiOrder
public import Erdos1172.Part3StationaryFiniteStars

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3StationaryOmegaStars

open Erdos1172Part3Failure Erdos1172Part3FiniteStars
  Erdos1172Part3StationaryCountablePredecessors
  Erdos1172Part3StationaryCombinedFan
  Erdos1172Part3StationaryFiniteStars

/-- Stationary-domain form of countable CH profile concentration.  The
domain is allowed to be any stationary subset of `ω₂` lying above the
canonical `ω₁` cutoff; the concentrated fiber remains inside that domain.
-/
theorem exists_stationary_fiber_of_countable_alephOne_profile_on
    (hCH : CH) (A : ℕ → Type) (hA : ∀ n, #(A n) = ℵ_ 1)
    (profile : W2 → ∀ n, A n) {domain : Set W2}
    (hdomainStationary : IsStationary domain)
    (hdomainTail : domain ⊆ Set.Ioi omegaOneCutoff) :
    ∃ (fixedProfile : ∀ n, A n) (fiber : Set W2),
      IsStationary fiber ∧ #fiber = ℵ_ 2 ∧
      typeLT fiber = ω_ 2 ∧ fiber ⊆ domain ∧
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
    if hb : b ∈ domain then w1ToW2 (profileCode (profile b)) else b
  have hcodeRegressive : ∀ b ∈ domain, codeAll b < b := by
    intro b hb
    simpa only [codeAll, dif_pos hb] using
      (hcodeBelow (profile b)).trans (hdomainTail hb)
  have hreg : (ℵ_ 2 : Cardinal.{0}).IsRegular := by
    rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num]
    exact Cardinal.isRegular_aleph_add_one 1
  have hpress : StationaryPressingDown W2 := by
    change StationaryPressingDown ((ω_ 2 : Ordinal.{0}).ToType)
    rw [← Cardinal.ord_aleph]
    exact Set.stationaryPressingDown_ord (ℵ_ 2) hreg
      (Cardinal.aleph0_lt_aleph.mpr (by norm_num))
  obtain ⟨value, hstationaryCodeFiber⟩ :=
    hpress domain codeAll hdomainStationary hcodeRegressive
  let codeFiber : Set W2 :=
    {b | b ∈ domain ∧ codeAll b = value}
  have hcodeFiberStationary : IsStationary codeFiber :=
    hstationaryCodeFiber
  obtain ⟨sample, hsample⟩ := hcodeFiberStationary.nonempty
  let fixedProfile : Profile := profile sample
  have hprofileConstant (b : W2) (hb : b ∈ codeFiber) :
      profile b = fixedProfile := by
    have hbCode : w1ToW2 (profileCode (profile b)) = value := by
      simpa only [codeAll, dif_pos hb.1] using hb.2
    have hsampleCode : w1ToW2 (profileCode fixedProfile) = value := by
      simpa only [fixedProfile, codeAll, dif_pos hsample.1] using hsample.2
    exact profileCode.injective
      (hw1ToW2Strict.injective (hbCode.trans hsampleCode.symm))
  have hcodeFiberCard : #codeFiber = ℵ_ 2 :=
    mk_eq_alephTwo_of_isStationary hcodeFiberStationary
  exact ⟨fixedProfile, codeFiber, hcodeFiberStationary,
    hcodeFiberCard, typeLT_eq_omegaTwo_of_mk_eq hcodeFiberCard,
    fun _ hb ↦ hb.1, hprofileConstant⟩

/-- Spine indices whose vertices lie in `base` and are red-adjacent to the
spine vertex at index `b`. -/
def baseRedNeighborIndices (red : SimpleGraph W2) (spine : W2 → W2)
    (base : Set W2) (b : W2) : Set W2 :=
  {a | spine a ∈ base ∧ red.Adj (spine a) (spine b)}

/-- Under failure of both exact Part 3 targets, stationarily many points
of any stationary later spine fiber have infinitely many red neighbours
in the blue spine base.  Otherwise the complete finite set of neighbour
indices is regressive and Fodor freezes it on a stationary fiber.  Deleting
the corresponding finitely many base vertices makes the whole stationary
spine image `unwitnessed`, contradicting its proven smallness. -/
theorem isStationary_infinite_base_red_neighbor_indices
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (spine : W2 → W2) (hspine : StrictMono spine)
    {base : Set W2} (hbaseSub : base ⊆ Set.range spine)
    {anchor : W2} (hanchorMem : spine anchor ∈ base)
    (hanchorMax : ∀ y ∈ base, y ≤ spine anchor)
    (hbaseBlue : blue.IsClique base)
    (hbaseType : typeLT base = ω_ 1 + 1)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    {fiber : Set W2} (hfiberStationary : IsStationary fiber)
    (hfiberTail : fiber ⊆ Set.Ioi anchor) :
    IsStationary
      {b | b ∈ fiber ∧
        (baseRedNeighborIndices red spine base b).Infinite} := by
  classical
  let infiniteFiber : Set W2 :=
    {b | b ∈ fiber ∧
      (baseRedNeighborIndices red spine base b).Infinite}
  by_contra hinfiniteNonstationary
  have hinfiniteNonstationary' : ¬ IsStationary infiniteFiber := by
    simpa only [infiniteFiber] using hinfiniteNonstationary
  let finiteFiber : Set W2 := fiber \ infiniteFiber
  have hinfiniteUnionFinite : infiniteFiber ∪ finiteFiber = fiber := by
    ext b
    simp only [infiniteFiber, finiteFiber, mem_union, mem_ofPred_eq,
      mem_sdiff]
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
  have hfiniteFiberStationary : IsStationary finiteFiber := by
    have hunionStationary : IsStationary (infiniteFiber ∪ finiteFiber) := by
      simpa only [hinfiniteUnionFinite] using hfiberStationary
    rcases (isStationary_union_iff hcof).mp hunionStationary with
      hinfinite | hfinite
    · exact (hinfiniteNonstationary' hinfinite).elim
    · exact hfinite
  have hneighborFinite (b : finiteFiber) :
      (baseRedNeighborIndices red spine base b).Finite := by
    by_contra hnotFinite
    exact b.property.2 ⟨b.property.1, hnotFinite⟩
  let finiteNeighbors (b : finiteFiber) : Finset W2 :=
    (hneighborFinite b).toFinset
  let finiteNeighborsAll (b : W2) : Finset W2 :=
    if hb : b ∈ finiteFiber then finiteNeighbors ⟨b, hb⟩ else ∅
  have hfiniteNeighborsRegressive :
      ∀ b ∈ finiteFiber, ∀ a ∈ finiteNeighborsAll b, a < b := by
    intro b hb a ha
    have haFinite : a ∈ finiteNeighbors ⟨b, hb⟩ := by
      simpa only [finiteNeighborsAll, dif_pos hb] using ha
    have haNeighbor : a ∈ baseRedNeighborIndices red spine base b :=
      (hneighborFinite ⟨b, hb⟩).mem_toFinset.mp haFinite
    have haLeAnchor : a ≤ anchor :=
      hspine.le_iff_le.mp (hanchorMax (spine a) haNeighbor.1)
    exact haLeAnchor.trans_lt (hfiberTail hb.1)
  have hreg : (ℵ_ 2 : Cardinal.{0}).IsRegular := by
    rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num]
    exact Cardinal.isRegular_aleph_add_one 1
  have hpress : StationaryPressingDown W2 := by
    change StationaryPressingDown ((ω_ 2 : Ordinal.{0}).ToType)
    rw [← Cardinal.ord_aleph]
    exact Set.stationaryPressingDown_ord (ℵ_ 2) hreg
      (Cardinal.aleph0_lt_aleph.mpr (by norm_num))
  let _ : Nonempty W2 := ⟨anchor⟩
  let _ : OrderBot W2 := WellFoundedLT.toOrderBot W2
  obtain ⟨fixedNeighbors, hpressedStationary⟩ :=
    hpress.finset hcof finiteFiber finiteNeighborsAll
      hfiniteFiberStationary hfiniteNeighborsRegressive
  let pressedFiber : Set W2 :=
    {b | b ∈ finiteFiber ∧ finiteNeighborsAll b = fixedNeighbors}
  have hpressedFiberStationary : IsStationary pressedFiber :=
    hpressedStationary
  let representativeFiber : Set W2 := spine '' pressedFiber
  have hrepresentativeCard : #representativeFiber = ℵ_ 2 := by
    calc
      #representativeFiber = #pressedFiber :=
        Cardinal.mk_image_eq hspine.injective
      _ = ℵ_ 2 :=
        mk_eq_alephTwo_of_isStationary hpressedFiberStationary
  have hrepresentativeTail :
      representativeFiber ⊆ Set.Ioi (spine anchor) := by
    rintro _ ⟨b, hb, rfl⟩
    exact hspine (hfiberTail hb.1.1)
  let deletedCenters : Finset W2 := fixedNeighbors.image spine
  have hanchorIsMax : IsMax (⟨spine anchor, hanchorMem⟩ : base) := by
    rw [isMax_iff_forall_not_lt]
    intro y hy
    exact (not_lt_of_ge (hanchorMax y y.property)) hy
  let unwitnessed : Set W2 :=
    {x | x ∈ representativeFiber ∧
      ∀ y ∈ base \ (deletedCenters : Set W2), blue.Adj y x}
  have hunwitnessedSmall : #unwitnessed < ℵ_ 2 := by
    simpa only [unwitnessed] using
      mk_unwitnessed_lt_alephTwo red blue hcompl hanchorMem
        hanchorIsMax hbaseBlue hbaseType hrepresentativeTail hnoRed
        hnoBlue deletedCenters
  have hrepresentativeUnwitnessed : representativeFiber ⊆ unwitnessed := by
    rintro _ ⟨b, hb, rfl⟩
    refine ⟨⟨b, hb, rfl⟩, ?_⟩
    intro y hy
    have hlater : y < spine b :=
      (hanchorMax y hy.1).trans_lt (hspine (hfiberTail hb.1.1))
    have hnotRed : ¬ red.Adj y (spine b) := by
      intro hred
      obtain ⟨a, ha⟩ := hbaseSub hy.1
      have haNeighbor : a ∈ baseRedNeighborIndices red spine base b := by
        exact ⟨ha.symm ▸ hy.1, ha.symm ▸ hred⟩
      have haFinite : a ∈ finiteNeighbors ⟨b, hb.1⟩ :=
        (hneighborFinite ⟨b, hb.1⟩).mem_toFinset.mpr haNeighbor
      have hfixedEq : finiteNeighbors ⟨b, hb.1⟩ = fixedNeighbors := by
        simpa only [finiteNeighborsAll, dif_pos hb.1] using hb.2
      have haFixed : a ∈ fixedNeighbors := by
        rw [← hfixedEq]
        exact haFinite
      apply hy.2
      exact Finset.mem_image.mpr ⟨a, haFixed, ha⟩
    rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
    exact ⟨hlater.ne, hnotRed⟩
  have hunwitnessedEq : unwitnessed = representativeFiber :=
    Set.Subset.antisymm (fun _ hx ↦ hx.1) hrepresentativeUnwitnessed
  have hunwitnessedCard : #unwitnessed = ℵ_ 2 := by
    rw [hunwitnessedEq]
    exact hrepresentativeCard
  exact hunwitnessedSmall.ne hunwitnessedCard

/-- The range of a strictly increasing sequence in `ω₂` has exact order
type `ω`. -/
theorem typeLT_range_eq_omega_of_strictMono (f : ℕ → W2)
    (hf : StrictMono f) : typeLT (Set.range f) = ω := by
  have htype :=
    ((hf.strictMonoOn Set.univ).orderIso f Set.univ).ordinalType_congr
  have himageRange : typeLT (f '' Set.univ) = typeLT (Set.range f) :=
    (OrderIso.setCongr (f '' Set.univ) (Set.range f)
      Set.image_univ).ordinalType_congr
  calc
    typeLT (Set.range f) = typeLT (f '' Set.univ) := himageRange.symm
    _ = typeLT (Set.univ : Set ℕ) := htype.symm
    _ = typeLT ℕ := OrderIso.Set.univ.ordinalType_congr
    _ = ω := Ordinal.type_nat_lt

/-- Countably many distinct blue base vertices can be frozen as common
red neighbours of one stationary spine fiber.  The infinite-neighbour
stationary set supplies an injective sequence at each index; CH encodes
the whole sequence below `ω₁`, and Fodor freezes it.  A monotone
subsequence then has exact order type `ω`. -/
theorem exists_stationary_omega_base_star
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
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
    ∃ (centers : ℕ → W2) (indexFiber : Set W2),
      StrictMono centers ∧ typeLT (Set.range centers) = ω ∧
      (∀ n, centers n ∈ base) ∧
      blue.IsClique (Set.range centers) ∧
      IsStationary indexFiber ∧ #indexFiber = ℵ_ 2 ∧
      typeLT indexFiber = ω_ 2 ∧
      indexFiber ⊆ initialFiber ∩ Set.Ioi omegaOneCutoff ∧
      ∀ n, ∀ b ∈ indexFiber,
        centers n < spine b ∧ red.Adj (centers n) (spine b) := by
  classical
  let infiniteFiber : Set W2 :=
    {b | b ∈ initialFiber ∧
      (baseRedNeighborIndices red spine base b).Infinite}
  have hinfiniteFiberStationary : IsStationary infiniteFiber := by
    simpa only [infiniteFiber] using
      isStationary_infinite_base_red_neighbor_indices
        red blue hcompl spine hspine hbaseSub hanchorMem hanchorMax
        hbaseBlue hbaseType hnoRed hnoBlue hinitialStationary hinitialTail
  let profileDomain : Set W2 :=
    {b | b ∈ infiniteFiber ∧ omegaOneCutoff < b}
  have hprofileDomainStationary : IsStationary profileDomain := by
    simpa only [profileDomain] using
      Erdos1172Part3StationaryCombinedFan.IsStationary.inter_Ioi_omegaTwo
        hinfiniteFiberStationary omegaOneCutoff
  have hprofileDomainTail : profileDomain ⊆ Set.Ioi omegaOneCutoff :=
    fun _ hb ↦ hb.2
  have hneighborInfinite (b : profileDomain) :
      (baseRedNeighborIndices red spine base b).Infinite :=
    b.property.1.2
  let neighborEmbedding (b : profileDomain) :
      ℕ ↪ baseRedNeighborIndices red spine base b :=
    (hneighborInfinite b).natEmbedding _
  let profile : W2 → ℕ → base := fun b ↦
    if hb : b ∈ profileDomain then
      fun n ↦ ⟨spine (neighborEmbedding ⟨b, hb⟩ n),
        (neighborEmbedding ⟨b, hb⟩ n).property.1⟩
    else fun _ ↦ ⟨spine anchor, hanchorMem⟩
  have hbaseCard : #base = ℵ_ 1 := by
    have hc := congrArg Ordinal.card hbaseType
    simpa only [Ordinal.card_type, Cardinal.card_omega_one_add_one] using hc
  obtain ⟨fixedProfile, indexFiber, hindexStationary, hindexCard,
      hindexType, hindexSub, hprofileConstant⟩ :=
    exists_stationary_fiber_of_countable_alephOne_profile_on
      hCH (fun _ : ℕ ↦ base) (fun _ ↦ hbaseCard) profile
      hprofileDomainStationary hprofileDomainTail
  let rawCenters : ℕ → W2 := fun n ↦ fixedProfile n
  obtain ⟨sample, hsample⟩ := hindexStationary.nonempty
  have hsampleDomain : sample ∈ profileDomain := hindexSub hsample
  have hsampleCoordinate (n : ℕ) :
      spine (neighborEmbedding ⟨sample, hsampleDomain⟩ n) =
        rawCenters n := by
    have hcoordinate :=
      congrArg Subtype.val (congrFun (hprofileConstant sample hsample) n)
    simpa only [profile, dif_pos hsampleDomain, rawCenters] using hcoordinate
  have hrawCentersInjective : Function.Injective rawCenters := by
    intro i j hij
    apply (neighborEmbedding ⟨sample, hsampleDomain⟩).injective
    apply Subtype.ext
    apply hspine.injective
    exact (hsampleCoordinate i).trans (hij.trans (hsampleCoordinate j).symm)
  have hrawCenterMem (n : ℕ) : rawCenters n ∈ base :=
    (fixedProfile n).property
  have hrawCross (n : ℕ) (b : W2) (hb : b ∈ indexFiber) :
      rawCenters n < spine b ∧ red.Adj (rawCenters n) (spine b) := by
    have hbDomain : b ∈ profileDomain := hindexSub hb
    have hcoordinate :
        spine (neighborEmbedding ⟨b, hbDomain⟩ n) = rawCenters n := by
      have heq :=
        congrArg Subtype.val (congrFun (hprofileConstant b hb) n)
      simpa only [profile, dif_pos hbDomain, rawCenters] using heq
    have hneighbor := (neighborEmbedding ⟨b, hbDomain⟩ n).property
    refine ⟨?_, ?_⟩
    · rw [← hcoordinate]
      exact (hanchorMax _ hneighbor.1).trans_lt
        (hspine (hinitialTail hbDomain.1.1))
    · rw [← hcoordinate]
      exact hneighbor.2
  obtain ⟨subseq, hsubseqMonotone⟩ :=
    wellQuasiOrdered_le.exists_monotone_subseq rawCenters
  let centers : ℕ → W2 := fun n ↦ rawCenters (subseq n)
  have hcentersStrict : StrictMono centers := by
    intro i j hij
    have hle : centers i ≤ centers j :=
      hsubseqMonotone i j hij.le
    exact lt_of_le_of_ne hle fun heq ↦ by
      have hrawEq : (subseq i : ℕ) = subseq j :=
        hrawCentersInjective heq
      exact hij.ne (subseq.injective hrawEq)
  have hcentersType : typeLT (Set.range centers) = ω :=
    typeLT_range_eq_omega_of_strictMono centers hcentersStrict
  have hcentersMem (n : ℕ) : centers n ∈ base :=
    hrawCenterMem (subseq n)
  have hcentersBlue : blue.IsClique (Set.range centers) :=
    hbaseBlue.subset (by
      rintro _ ⟨n, rfl⟩
      exact hcentersMem n)
  refine ⟨centers, indexFiber, hcentersStrict, hcentersType,
    hcentersMem, hcentersBlue, hindexStationary, hindexCard,
    hindexType, ?_, ?_⟩
  · intro b hb
    have hbDomain : b ∈ profileDomain := hindexSub hb
    exact ⟨hbDomain.1.1, hbDomain.2⟩
  · intro n b hb
    exact hrawCross (subseq n) b hb

/-- A blue base sequence of exact type `ω` and the previously frozen
homogeneous countable arm-predecessor sequence are simultaneously
red-joined to one stationary `ω₂` spine fiber.  Its spine image retains a
blue fan of exact type `ω₁ + 1`. -/
def StationaryOmegaBaseStarWithCountablePredecessors
    (red blue : SimpleGraph W2) : Prop :=
  ∃ (spine : W2 → W2) (base : Set W2) (anchor : W2)
      (omegaCenters : ℕ → W2) (centerArms : ℕ → Set W2)
      (armCenters : ℕ → W2)
      (indexFiber representativeFiber fan : Set W2),
    StrictMono spine ∧ typeLT (Set.range spine) = ω_ 2 ∧
    base ⊆ Set.range spine ∧ blue.IsClique base ∧
    typeLT base = ω_ 1 + 1 ∧ spine anchor ∈ base ∧
    (∀ y ∈ base, y ≤ spine anchor) ∧
    StrictMono omegaCenters ∧ typeLT (Set.range omegaCenters) = ω ∧
    (∀ n, omegaCenters n ∈ base) ∧
    blue.IsClique (Set.range omegaCenters) ∧
    (∀ n, blue.IsClique (centerArms n) ∧
      typeLT (centerArms n) = ω_ 1 + 1) ∧
    (∀ n, armCenters n ∈ centerArms n) ∧
    (∀ i j, i < j → ∀ x ∈ centerArms i,
      ∀ y ∈ centerArms j, x < y) ∧
    StrictMono armCenters ∧ typeLT (Set.range armCenters) = ω ∧
    (red.IsClique (Set.range armCenters) ∨
      blue.IsClique (Set.range armCenters)) ∧
    IsStationary indexFiber ∧ #indexFiber = ℵ_ 2 ∧
    typeLT indexFiber = ω_ 2 ∧
    indexFiber ⊆ Set.Ioi anchor ∩ Set.Ioi omegaOneCutoff ∧
    representativeFiber = spine '' indexFiber ∧
    #representativeFiber = ℵ_ 2 ∧
    typeLT representativeFiber = ω_ 2 ∧
    fan ⊆ representativeFiber ∧ blue.IsClique fan ∧
    typeLT fan = ω_ 1 + 1 ∧
    (∀ n, ∀ b ∈ indexFiber,
      omegaCenters n < spine b ∧
        red.Adj (omegaCenters n) (spine b)) ∧
    ∀ n, ∀ b ∈ indexFiber,
      armCenters n < spine b ∧ red.Adj (armCenters n) (spine b)

/-- Upgrade a combined stationary fan to a single common stationary fiber
for countably infinitely many blue base centers, while retaining the
original countable homogeneous arm-predecessor tuple. -/
theorem StationaryCombinedSpinalFan.to_omegaBaseStarWithCountablePredecessors
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (hcombined : StationaryCombinedSpinalFan red blue) :
    StationaryOmegaBaseStarWithCountablePredecessors red blue := by
  classical
  obtain ⟨spine, base, anchor, _baseCenter, centerArms, armCenters,
      initialFiber, _initialRepresentativeFiber, _initialFan,
      hspine, hspineType, hbaseSub, hbaseBlue, hbaseType,
      hanchorMem, hanchorMax, _hbaseCenterMem, hcenterArms,
      harmCentersMem, hcenterArmsOrdered, harmCentersStrict,
      harmCentersType, harmCentersHomogeneous, hinitialStationary,
      _hinitialCard, _hinitialType, hinitialTail,
      _hinitialRepresentativeEq, _hinitialRepresentativeCard,
      _hinitialRepresentativeType, _hinitialFanSub, _hinitialFanBlue,
      _hinitialFanType, _hbaseCenterCross, harmCentersCross⟩ := hcombined
  obtain ⟨omegaCenters, indexFiber, homegaCentersStrict,
      homegaCentersType, homegaCentersMem, homegaCentersBlue,
      hindexStationary, hindexCard, hindexType, hindexSub,
      homegaCentersCross⟩ :=
    exists_stationary_omega_base_star hCH red blue hcompl spine hspine
      hbaseSub hanchorMem hanchorMax hbaseBlue hbaseType hnoRed hnoBlue
      hinitialStationary (fun _ hb ↦ (hinitialTail hb).1)
  have hindexTail :
      indexFiber ⊆ Set.Ioi anchor ∩ Set.Ioi omegaOneCutoff := by
    intro b hb
    exact ⟨(hinitialTail (hindexSub hb).1).1, (hindexSub hb).2⟩
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
  · refine ⟨spine, base, anchor, omegaCenters, centerArms, armCenters,
      indexFiber, representativeFiber, fan, hspine, hspineType,
      hbaseSub, hbaseBlue, hbaseType, hanchorMem, hanchorMax,
      homegaCentersStrict, homegaCentersType, homegaCentersMem,
      homegaCentersBlue, hcenterArms, harmCentersMem,
      hcenterArmsOrdered, harmCentersStrict, harmCentersType,
      harmCentersHomogeneous, hindexStationary, hindexCard, hindexType,
      hindexTail, rfl, hrepresentativeCard, hrepresentativeType,
      hfanSub, hfanBlue, hfanType, homegaCentersCross, ?_⟩
    intro n b hb
    exact harmCentersCross n b (hindexSub hb).1

/-- Global exact-target-or-stationary-`ω`-base-star normal form under CH.
-/
theorem part3_exact_or_stationaryOmegaBaseStarWithCountablePredecessors
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      StationaryOmegaBaseStarWithCountablePredecessors red blue := by
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
        StationaryCombinedSpinalFan.to_omegaBaseStarWithCountablePredecessors
          hCH red blue hcompl hnone.1 hnone.2 hcombined

end Erdos1172Part3StationaryOmegaStars
