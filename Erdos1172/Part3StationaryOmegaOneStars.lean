/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3StationaryOmegaStars

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3StationaryOmegaOneStars

open Erdos1172Part3Failure Erdos1172Part3FiniteStars
  Erdos1172Part3StationaryCountablePredecessors
  Erdos1172Part3StationaryCombinedFan
  Erdos1172Part3StationaryFiniteStars
  Erdos1172Part3StationaryOmegaStars

/-- Red neighbours of `x` viewed as a subset of a prescribed base. -/
def baseRedNeighbors (red : SimpleGraph W2) (base : Set W2)
    (x : W2) : Set base :=
  {y | red.Adj y x}

/-- Removing a countable set from an `ℵ₁`-sized set preserves cardinality
`ℵ₁`. -/
theorem mk_sdiff_eq_alephOne_of_countable {s t : Set W2}
    (hs : #s = ℵ_ 1) (ht : t.Countable) :
    #(s \ t : Set W2) = ℵ_ 1 := by
  have htlt : #t < ℵ_ 1 :=
    ht.le_aleph0.trans_lt Cardinal.aleph0_lt_aleph_one
  apply le_antisymm
  · simpa only [hs] using
      Cardinal.mk_le_mk_of_subset (Set.sdiff_subset : s \ t ⊆ s)
  · by_contra h
    have hdiff : #(s \ t : Set W2) < ℵ_ 1 := lt_of_not_ge h
    have hcover : ℵ_ 1 ≤ #(s \ t : Set W2) + #t := by
      simpa only [hs] using Cardinal.le_mk_sdiff_add_mk s t
    exact (not_lt_of_ge hcover)
      (Cardinal.add_lt_of_lt (Cardinal.aleph0_le_aleph 1) hdiff htlt)

/-- Under failure of both exact targets, stationarily many points of a
stationary later spine fiber have uncountably many red neighbours in the
blue `ω₁ + 1` base.  If countable degree held on a stationary remainder,
enumerate each complete neighbour set by `ℕ`, using the common red center
as default.  CH and Fodor freeze the enumeration, hence the entire
neighbour set, on a stationary fiber.  Removing that countable set leaves
a blue `ω₁` core, while a blue later pair extends it to the forbidden blue
`ω₁ + 2`. -/
theorem isStationary_uncountable_base_red_neighbors
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (spine : W2 → W2) (hspine : StrictMono spine)
    {base : Set W2} {anchor baseCenter : W2}
    (_hanchorMem : spine anchor ∈ base)
    (hanchorMax : ∀ y ∈ base, y ≤ spine anchor)
    (hbaseCenterMem : baseCenter ∈ base)
    (hbaseBlue : blue.IsClique base)
    (hbaseType : typeLT base = ω_ 1 + 1)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    {initialFiber : Set W2}
    (hinitialStationary : IsStationary initialFiber)
    (hinitialTail : initialFiber ⊆ Set.Ioi anchor)
    (hbaseCenterCross : ∀ b ∈ initialFiber,
      red.Adj baseCenter (spine b)) :
    IsStationary
      {b | b ∈ initialFiber ∧
        ¬ (baseRedNeighbors red base (spine b)).Countable} := by
  classical
  let uncountableFiber : Set W2 :=
    {b | b ∈ initialFiber ∧
      ¬ (baseRedNeighbors red base (spine b)).Countable}
  by_contra huncountableNonstationary
  have huncountableNonstationary' : ¬ IsStationary uncountableFiber := by
    simpa only [uncountableFiber] using huncountableNonstationary
  let countableFiber : Set W2 := initialFiber \ uncountableFiber
  have huncountableUnionCountable :
      uncountableFiber ∪ countableFiber = initialFiber := by
    ext b
    simp only [uncountableFiber, countableFiber, mem_union,
      mem_ofPred_eq, mem_sdiff]
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
  have hcountableFiberStationary : IsStationary countableFiber := by
    have hunionStationary :
        IsStationary (uncountableFiber ∪ countableFiber) := by
      simpa only [huncountableUnionCountable] using hinitialStationary
    rcases (isStationary_union_iff hcof).mp hunionStationary with
      huncountable | hcountable
    · exact (huncountableNonstationary' huncountable).elim
    · exact hcountable
  let profileDomain : Set W2 :=
    {b | b ∈ countableFiber ∧ omegaOneCutoff < b}
  have hprofileDomainStationary : IsStationary profileDomain := by
    simpa only [profileDomain] using
      Erdos1172Part3StationaryCombinedFan.IsStationary.inter_Ioi_omegaTwo
        hcountableFiberStationary omegaOneCutoff
  have hprofileDomainTail : profileDomain ⊆ Set.Ioi omegaOneCutoff :=
    fun _ hb ↦ hb.2
  have hneighborCountable (b : profileDomain) :
      (baseRedNeighbors red base (spine b)).Countable := by
    by_contra hnotCountable
    exact b.property.1.2 ⟨b.property.1.1, hnotCountable⟩
  let defaultCenter : base := ⟨baseCenter, hbaseCenterMem⟩
  have hdefaultNeighbor (b : profileDomain) :
      defaultCenter ∈ baseRedNeighbors red base (spine b) :=
    hbaseCenterCross b b.property.1.1
  let enumeration (b : profileDomain) : ℕ → base :=
    Set.enumerateCountable (hneighborCountable b) defaultCenter
  let profile : W2 → ℕ → base := fun b ↦
    if hb : b ∈ profileDomain then enumeration ⟨b, hb⟩
    else fun _ ↦ defaultCenter
  have hbaseCard : #base = ℵ_ 1 := by
    have hc := congrArg Ordinal.card hbaseType
    simpa only [Ordinal.card_type, Cardinal.card_omega_one_add_one] using hc
  obtain ⟨fixedProfile, frozenFiber, hfrozenStationary, hfrozenCard,
      _hfrozenType, hfrozenSub, hprofileConstant⟩ :=
    exists_stationary_fiber_of_countable_alephOne_profile_on
      hCH (fun _ : ℕ ↦ base) (fun _ ↦ hbaseCard) profile
      hprofileDomainStationary hprofileDomainTail
  obtain ⟨sample, hsample⟩ := hfrozenStationary.nonempty
  have hsampleDomain : sample ∈ profileDomain := hfrozenSub hsample
  have hneighborConstant (b : W2) (hb : b ∈ frozenFiber) :
      baseRedNeighbors red base (spine b) =
        baseRedNeighbors red base (spine sample) := by
    have hbDomain : b ∈ profileDomain := hfrozenSub hb
    have henumerationEq :
        enumeration ⟨b, hbDomain⟩ =
          enumeration ⟨sample, hsampleDomain⟩ := by
      have hprofileEq :=
        (hprofileConstant b hb).trans
          (hprofileConstant sample hsample).symm
      simpa only [profile, dif_pos hbDomain, dif_pos hsampleDomain] using
        hprofileEq
    calc
      baseRedNeighbors red base (spine b) =
          Set.range (enumeration ⟨b, hbDomain⟩) :=
        (Set.range_enumerateCountable_of_mem
          (hneighborCountable ⟨b, hbDomain⟩)
          (hdefaultNeighbor ⟨b, hbDomain⟩)).symm
      _ = Set.range (enumeration ⟨sample, hsampleDomain⟩) :=
        congrArg Set.range henumerationEq
      _ = baseRedNeighbors red base (spine sample) :=
        Set.range_enumerateCountable_of_mem
          (hneighborCountable ⟨sample, hsampleDomain⟩)
          (hdefaultNeighbor ⟨sample, hsampleDomain⟩)
  let sampleNeighbors : Set base :=
    baseRedNeighbors red base (spine sample)
  let deletedVertices : Set W2 := Subtype.val '' sampleNeighbors
  have hdeletedCountable : deletedVertices.Countable := by
    exact (hneighborCountable ⟨sample, hsampleDomain⟩).image Subtype.val
  have hremainingCard : #(base \ deletedVertices : Set W2) = ℵ_ 1 :=
    mk_sdiff_eq_alephOne_of_countable hbaseCard hdeletedCountable
  have homegaOneLeRemaining :
      (ω_ 1 : Ordinal.{0}) ≤ typeLT (base \ deletedVertices : Set W2) := by
    simpa only [hremainingCard, Cardinal.ord_aleph] using
      (Cardinal.ord_le_type ((· < ·) :
        ((base \ deletedVertices : Set W2)) →
          ((base \ deletedVertices : Set W2)) → Prop))
  obtain ⟨core, hcoreSub, hcoreType⟩ :=
    Ordinal.exists_subset_typeLT_eq
      (base \ deletedVertices : Set W2) homegaOneLeRemaining
  have hcoreBlue : blue.IsClique core :=
    hbaseBlue.subset (hcoreSub.trans Set.sdiff_subset)
  let representativeFiber : Set W2 := spine '' frozenFiber
  have hrepresentativeCard : #representativeFiber = ℵ_ 2 := by
    calc
      #representativeFiber = #frozenFiber :=
        Cardinal.mk_image_eq hspine.injective
      _ = ℵ_ 2 := hfrozenCard
  obtain ⟨later, hlaterSub, hlaterBlue, hlaterType⟩ :=
    exists_blue_omega_add_one_in_every_alephTwo_set
      red blue hcompl hnoRed hrepresentativeCard
  have htwo : (2 : Ordinal.{0}) ≤ ω + 1 :=
    (Ordinal.natCast_lt_omega0 2).le.trans le_self_add
  obtain ⟨pair, hpairSub, hpairType⟩ :=
    Ordinal.exists_subset_typeLT_eq later (hlaterType ▸ htwo)
  have hpairBlue : blue.IsClique pair := hlaterBlue.subset hpairSub
  have hpairRepresentative : pair ⊆ representativeFiber :=
    hpairSub.trans hlaterSub
  have hcross : ∀ x ∈ core, ∀ y ∈ pair, blue.Adj x y := by
    intro x hx y hy
    have hxRemaining := hcoreSub hx
    obtain ⟨b, hb, hby⟩ := hpairRepresentative hy
    have hnotRed : ¬ red.Adj x y := by
      intro hred
      apply hxRemaining.2
      refine ⟨⟨x, hxRemaining.1⟩, ?_, rfl⟩
      have hxNeighbor :
          (⟨x, hxRemaining.1⟩ : base) ∈
            baseRedNeighbors red base (spine b) := by
        exact hby.symm ▸ hred
      rw [hneighborConstant b hb] at hxNeighbor
      exact hxNeighbor
    rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
    refine ⟨?_, hnotRed⟩
    have hxy : x < y :=
      ((hanchorMax x hxRemaining.1).trans_lt
        (hspine (hinitialTail (hfrozenSub hb).1.1))).trans_eq hby
    exact ne_of_lt hxy
  have hlaterOrder : ∀ x ∈ core, ∀ y ∈ pair, x < y := by
    intro x hx y hy
    have hxRemaining := hcoreSub hx
    obtain ⟨b, hb, rfl⟩ := hpairRepresentative hy
    exact (hanchorMax x hxRemaining.1).trans_lt
      (hspine (hinitialTail (hfrozenSub hb).1.1))
  exact hnoBlue <| blue.exists_clique_type_add_of_later_block
    hcoreBlue hpairBlue hcoreType hpairType hlaterOrder hcross

/-- A stationary `ω₂` spine fiber on which every spine point has exactly
`ℵ₁` red neighbours in one blue `ω₁ + 1` base.  The combined fan's
countable homogeneous arm-predecessor tuple is retained on the same
fiber, whose image contains a blue fan of exact type `ω₁ + 1`. -/
def StationaryOmegaOneBaseRedDegreeWithCountablePredecessors
    (red blue : SimpleGraph W2) : Prop :=
  ∃ (spine : W2 → W2) (base : Set W2) (anchor baseCenter : W2)
      (centerArms : ℕ → Set W2) (armCenters : ℕ → W2)
      (indexFiber representativeFiber fan : Set W2),
    StrictMono spine ∧ typeLT (Set.range spine) = ω_ 2 ∧
    base ⊆ Set.range spine ∧ blue.IsClique base ∧
    typeLT base = ω_ 1 + 1 ∧ spine anchor ∈ base ∧
    (∀ y ∈ base, y ≤ spine anchor) ∧ baseCenter ∈ base ∧
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
    (∀ b ∈ indexFiber,
      #(baseRedNeighbors red base (spine b)) = ℵ_ 1) ∧
    representativeFiber = spine '' indexFiber ∧
    #representativeFiber = ℵ_ 2 ∧
    typeLT representativeFiber = ω_ 2 ∧
    fan ⊆ representativeFiber ∧ blue.IsClique fan ∧
    typeLT fan = ω_ 1 + 1 ∧
    (∀ b ∈ indexFiber,
      baseCenter < spine b ∧ red.Adj baseCenter (spine b)) ∧
    ∀ n, ∀ b ∈ indexFiber,
      armCenters n < spine b ∧ red.Adj (armCenters n) (spine b)

/-- Refine a combined stationary fan to the stationary set of spine
points having full `ℵ₁` red degree into its blue base. -/
theorem StationaryCombinedSpinalFan.to_omegaOneBaseRedDegreeWithCountablePredecessors
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (hcombined : StationaryCombinedSpinalFan red blue) :
    StationaryOmegaOneBaseRedDegreeWithCountablePredecessors red blue := by
  classical
  obtain ⟨spine, base, anchor, baseCenter, centerArms, armCenters,
      initialFiber, _initialRepresentativeFiber, _initialFan,
      hspine, hspineType, hbaseSub, hbaseBlue, hbaseType,
      hanchorMem, hanchorMax, hbaseCenterMem, hcenterArms,
      harmCentersMem, hcenterArmsOrdered, harmCentersStrict,
      harmCentersType, harmCentersHomogeneous, hinitialStationary,
      _hinitialCard, _hinitialType, hinitialTail,
      _hinitialRepresentativeEq, _hinitialRepresentativeCard,
      _hinitialRepresentativeType, _hinitialFanSub, _hinitialFanBlue,
      _hinitialFanType, hbaseCenterCross, harmCentersCross⟩ := hcombined
  let indexFiber : Set W2 :=
    {b | b ∈ initialFiber ∧
      ¬ (baseRedNeighbors red base (spine b)).Countable}
  have hindexStationary : IsStationary indexFiber := by
    simpa only [indexFiber] using
      isStationary_uncountable_base_red_neighbors
        hCH red blue hcompl spine hspine hanchorMem hanchorMax
        hbaseCenterMem hbaseBlue hbaseType hnoRed hnoBlue
        hinitialStationary (fun _ hb ↦ (hinitialTail hb).1)
        (fun b hb ↦ (hbaseCenterCross b hb).2)
  have hindexCard : #indexFiber = ℵ_ 2 :=
    mk_eq_alephTwo_of_isStationary hindexStationary
  have hindexType : typeLT indexFiber = ω_ 2 :=
    typeLT_eq_omegaTwo_of_mk_eq hindexCard
  have hindexTail :
      indexFiber ⊆ Set.Ioi anchor ∩ Set.Ioi omegaOneCutoff := by
    intro b hb
    exact hinitialTail hb.1
  have hbaseCard : #base = ℵ_ 1 := by
    have hc := congrArg Ordinal.card hbaseType
    simpa only [Ordinal.card_type, Cardinal.card_omega_one_add_one] using hc
  have hneighborCard (b : W2) (hb : b ∈ indexFiber) :
      #(baseRedNeighbors red base (spine b)) = ℵ_ 1 := by
    apply le_antisymm
    · exact (Cardinal.mk_set_le
        (baseRedNeighbors red base (spine b))).trans_eq hbaseCard
    · apply Cardinal.aleph_one_le_iff.mpr
      apply lt_of_not_ge
      intro hle
      exact hb.2 (Cardinal.le_aleph0_iff_set_countable.mp hle)
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
  · refine ⟨spine, base, anchor, baseCenter, centerArms, armCenters,
      indexFiber, representativeFiber, fan, hspine, hspineType,
      hbaseSub, hbaseBlue, hbaseType, hanchorMem, hanchorMax,
      hbaseCenterMem, hcenterArms, harmCentersMem, hcenterArmsOrdered,
      harmCentersStrict, harmCentersType, harmCentersHomogeneous,
      hindexStationary, hindexCard, hindexType, hindexTail,
      hneighborCard, rfl, hrepresentativeCard, hrepresentativeType,
      hfanSub, hfanBlue, hfanType, ?_, ?_⟩
    · intro b hb
      exact hbaseCenterCross b hb.1
    · intro n b hb
      exact harmCentersCross n b hb.1

/-- Global exact-target-or-stationary-full-base-red-degree normal form
under CH. -/
theorem part3_exact_or_stationaryOmegaOneBaseRedDegreeWithCountablePredecessors
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      StationaryOmegaOneBaseRedDegreeWithCountablePredecessors red blue := by
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
        StationaryCombinedSpinalFan.to_omegaOneBaseRedDegreeWithCountablePredecessors
          hCH red blue hcompl hnone.1 hnone.2 hcombined

end Erdos1172Part3StationaryOmegaOneStars
