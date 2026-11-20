/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3StationaryOmegaOneStars
public import Erdos1172.Part3OmegaOneNeighborProfiles

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3OmegaOneNeighborProfileBridge

open Erdos1172Part3Failure Erdos1172Part3StationaryOmegaStars
  Erdos1172Part3StationaryOmegaOneStars
  Erdos1172Part3StationaryCountablePredecessors
  Erdos1172Part3OmegaOneProfileBarrier
  Erdos1172Part3OmegaOneNeighborProfiles

/-- Passing through a strictly increasing spine identifies the red
neighbour indices of a base with the red neighbours viewed as base
vertices, so the two sets have the same cardinality. -/
theorem mk_baseRedNeighborIndices_eq_alephOne
    (red : SimpleGraph W2) (spine : W2 → W2)
    (hspine : StrictMono spine) {base : Set W2}
    (hbaseSub : base ⊆ Set.range spine) (b : W2)
    (hneighbours : #(baseRedNeighbors red base (spine b)) = ℵ_ 1) :
    #(baseRedNeighborIndices red spine base b) = ℵ_ 1 := by
  classical
  have himageEq :
      spine '' baseRedNeighborIndices red spine base b =
        Subtype.val '' baseRedNeighbors red base (spine b) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨spine a, ha.1⟩, ha.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨a, ha⟩ := hbaseSub y.property
      refine ⟨a, ?_, ha⟩
      exact ⟨ha ▸ y.property, ha ▸ hy⟩
  calc
    #(baseRedNeighborIndices red spine base b) =
        #(spine '' baseRedNeighborIndices red spine base b) :=
      (Cardinal.mk_image_eq hspine.injective).symm
    _ = #(Subtype.val '' baseRedNeighbors red base (spine b)) :=
      by rw [himageEq]
    _ = #(baseRedNeighbors red base (spine b)) :=
      Cardinal.mk_image_eq Subtype.val_injective
    _ = ℵ_ 1 := hneighbours

/-- The stationary full-base-red-degree pattern realizes the exact
neighbourhood-profile barrier. -/
theorem StationaryOmegaOneBaseRedDegreeWithCountablePredecessors.to_neighborProfileBarrier
    {red blue : SimpleGraph W2}
    (h : StationaryOmegaOneBaseRedDegreeWithCountablePredecessors
      red blue) :
    StationaryOmegaOneBaseNeighborProfileBarrier red blue := by
  obtain ⟨spine, base, anchor, _baseCenter, _centerArms, _armCenters,
    indexFiber, _representativeFiber, _fan, hspine, hspineType,
    hbaseSub, hbaseBlue, hbaseType, hanchorMem, hanchorMax,
    _hbaseCenterMem, _hcenterArms, _harmCentersMem,
    _hcenterArmsOrdered, _harmCentersStrict, _harmCentersType,
    _harmCentersHomogeneous, hindexStationary, hindexCard,
    hindexType, hindexTail, hneighborCard, _hrepresentativeEq,
    _hrepresentativeCard, _hrepresentativeType, _hfanSub,
    _hfanBlue, _hfanType, _hbaseCenterCross,
    _harmCentersCross⟩ := h
  apply stationaryOmegaOneBaseNeighborProfileBarrier_of_domain
    red blue spine hspine hspineType hbaseSub hanchorMem hanchorMax
      hbaseBlue hbaseType hindexStationary hindexCard hindexType
      (fun b hb ↦ (hindexTail hb).1)
  intro b hb
  exact mk_baseRedNeighborIndices_eq_alephOne red spine hspine
    hbaseSub b (hneighborCard b hb)

/-- The injective side of the full-neighbourhood profile dichotomy,
retaining the stationary blue fan and the complete countable homogeneous
arm-predecessor data from the source pattern. -/
def StationaryInjectiveOmegaOneBaseNeighborhoodResidualWithFan
    (red blue : SimpleGraph W2) : Prop :=
  ∃ (spine : W2 → W2) (base : Set W2) (anchor baseCenter : W2)
      (centerArms : ℕ → Set W2) (armCenters : ℕ → W2)
      (indexFiber representativeFiber fan : Set W2)
      (residual : Set indexFiber),
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
      #(baseRedNeighborIndices red spine base b) = ℵ_ 1) ∧
    representativeFiber = spine '' indexFiber ∧
    #representativeFiber = ℵ_ 2 ∧
    typeLT representativeFiber = ω_ 2 ∧
    fan ⊆ representativeFiber ∧ blue.IsClique fan ∧
    typeLT fan = ω_ 1 + 1 ∧
    (∀ b ∈ indexFiber,
      baseCenter < spine b ∧ red.Adj baseCenter (spine b)) ∧
    (∀ n, ∀ b ∈ indexFiber,
      armCenters n < spine b ∧ red.Adj (armCenters n) (spine b)) ∧
    #residual = ℵ_ 2 ∧
    Set.InjOn
      (fun b : indexFiber ↦
        baseRedNeighborIndices red spine base b)
      residual

/-- The stationary full-degree pattern has exactly the expected sharp
split: a common exact `omegaOne` red neighbourhood on `omegaTwo` many
later points, or `alephTwo` pairwise distinct complete neighbourhoods.
The latter branch retains every inherited fan and arm-center field. -/
theorem StationaryOmegaOneBaseRedDegreeWithCountablePredecessors.rectangle_or_injectiveResidual
    {red blue : SimpleGraph W2}
    (h : StationaryOmegaOneBaseRedDegreeWithCountablePredecessors
      red blue) :
    HasOmegaOneByOmegaTwoRedRectangle red blue ∨
      StationaryInjectiveOmegaOneBaseNeighborhoodResidualWithFan
        red blue := by
  classical
  obtain ⟨spine, base, anchor, baseCenter, centerArms, armCenters,
    indexFiber, representativeFiber, fan, hspine, hspineType,
    hbaseSub, hbaseBlue, hbaseType, hanchorMem, hanchorMax,
    hbaseCenterMem, hcenterArms, harmCentersMem,
    hcenterArmsOrdered, harmCentersStrict, harmCentersType,
    harmCentersHomogeneous, hindexStationary, hindexCard,
    hindexType, hindexTail, hneighborVertexCard,
    hrepresentativeEq, hrepresentativeCard, hrepresentativeType,
    hfanSub, hfanBlue, hfanType, hbaseCenterCross,
    harmCentersCross⟩ := h
  have hneighborIndexCard (b : W2) (hb : b ∈ indexFiber) :
      #(baseRedNeighborIndices red spine base b) = ℵ_ 1 :=
    mk_baseRedNeighborIndices_eq_alephOne red spine hspine hbaseSub b
      (hneighborVertexCard b hb)
  let profile : indexFiber → Set W2 := fun b ↦
    baseRedNeighborIndices red spine base b
  obtain ⟨fixed, hfixedFiberCard⟩ |
      ⟨residual, hresidualCard, hresidualInjective⟩ :=
    alephTwo_fiber_or_alephTwo_injective_restriction
      hindexCard profile
  · have hfiberNonempty : (profile ⁻¹' {fixed}).Nonempty := by
      apply Cardinal.mk_set_ne_zero_iff.mp
      rw [hfixedFiberCard]
      exact (Cardinal.aleph_pos 2).ne'
    obtain ⟨sample, hsample⟩ := hfiberNonempty
    have hsampleEq : profile sample = fixed := by
      simpa only [mem_preimage, mem_singleton_iff] using hsample
    have hfixedCard : #fixed = ℵ_ 1 := by
      rw [← hsampleEq]
      exact hneighborIndexCard sample sample.property
    left
    apply omegaOneByOmegaTwoRedRectangle_of_constantProfile
    exact ⟨spine, base, anchor, indexFiber, fixed,
      profile ⁻¹' {fixed}, hspine, hbaseSub, hbaseBlue, hbaseType,
      hanchorMem, hanchorMax, (fun b hb ↦ (hindexTail hb).1),
      hfixedCard, hfixedFiberCard, fun b hb ↦ by
        simpa only [profile, mem_preimage, mem_singleton_iff] using hb⟩
  · right
    exact ⟨spine, base, anchor, baseCenter, centerArms, armCenters,
      indexFiber, representativeFiber, fan, residual, hspine,
      hspineType, hbaseSub, hbaseBlue, hbaseType, hanchorMem,
      hanchorMax, hbaseCenterMem, hcenterArms, harmCentersMem,
      hcenterArmsOrdered, harmCentersStrict, harmCentersType,
      harmCentersHomogeneous, hindexStationary, hindexCard,
      hindexType, hindexTail, hneighborIndexCard,
      hrepresentativeEq, hrepresentativeCard, hrepresentativeType,
      hfanSub, hfanBlue, hfanType, hbaseCenterCross,
      harmCentersCross, hresidualCard, by
        simpa only [profile] using hresidualInjective⟩

/-- Global CH normal form at the exact full-neighbourhood threshold:
either one Part 3 target exists, an exact blue-`omegaOne` by
blue-`omegaTwo` complete-red rectangle exists, or the counterexample
carries `alephTwo` distinct full base-neighbourhoods together with its
stationary fan and countable predecessor system. -/
theorem part3_exact_or_omegaOneByOmegaTwoRedRectangle_or_injectiveNeighborhoodResidual
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red
        Erdos1172Part3FiniteStars.RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      HasOmegaOneByOmegaTwoRedRectangle red blue ∨
      StationaryInjectiveOmegaOneBaseNeighborhoodResidualWithFan
        red blue := by
  obtain htarget | hdegree :=
    part3_exact_or_stationaryOmegaOneBaseRedDegreeWithCountablePredecessors
      hCH red blue hcompl
  · exact Or.inl htarget
  · obtain hrectangle | hresidual :=
      StationaryOmegaOneBaseRedDegreeWithCountablePredecessors.rectangle_or_injectiveResidual
        hdegree
    · exact Or.inr (Or.inl hrectangle)
    · exact Or.inr (Or.inr hresidual)

end Erdos1172Part3OmegaOneNeighborProfileBridge
