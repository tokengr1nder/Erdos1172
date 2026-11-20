/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3StationaryOmegaStars
public import Erdos1172.Part3OmegaOneProfileBarrier

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3OmegaOneNeighborProfiles

open Erdos1172Part3Failure Erdos1172Part3StationaryOmegaStars
  Erdos1172Part3OmegaOneProfileBarrier

/-- The exact profile threshold for the red neighbourhoods of a blue
`omegaOne + 1` spine base.  Every point in a stationary `omegaTwo` tail
has `alephOne` many red predecessors in the base.  The complete
neighbourhood map either has a constant `alephTwo` fiber or is injective
on an `alephTwo` residual. -/
def StationaryOmegaOneBaseNeighborProfileBarrier
    (red blue : SimpleGraph W2) : Prop :=
  ∃ (spine : W2 → W2) (base : Set W2) (anchor : W2)
      (domain : Set W2),
    StrictMono spine ∧ typeLT (Set.range spine) = ω_ 2 ∧
    base ⊆ Set.range spine ∧ blue.IsClique base ∧
    typeLT base = ω_ 1 + 1 ∧ spine anchor ∈ base ∧
    (∀ y ∈ base, y ≤ spine anchor) ∧
    IsStationary domain ∧ #domain = ℵ_ 2 ∧
    typeLT domain = ω_ 2 ∧ domain ⊆ Set.Ioi anchor ∧
    (∀ b ∈ domain,
      #(baseRedNeighborIndices red spine base b) = ℵ_ 1) ∧
    ((∃ (fixed : Set W2) (fiber : Set domain),
        #fixed = ℵ_ 1 ∧ #fiber = ℵ_ 2 ∧
        ∀ b ∈ fiber,
          baseRedNeighborIndices red spine base b = fixed) ∨
      ∃ residual : Set domain,
        #residual = ℵ_ 2 ∧
        Set.InjOn
          (fun b : domain ↦
            baseRedNeighborIndices red spine base b)
          residual)

/-- Any stationary tail on which every base-neighbourhood has cardinal
`alephOne` satisfies the full-size constant-fiber/injective-residual
dichotomy. -/
theorem stationaryOmegaOneBaseNeighborProfileBarrier_of_domain
    (red blue : SimpleGraph W2)
    (spine : W2 → W2) (hspine : StrictMono spine)
    (hspineType : typeLT (Set.range spine) = ω_ 2)
    {base : Set W2} (hbaseSub : base ⊆ Set.range spine)
    {anchor : W2} (hanchorMem : spine anchor ∈ base)
    (hanchorMax : ∀ y ∈ base, y ≤ spine anchor)
    (hbaseBlue : blue.IsClique base)
    (hbaseType : typeLT base = ω_ 1 + 1)
    {domain : Set W2} (hdomainStationary : IsStationary domain)
    (hdomainCard : #domain = ℵ_ 2)
    (hdomainType : typeLT domain = ω_ 2)
    (hdomainTail : domain ⊆ Set.Ioi anchor)
    (hneighbourCard : ∀ b ∈ domain,
      #(baseRedNeighborIndices red spine base b) = ℵ_ 1) :
    StationaryOmegaOneBaseNeighborProfileBarrier red blue := by
  classical
  let profile : domain → Set W2 := fun b ↦
    baseRedNeighborIndices red spine base b
  obtain ⟨fixed, hfixedFiberCard⟩ |
      ⟨residual, hresidualCard, hresidualInjective⟩ :=
    alephTwo_fiber_or_alephTwo_injective_restriction
      hdomainCard profile
  · have hfiberNonempty : (profile ⁻¹' {fixed}).Nonempty := by
      apply Cardinal.mk_set_ne_zero_iff.mp
      rw [hfixedFiberCard]
      exact (Cardinal.aleph_pos 2).ne'
    obtain ⟨sample, hsample⟩ := hfiberNonempty
    have hsampleEq : profile sample = fixed := by
      simpa only [mem_preimage, mem_singleton_iff] using hsample
    have hfixedCard : #fixed = ℵ_ 1 := by
      rw [← hsampleEq]
      exact hneighbourCard sample sample.property
    refine ⟨spine, base, anchor, domain, hspine, hspineType,
      hbaseSub, hbaseBlue, hbaseType, hanchorMem, hanchorMax,
      hdomainStationary, hdomainCard, hdomainType, hdomainTail,
      hneighbourCard, Or.inl ⟨fixed, profile ⁻¹' {fixed},
        hfixedCard, hfixedFiberCard, ?_⟩⟩
    intro b hb
    simpa only [profile, mem_preimage, mem_singleton_iff] using hb
  · refine ⟨spine, base, anchor, domain, hspine, hspineType,
      hbaseSub, hbaseBlue, hbaseType, hanchorMem, hanchorMax,
      hdomainStationary, hdomainCard, hdomainType, hdomainTail,
      hneighbourCard, Or.inr ⟨residual, hresidualCard, ?_⟩⟩
    simpa only [profile] using hresidualInjective

/-- The constant-profile side of the barrier contains an exact blue
`omegaOne` set of base vertices completely red-joined, in increasing
order, to an exact `omegaTwo` set of spine vertices. -/
def HasOmegaOneByOmegaTwoRedRectangle
    (red blue : SimpleGraph W2) : Prop :=
  ∃ (left right : Set W2),
    blue.IsClique left ∧ typeLT left = ω_ 1 ∧
    typeLT right = ω_ 2 ∧
    (∀ x ∈ left, ∀ y ∈ right, x < y) ∧
    ∀ x ∈ left, ∀ y ∈ right, red.Adj x y

/-- A constant `alephTwo` neighbourhood fiber yields the exact
`omegaOne`-by-`omegaTwo` red rectangle. -/
theorem omegaOneByOmegaTwoRedRectangle_of_constantProfile
    {red blue : SimpleGraph W2}
    (hconstant : ∃ (spine : W2 → W2) (base : Set W2) (anchor : W2)
        (domain : Set W2) (fixed : Set W2) (fiber : Set domain),
      StrictMono spine ∧ base ⊆ Set.range spine ∧
      blue.IsClique base ∧ typeLT base = ω_ 1 + 1 ∧
      spine anchor ∈ base ∧ (∀ y ∈ base, y ≤ spine anchor) ∧
      domain ⊆ Set.Ioi anchor ∧ #fixed = ℵ_ 1 ∧ #fiber = ℵ_ 2 ∧
      ∀ b ∈ fiber,
        baseRedNeighborIndices red spine base b = fixed) :
    HasOmegaOneByOmegaTwoRedRectangle red blue := by
  classical
  obtain ⟨spine, base, anchor, domain, fixed, fiber,
    hspine, hbaseSub, hbaseBlue, hbaseType, hanchorMem,
    hanchorMax, hdomainTail, hfixedCard, hfiberCard,
    hprofileConstant⟩ := hconstant
  have hfixedSub : fixed ⊆ {a | spine a ∈ base} := by
    obtain ⟨sample, hsample⟩ : fiber.Nonempty := by
      apply Cardinal.mk_set_ne_zero_iff.mp
      rw [hfiberCard]
      exact (Cardinal.aleph_pos 2).ne'
    intro a ha
    have ha' : a ∈ baseRedNeighborIndices red spine base sample := by
      rw [hprofileConstant sample hsample]
      exact ha
    exact ha'.1
  let rawLeft : Set W2 := spine '' fixed
  have hrawLeftCard : #rawLeft = ℵ_ 1 := by
    calc
      #rawLeft = #fixed := Cardinal.mk_image_eq hspine.injective
      _ = ℵ_ 1 := hfixedCard
  have homegaOneLeRawLeft :
      (ω_ 1 : Ordinal.{0}) ≤ typeLT rawLeft := by
    simpa only [hrawLeftCard, Cardinal.ord_aleph] using
      (Cardinal.ord_le_type ((· < ·) : rawLeft → rawLeft → Prop))
  obtain ⟨left, hleftSub, hleftType⟩ :=
    Ordinal.exists_subset_typeLT_eq rawLeft homegaOneLeRawLeft
  let rawRightIndices : Set W2 := Subtype.val '' fiber
  have hrawRightIndicesCard : #rawRightIndices = ℵ_ 2 := by
    calc
      #rawRightIndices = #fiber :=
        Cardinal.mk_image_eq Subtype.val_injective
      _ = ℵ_ 2 := hfiberCard
  let right : Set W2 := spine '' rawRightIndices
  have hrightCard : #right = ℵ_ 2 := by
    calc
      #right = #rawRightIndices := Cardinal.mk_image_eq hspine.injective
      _ = ℵ_ 2 := hrawRightIndicesCard
  have hrightType : typeLT right = ω_ 2 :=
    typeLT_eq_omegaTwo_of_mk_eq hrightCard
  have hleftBase : left ⊆ base := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hleftSub hx
    exact hfixedSub ha
  have hleftBlue : blue.IsClique left :=
    hbaseBlue.subset hleftBase
  refine ⟨left, right, hleftBlue, hleftType, hrightType, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨b, hb, rfl⟩ := hy
    obtain ⟨b', hb', rfl⟩ := hb
    exact (hanchorMax x (hleftBase hx)).trans_lt
      (hspine (hdomainTail b'.property))
  · intro x hx y hy
    obtain ⟨a, ha, hax⟩ := hleftSub hx
    obtain ⟨b, hb, rfl⟩ := hy
    obtain ⟨b', hb', rfl⟩ := hb
    have haFixed : a ∈ fixed := ha
    have haNeighbor :
        a ∈ baseRedNeighborIndices red spine base b' := by
      rw [hprofileConstant b' hb']
      exact haFixed
    rw [← hax]
    exact haNeighbor.2

/-- Every stationary `omegaOne`-neighbourhood barrier already contains
the exact red rectangle, or its neighbourhood map stays injective on an
`alephTwo` residual. -/
theorem StationaryOmegaOneBaseNeighborProfileBarrier.rectangle_or_injective
    {red blue : SimpleGraph W2}
    (h : StationaryOmegaOneBaseNeighborProfileBarrier red blue) :
    HasOmegaOneByOmegaTwoRedRectangle red blue ∨
      ∃ (spine : W2 → W2) (base : Set W2) (domain : Set W2)
          (residual : Set domain),
        #residual = ℵ_ 2 ∧
        Set.InjOn
          (fun b : domain ↦
            baseRedNeighborIndices red spine base b)
          residual := by
  rcases h with ⟨spine, base, anchor, domain, hspine, hspineType,
    hbaseSub, hbaseBlue, hbaseType, hanchorMem, hanchorMax,
    hdomainStationary, hdomainCard, hdomainType, hdomainTail,
    hneighbourCard, hconstant | hinjective⟩
  · left
    apply omegaOneByOmegaTwoRedRectangle_of_constantProfile
      (red := red) (blue := blue)
    obtain ⟨fixed, fiber, hfixedCard, hfiberCard,
      hprofileConstant⟩ := hconstant
    exact ⟨spine, base, anchor, domain, fixed, fiber,
      hspine, hbaseSub, hbaseBlue, hbaseType, hanchorMem,
      hanchorMax, hdomainTail, hfixedCard, hfiberCard,
      hprofileConstant⟩
  · right
    obtain ⟨residual, hresidualCard, hresidualInjective⟩ := hinjective
    exact ⟨spine, base, domain, residual,
      hresidualCard, hresidualInjective⟩

end Erdos1172Part3OmegaOneNeighborProfiles
