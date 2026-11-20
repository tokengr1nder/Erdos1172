/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3TransfiniteTransversal

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3TransfiniteSpinalFan

open Erdos1172Part3Failure Erdos1172Part3FiniteStars
  Erdos1172Part3TransfiniteTransversal

/-- A blue `ω₁ + 1` clique on a strictly increasing `ω₂` spine which
cannot be extended by one point has an `ℵ₂`-sized red failure fiber still
lying on the later part of that same spine. -/
theorem exists_large_red_failure_fiber_on_strict_spine
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (spine : W2 → W2) (hspine : StrictMono spine)
    {base : Set W2} (hbaseSub : base ⊆ Set.range spine)
    (hbase : blue.IsClique base) (hbaseType : typeLT base = ω_ 1 + 1)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) :
    ∃ (anchor : W2) (center : W2) (fiber : Set W2),
      spine anchor ∈ base ∧
      (∀ y ∈ base, y ≤ spine anchor) ∧ center ∈ base ∧
      #fiber = ℵ_ 2 ∧ fiber ⊆ Set.Ioi anchor ∧
      ∀ b ∈ fiber, red.Adj center (spine b) := by
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
    have hext := blue.exists_clique_type_add_one_of_common_later
      hbase hbaseType (hlater b) hblueAdj
    apply hnoBlue
    obtain ⟨t, ht, httype⟩ := hext
    refine ⟨t, ht, ?_⟩
    calc
      typeLT t = (ω_ 1 + 1) + 1 := httype
      _ = ω_ 1 + 2 := by norm_num [add_assoc]
  let failure : Set.Ioi anchor → base :=
    fun b ↦ Classical.choose (hwitness b)
  have hfailure (b : Set.Ioi anchor) :
      red.Adj (failure b) (spine b) :=
    Classical.choose_spec (hwitness b)
  have htailCard : #(Set.Ioi anchor) = ℵ_ 2 := mk_Ioi_omegaTwo_eq anchor
  have hbaseCard : #base = ℵ_ 1 := by
    have hc := congrArg Ordinal.card hbaseType
    simpa only [Ordinal.card_type, Cardinal.card_omega_one_add_one] using hc
  obtain ⟨center, hlargeFiber⟩ := Cardinal.infinite_pigeonhole failure
    (by rw [htailCard]; exact Cardinal.aleph0_le_aleph 2)
    (by
      rw [hbaseCard, htailCard]
      rw [show (ℵ_ 2 : Cardinal.{0}) = ℵ_ ((1 : Ordinal.{0}) + 1) by norm_num,
        (Cardinal.isRegular_aleph_add_one 1).cof_ord]
      exact Cardinal.aleph_lt_aleph.mpr (by norm_num))
  let fiber : Set W2 := Subtype.val '' (failure ⁻¹' {center})
  refine ⟨anchor, center, fiber, hanchorMem, hanchorMax,
    center.property, ?_, ?_, ?_⟩
  · calc
      #fiber = #(failure ⁻¹' {center}) :=
        Cardinal.mk_image_eq Subtype.val_injective
      _ = #(Set.Ioi anchor) := hlargeFiber
      _ = ℵ_ 2 := htailCard
  · rintro b ⟨z, hz, rfl⟩
    exact z.property
  · rintro b ⟨z, hz, rfl⟩
    have hzc : failure z = center := by
      simpa only [mem_preimage, mem_singleton_iff] using hz
    simpa only [hzc] using hfailure z

/-- The spinal-fan obstruction left after both exact targets fail.  The
center belongs to an earlier blue `ω₁ + 1` base, while a blue
`ω₁ + 1` clique of later spine points is completely red-joined to it.
The set of available later spine indices still has cardinality `ℵ₂`. -/
def OmegaTwoSpinalFan (red blue : SimpleGraph W2) : Prop :=
  ∃ (spine : W2 → W2) (base : Set W2) (anchor center : W2)
      (fiber fan : Set W2),
    StrictMono spine ∧ typeLT (Set.range spine) = ω_ 2 ∧
    base ⊆ Set.range spine ∧ blue.IsClique base ∧
    typeLT base = ω_ 1 + 1 ∧ spine anchor ∈ base ∧
    (∀ y ∈ base, y ≤ spine anchor) ∧ center ∈ base ∧
    #fiber = ℵ_ 2 ∧ fiber ⊆ Set.Ioi anchor ∧
    fan ⊆ spine '' fiber ∧ blue.IsClique fan ∧
    typeLT fan = ω_ 1 + 1 ∧
    ∀ x ∈ fan, spine anchor < x ∧ red.Adj center x

/-- A full transversal split yields the exact red target, or an
`ω₂` spinal fan. -/
theorem fullOmegaTwoTransversalSplit_redTarget_or_spinalFan
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (hsplit : FullOmegaTwoTransversalSplit red blue) :
    OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      OmegaTwoSpinalFan red blue := by
  classical
  obtain ⟨indexedArms, representatives, transversal,
    hrepresentativesStrict, hrepresentativesType, harms,
    hrepresentativeMem, hrepresentativeMax, htransversalSub,
    htransversalBlue, htransversalType, hcrossSplit⟩ := hsplit
  obtain ⟨anchor, center, fiber, hanchorMem, hanchorMax,
      hcenterMem, hfiberCard, hfiberTail, hredFiber⟩ :=
    exists_large_red_failure_fiber_on_strict_spine
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
    refine ⟨representatives, transversal, anchor, center, fiber, fan,
      hrepresentativesStrict, hrepresentativesType, htransversalSub,
      htransversalBlue, htransversalType, hanchorMem, hanchorMax,
      hcenterMem, hfiberCard, hfiberTail, hfanSub,
      hfanBlue, hfanType, ?_⟩
    intro x hx
    obtain ⟨b, hb, rfl⟩ := hfanSub hx
    exact ⟨hrepresentativesStrict (hfiberTail hb),
      hredFiber b hb⟩

/-- Global exact-target-or-spinal-fan normal form under CH. -/
theorem part3_exact_or_omegaTwoSpinalFan
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      OmegaTwoSpinalFan red blue := by
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
        fullOmegaTwoTransversalSplit_redTarget_or_spinalFan
          hCH red blue hcompl hnone.2 hsplit
      · exact (hnone.1 hred).elim
      · exact hfan

end Erdos1172Part3TransfiniteSpinalFan
