/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3TransfiniteTransversal
public import Erdos1172.Part3HomogeneousFailureLadder
public import Erdos1172.ForMathlib.SetTheory.Cardinal.GCHConsequences1172

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3TransversalPredecessorPattern

open Erdos1172Part3Failure Erdos1172Part3TransfiniteIncidence
  Erdos1172Part3TransfiniteTransversal
  Erdos1172Part3HomogeneousFailureLadder

/-- Generic countable dependent-profile concentration under CH.  If the
domain has cardinality `ℵ₂` and every coordinate type has cardinality
`ℵ₁`, then a profile in the countable dependent product repeats on an
`ℵ₂` fiber.  This is the reusable cardinal core of the predecessor
concentration argument. -/
theorem exists_alephTwo_fiber_of_countable_alephOne_profile
    (hCH : CH) {D : Type} (A : ℕ → Type)
    (hD : #D = ℵ_ 2) (hA : ∀ n, #(A n) = ℵ_ 1)
    (profile : D → ∀ n, A n) :
    ∃ fixedProfile, #(profile ⁻¹' {fixedProfile}) = ℵ_ 2 := by
  have hprofileCard : #(∀ n : ℕ, A n) ≤ ℵ_ 1 := by
    rw [Cardinal.mk_pi]
    calc
      Cardinal.prod (fun n : ℕ ↦ #(A n)) ≤
          Cardinal.prod (fun _ : ℕ ↦ (ℵ_ 1 : Cardinal.{0})) :=
        Cardinal.prod_le_prod _ _ (fun n ↦ (hA n).le)
      _ = (ℵ_ 1 : Cardinal.{0}) ^ #ℕ := Cardinal.prod_const' ℕ (ℵ_ 1)
      _ = (ℵ_ 1 : Cardinal.{0}) ^ ℵ₀ := by simp
      _ = ℵ_ 1 := hCH.aleph_one_power_aleph_zero
  obtain ⟨fixedProfile, hlargeFiber⟩ :=
    Cardinal.infinite_pigeonhole profile
      (by rw [hD]; exact Cardinal.aleph0_le_aleph 2)
      (by
        rw [hD]
        rw [show (ℵ_ 2 : Cardinal.{0}) =
            ℵ_ ((1 : Ordinal.{0}) + 1) by norm_num,
          (Cardinal.isRegular_aleph_add_one 1).cof_ord]
        exact hprofileCard.trans_lt
          (Cardinal.aleph_lt_aleph.mpr (by norm_num)))
  exact ⟨fixedProfile, hlargeFiber.trans hD⟩

/-- A countable family of fixed predecessors, one from each of countably
many ordered blue `ω₁ + 1` arms, which is simultaneously red-adjacent to
an `ℵ₂` fiber of later representatives.  The representatives retain a blue
transversal of type `ω₁ + 1`, and the predecessors can be thinned to an
exact-`ω` homogeneous sequence. -/
def CountablyConcentratedTransversalPredecessorPattern
    (red blue : SimpleGraph W2) : Prop :=
  ∃ (centerArms : ℕ → Set W2) (centers : ℕ → W2)
      (representativeFiber transversal : Set W2),
    (∀ n, blue.IsClique (centerArms n) ∧
      typeLT (centerArms n) = ω_ 1 + 1) ∧
    (∀ n, centers n ∈ centerArms n) ∧
    (∀ i j, i < j → ∀ x ∈ centerArms i,
      ∀ y ∈ centerArms j, x < y) ∧
    StrictMono centers ∧
    typeLT (Set.range centers) = ω ∧
    (red.IsClique (Set.range centers) ∨
      blue.IsClique (Set.range centers)) ∧
    #representativeFiber = ℵ_ 2 ∧
    typeLT representativeFiber = ω_ 2 ∧
    transversal ⊆ representativeFiber ∧
    blue.IsClique transversal ∧
    typeLT transversal = ω_ 1 + 1 ∧
    ∀ n, ∀ y ∈ representativeFiber,
      centers n < y ∧ red.Adj (centers n) y

/-- Under CH, the full `ω₂` incidence obstruction has a countable fixed
predecessor profile on an `ℵ₂` fiber of later representatives.  The key
cardinal calculation is `ℵ₁ ^ ℵ₀ = ℵ₁`, so one complete predecessor tuple
repeats on a full fiber.  The CH asymmetric theorem then thins that fiber
to a blue `ω₁ + 1` transversal unless the exact red target already occurs. -/
theorem fullOmegaTwoIncidence_redTarget_or_countablyConcentratedPattern
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (hobs : FullOmegaTwoIncidenceObstruction red blue) :
    OrdinalRamsey.HasCliqueOfType red
        Erdos1172Part3FiniteStars.RedTarget ∨
      CountablyConcentratedTransversalPredecessorPattern red blue := by
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
  let cutoff : W2 := Ordinal.ToType.mk ⟨ω, homegaLt⟩
  have hearlyPointLtCutoff (n : ℕ) :
      Ordinal.ToType.mk
          ⟨(n : Ordinal),
            (Ordinal.natCast_lt_omega0 n).trans homegaLt⟩ < cutoff := by
    apply Ordinal.ToType.mk.lt_iff_lt.mpr
    exact Ordinal.natCast_lt_omega0 n
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
  have hearlyBeforeTail (n : ℕ) (j : Set.Ioi cutoff) :
      early n < stage (j : W2) := by
    exact hstageStrict
      ((hearlyPointLtCutoff n).trans j.property)
  have hrepresentativeExists (a : W2) : ∃ x : arms (stage a), True := by
    obtain ⟨m, -⟩ := exists_max_of_type_omegaOne_add_one (harms (stage a)).2
    exact ⟨m, trivial⟩
  let representative (a : W2) : arms (stage a) :=
    Classical.choose (hrepresentativeExists a)
  have hrepresentativeStrict : StrictMono
      (fun a : W2 ↦ (representative a : W2)) := by
    intro a b hab
    exact hordered (stage a) (stage b) (hstageStrict hab)
      (representative a) (representative a).property
      (representative b) (representative b).property
  have hpredecessorExists (j : Set.Ioi cutoff) (n : ℕ) :
      ∃ x : arms (early n), red.Adj x (representative (j : W2)) := by
    obtain ⟨x, hx, hred⟩ :=
      hincidence (early n) (stage (j : W2))
        (hearlyBeforeTail n j)
        (representative (j : W2)) (representative (j : W2)).property
    exact ⟨⟨x, hx⟩, hred⟩
  let predecessorProfile (j : Set.Ioi cutoff) :
      ∀ n : ℕ, arms (early n) :=
    fun n ↦ Classical.choose (hpredecessorExists j n)
  have hpredecessorRed (j : Set.Ioi cutoff) (n : ℕ) :
      red.Adj (predecessorProfile j n) (representative (j : W2)) :=
    Classical.choose_spec (hpredecessorExists j n)
  have harmsCard (n : ℕ) : #(arms (early n)) = ℵ_ 1 := by
    have hc := congrArg Ordinal.card (harms (early n)).2
    simpa only [Ordinal.card_type, Cardinal.card_omega_one_add_one] using hc
  have htailCard : #(Set.Ioi cutoff) = ℵ_ 2 :=
    mk_Ioi_omegaTwo_eq cutoff
  obtain ⟨fixedProfile, hlargeProfileFiber⟩ :=
    exists_alephTwo_fiber_of_countable_alephOne_profile
      hCH (fun n ↦ arms (early n)) htailCard harmsCard predecessorProfile
  let indexFiber : Set W2 :=
    Subtype.val '' (predecessorProfile ⁻¹' {fixedProfile})
  have hindexFiberCard : #indexFiber = ℵ_ 2 := by
    calc
      #indexFiber = #(predecessorProfile ⁻¹' {fixedProfile}) :=
        Cardinal.mk_image_eq Subtype.val_injective
      _ = ℵ_ 2 := hlargeProfileFiber
  let representativeFiber : Set W2 :=
    (fun a : W2 ↦ (representative a : W2)) '' indexFiber
  have hrepresentativeFiberCard : #representativeFiber = ℵ_ 2 := by
    calc
      #representativeFiber = #indexFiber :=
        Cardinal.mk_image_eq hrepresentativeStrict.injective
      _ = ℵ_ 2 := hindexFiberCard
  have hrepresentativeFiberType :
      typeLT representativeFiber = ω_ 2 :=
    typeLT_eq_omegaTwo_of_mk_eq hrepresentativeFiberCard
  let rawCenters : ℕ → W2 := fun n ↦ fixedProfile n
  have hrawCentersMem (n : ℕ) : rawCenters n ∈ arms (early n) :=
    (fixedProfile n).property
  have hrawCentersStrict : StrictMono rawCenters := by
    intro i j hij
    exact hordered (early i) (early j) (hearlyStrict hij)
      (rawCenters i) (hrawCentersMem i)
      (rawCenters j) (hrawCentersMem j)
  have hrawCentersBeforeFiber (n : ℕ) (y : W2)
      (hy : y ∈ representativeFiber) : rawCenters n < y := by
    obtain ⟨j, hj, rfl⟩ := hy
    obtain ⟨z, hz, rfl⟩ := hj
    exact hordered (early n) (stage (z : W2))
      (hearlyBeforeTail n z)
      (rawCenters n) (hrawCentersMem n)
      (representative (z : W2)) (representative (z : W2)).property
  have hrawCentersRedFiber (n : ℕ) (y : W2)
      (hy : y ∈ representativeFiber) :
      red.Adj (rawCenters n) y := by
    obtain ⟨j, hj, rfl⟩ := hy
    obtain ⟨z, hz, rfl⟩ := hj
    have hprofileEq : predecessorProfile z = fixedProfile := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hz
    simpa only [rawCenters, hprofileEq] using hpredecessorRed z n
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
  obtain ⟨transversal, htransversalSub, htransversalRed,
      htransversalType⟩ |
      ⟨transversal, htransversalSub, htransversalBlue,
        htransversalType⟩ :=
    OrdinalRamsey.on_set_of_type
      (Erdos1172Part3CHAsymmetric.red_target_or_blue_omegaOne_add_one hCH)
      red blue hcompl representativeFiber hrepresentativeFiberType
  · exact Or.inl ⟨transversal, htransversalRed, htransversalType⟩
  · right
    refine ⟨centerArms, centers, representativeFiber, transversal,
      hcenterArms, hcentersMem, hcenterArmsOrdered,
      hcentersStrict, ?_, ?_, hrepresentativeFiberCard,
      hrepresentativeFiberType, htransversalSub, htransversalBlue,
      htransversalType, ?_⟩
    · simpa only [centers] using hcentersType
    · simpa only [centers] using hcentersHomogeneous
    · intro n y hy
      exact ⟨hrawCentersBeforeFiber (indices n) y hy,
        hrawCentersRedFiber (indices n) y hy⟩

/-- The countably concentrated pattern has a sharp homogeneous split.
If the predecessor sequence is red, any point of the later transversal
extends it to an exact red `ω + 1` clique.  Otherwise the two sides are
blue cliques of types `ω` and `ω₁ + 1` with every cross-edge red. -/
theorem CountablyConcentratedTransversalPredecessorPattern.redOmegaAddOne_or_blueRectangle
    {red blue : SimpleGraph W2}
    (hpattern : CountablyConcentratedTransversalPredecessorPattern red blue) :
    OrdinalRamsey.HasCliqueOfType red (ω + 1) ∨
      ∃ (centers : ℕ → W2) (transversal : Set W2),
        StrictMono centers ∧ typeLT (Set.range centers) = ω ∧
        blue.IsClique (Set.range centers) ∧
        blue.IsClique transversal ∧ typeLT transversal = ω_ 1 + 1 ∧
        ∀ n, ∀ y ∈ transversal,
          centers n < y ∧ red.Adj (centers n) y := by
  obtain ⟨centerArms, centers, representativeFiber, transversal,
    -, -, -, hcentersStrict, hcentersType, hcentersRed | hcentersBlue,
    -, -, htransversalSub, htransversalBlue, htransversalType,
    hcross⟩ := hpattern
  · left
    obtain ⟨apex, -⟩ :=
      exists_max_of_type_omegaOne_add_one htransversalType
    obtain ⟨clique, hclique, hcliqueType⟩ :=
      red.exists_clique_type_add_one_of_common_later
        hcentersRed hcentersType
        (fun y hy ↦ by
          obtain ⟨n, rfl⟩ := hy
          exact (hcross n apex (htransversalSub apex.property)).1)
        (fun y hy ↦ by
          obtain ⟨n, rfl⟩ := hy
          exact (hcross n apex (htransversalSub apex.property)).2)
    exact ⟨clique, hclique, hcliqueType⟩
  · right
    exact ⟨centers, transversal, hcentersStrict, hcentersType,
      hcentersBlue, htransversalBlue, htransversalType,
      fun n y hy ↦ hcross n y (htransversalSub hy)⟩

/-- Global exact-target-or-countably-concentrated predecessor normal form
under CH. -/
theorem part3_exact_or_countablyConcentratedTransversalPredecessorPattern
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red
        Erdos1172Part3FiniteStars.RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      CountablyConcentratedTransversalPredecessorPattern red blue := by
  obtain htarget | hobs :=
    part3_exact_or_fullOmegaTwoIncidenceObstruction hCH red blue hcompl
  · exact Or.inl htarget
  · obtain hred | hpattern :=
      fullOmegaTwoIncidence_redTarget_or_countablyConcentratedPattern
        hCH red blue hcompl hobs
    · exact Or.inl (Or.inl hred)
    · exact Or.inr hpattern

end Erdos1172Part3TransversalPredecessorPattern
