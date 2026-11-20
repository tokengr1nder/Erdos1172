/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CountableProfiles
public import Erdos1172.Part3CHAsymmetric
public import Erdos1172.Part3InfiniteStars

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3CHUniformRectangles

open Erdos1172Part3Failure Erdos1172Part3FiniteStars
  Erdos1172Part3CHAsymmetric
  Erdos1172Part3InfiniteStars

/-- The range of a strictly increasing sequence in `ω₂` has exact order
type `ω`. -/
private theorem typeLT_range_eq_omega_of_strictMono (f : ℕ → W2)
    (hf : StrictMono f) : typeLT (Set.range f) = ω := by
  have htype :=
    ((hf.strictMonoOn Set.univ).orderIso f Set.univ).ordinalType_congr
  have himageRange : typeLT (f '' Set.univ) = typeLT (Set.range f) :=
    (OrderIso.setCongr (f '' Set.univ) (Set.range f) Set.image_univ).ordinalType_congr
  calc
    typeLT (Set.range f) = typeLT (f '' Set.univ) := himageRange.symm
    _ = typeLT (Set.univ : Set ℕ) := htype.symm
    _ = typeLT ℕ := OrderIso.Set.univ.ordinalType_congr
    _ = ω := Ordinal.type_nat_lt

/-- Removing a smaller set from an `ℵ₂`-sized set preserves cardinality. -/
private theorem mk_sdiff_eq_alephTwo_of_mk_lt
    {s t : Set W2} (hs : #s = ℵ_ 2) (ht : #t < ℵ_ 2) :
    #(s \ t : Set W2) = ℵ_ 2 := by
  apply le_antisymm
  · simpa [hs] using
      Cardinal.mk_le_mk_of_subset (Set.sdiff_subset : s \ t ⊆ s)
  · by_contra h
    have hdiff : #(s \ t : Set W2) < ℵ_ 2 := lt_of_not_ge h
    have hcover : ℵ_ 2 ≤ #(s \ t : Set W2) + #t := by
      simpa [hs] using Cardinal.le_mk_sdiff_add_mk s t
    exact (not_lt_of_ge hcover)
      (Cardinal.add_lt_of_lt (Cardinal.aleph0_le_aleph 2) hdiff ht)

/-- Under CH, either an exact Part 3 target occurs or there is a complete
monochromatic rectangle between an ordered blue `ω` side and an
`ℵ₂`-sized later fiber.  In the latter fiber there is also a blue arm of
exact type `ω₁ + 1`.  The rectangle color is red or blue; this is the
sharp alternative left by countable Boolean-profile compression. -/
theorem part3_exact_or_ordered_omega_by_alephTwo_uniform_rectangle
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      ∃ (m : W2) (centers : ℕ → W2) (arm fiber : Set W2),
        StrictMono centers ∧ typeLT (Set.range centers) = ω ∧
        blue.IsClique (Set.range centers) ∧
        #fiber = ℵ_ 2 ∧ fiber ⊆ Set.Ioi m ∧
        arm ⊆ fiber ∧ blue.IsClique arm ∧ typeLT arm = ω_ 1 + 1 ∧
        ((∀ i, ∀ x ∈ fiber, red.Adj (centers i) x) ∨
          ∀ i, ∀ x ∈ fiber, blue.Adj (centers i) x) := by
  classical
  by_cases htarget :
      OrdinalRamsey.HasCliqueOfType red RedTarget ∨
        OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)
  · exact Or.inl htarget
  · right
    have hnone := not_or.mp htarget
    obtain ⟨base, hbase, hbaseType⟩ | ⟨base, hbase, hbaseType⟩ :=
      red_target_or_blue_omegaOne_add_one hCH red blue hcompl
    · exact (hnone.1 ⟨base, hbase, hbaseType⟩).elim
    · obtain ⟨m, originalCenters, reservoirs, -, hcentersInjective,
        -, hcentersBlue, hreservoirs, -, -⟩ :=
        exists_coherent_infinite_center_reservoir_sequence red blue hcompl
          hbase hbaseType hnone.1 hnone.2
      have hcentersCard : #(Set.range originalCenters) ≤ ℵ₀ := by
        simpa using Cardinal.mk_range_le_lift (f := originalCenters)
      obtain ⟨profile, uniformFiber, huniformFiberSub,
          huniformFiberCard, huniformRaw⟩ :=
        Erdos1172Part3CountableProfiles.exists_alephTwo_uniform_adjacencyProfile
          hCH red hcentersCard (hreservoirs 0).1
      have hcentersLt : #(Set.range originalCenters) < ℵ_ 2 :=
        hcentersCard.trans_lt (Cardinal.aleph0_lt_aleph.mpr (by norm_num))
      let fiber : Set W2 := uniformFiber \ Set.range originalCenters
      have hfiberCard : #fiber = ℵ_ 2 :=
        mk_sdiff_eq_alephTwo_of_mk_lt huniformFiberCard hcentersLt
      have hfiberSub : fiber ⊆ uniformFiber := Set.sdiff_subset
      have hfiberReservoir : fiber ⊆ reservoirs 0 :=
        hfiberSub.trans huniformFiberSub
      have huniform (x : W2) (hx : x ∈ fiber) :
          Erdos1172Part3CountableProfiles.adjacencyProfile
            red (Set.range originalCenters) x = profile :=
        huniformRaw x (hfiberSub hx)
      let color : ℕ → Bool := fun n ↦
        profile ⟨originalCenters n, ⟨n, rfl⟩⟩
      obtain ⟨c, hcInfiniteType⟩ :=
        Finite.exists_infinite_fiber color
      have hcInfinite : (color ⁻¹' {c}).Infinite :=
        Set.infinite_coe_iff.mp hcInfiniteType
      let rawIndices : ℕ ↪ (color ⁻¹' {c}) :=
        hcInfinite.natEmbedding (color ⁻¹' {c})
      let sampled : ℕ → W2 := fun n ↦
        originalCenters (rawIndices n : ℕ)
      obtain ⟨subseq, hsubseqMono⟩ :=
        wellQuasiOrdered_le.exists_monotone_subseq sampled
      let indices : ℕ → ℕ := fun n ↦
        (rawIndices (subseq n) : ℕ)
      let centers : ℕ → W2 := fun n ↦ originalCenters (indices n)
      have hindicesInjective : Function.Injective indices := by
        intro i j hij
        have hraw : rawIndices (subseq i) = rawIndices (subseq j) :=
          Subtype.ext hij
        exact subseq.injective (rawIndices.injective hraw)
      have hcentersStrict : StrictMono centers := by
        intro i j hij
        have hle : centers i ≤ centers j := hsubseqMono i j hij.le
        exact lt_of_le_of_ne hle fun heq ↦ by
          have hindexEq : indices i = indices j := hcentersInjective heq
          exact hij.ne (hindicesInjective hindexEq)
      have hcentersRangeSub :
          Set.range centers ⊆ Set.range originalCenters := by
        rintro _ ⟨n, rfl⟩
        exact ⟨indices n, rfl⟩
      have hcentersClique : blue.IsClique (Set.range centers) :=
        hcentersBlue.subset hcentersRangeSub
      have hcentersType : typeLT (Set.range centers) = ω :=
        typeLT_range_eq_omega_of_strictMono centers hcentersStrict
      have hcolor (n : ℕ) : color (indices n) = c := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
          (rawIndices (subseq n)).property
      have hdecision (n : ℕ) (x : W2) (hx : x ∈ fiber) :
          decide (red.Adj (centers n) x) = c := by
        have hprofile := congrFun (huniform x hx)
          (⟨centers n, ⟨indices n, rfl⟩⟩ : Set.range originalCenters)
        change decide (red.Adj (centers n) x) =
          profile ⟨centers n, ⟨indices n, rfl⟩⟩ at hprofile
        exact hprofile.trans (hcolor n)
      have hfiberTail : fiber ⊆ Set.Ioi m :=
        hfiberReservoir.trans (hreservoirs 0).2
      have hrectangle :
          (∀ i, ∀ x ∈ fiber, red.Adj (centers i) x) ∨
            ∀ i, ∀ x ∈ fiber, blue.Adj (centers i) x := by
        cases c with
        | false =>
            right
            intro i x hx
            have hnred : ¬ red.Adj (centers i) x :=
              of_decide_eq_false (hdecision i x hx)
            have hne : centers i ≠ x := by
              intro heq
              exact hx.2 ⟨indices i, heq⟩
            rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
            exact ⟨hne, hnred⟩
        | true =>
            left
            intro i x hx
            exact of_decide_eq_true (hdecision i x hx)
      obtain ⟨arm, harmSub, harmBlue, harmType⟩ :=
        exists_blue_omegaOne_add_one_in_every_alephTwo_set
          hCH red blue hcompl hnone.1 hfiberCard
      exact ⟨m, centers, arm, fiber, hcentersStrict, hcentersType,
        hcentersClique, hfiberCard, hfiberTail, harmSub, harmBlue,
        harmType, hrectangle⟩

end Erdos1172Part3CHUniformRectangles
