/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3BlueRectangleFullLoss
public import Erdos1172.ForMathlib.SetTheory.Ordinal.InfiniteRamsey

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3HomogeneousFailureLadder

open Erdos1172Part3Failure Erdos1172Part3BlueRectangleFullLoss

/-- The range of a strictly increasing sequence in `ω₂` has exact order
type `ω`. -/
private theorem typeLT_range_eq_omega_of_strictMono (f : ℕ → W2)
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

/-- Infinite Ramsey, in the exact subsequence form needed for the arm
chain: a strictly increasing sequence in `ω₂` has a strictly increasing
subsequence of exact type `ω` which is homogeneous in one of the two
complementary colors. -/
theorem exists_homogeneous_strict_subsequence
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (points : ℕ → W2) (hpoints : StrictMono points) :
    ∃ indices : ℕ → ℕ, StrictMono indices ∧
      typeLT (Set.range (points ∘ indices)) = ω ∧
      (red.IsClique (Set.range (points ∘ indices)) ∨
        blue.IsClique (Set.range (points ∘ indices))) := by
  classical
  obtain ⟨indicesSet, hindicesInfinite, hindicesColor⟩ :
      ∃ s : Set ℕ, s.Infinite ∧
        ((red.comap points).IsClique s ∨
          (red.comap points)ᶜ.IsClique s) := by
    rcases (red.comap points).exists_infinite_clique_or_compl with
      ⟨s, hs, hsClique⟩ | ⟨s, hs, hsClique⟩
    · exact ⟨s, hs, Or.inl hsClique⟩
    · exact ⟨s, hs, Or.inr hsClique⟩
  let rawIndices : ℕ ↪ indicesSet :=
    hindicesInfinite.natEmbedding indicesSet
  obtain ⟨subseq, hsubseqMono⟩ :=
    wellQuasiOrdered_le.exists_monotone_subseq
      (fun n ↦ (rawIndices n : ℕ))
  let indices : ℕ → ℕ := fun n ↦ (rawIndices (subseq n) : ℕ)
  have hindicesStrict : StrictMono indices := by
    intro i j hij
    have hle : indices i ≤ indices j := hsubseqMono i j hij.le
    exact lt_of_le_of_ne hle fun heq ↦ by
      have hrawEq : rawIndices (subseq i) = rawIndices (subseq j) :=
        Subtype.ext heq
      have hsubseqEq : (subseq i : ℕ) = subseq j :=
        rawIndices.injective hrawEq
      exact hij.ne (subseq.injective hsubseqEq)
  have hindicesMem (n : ℕ) : indices n ∈ indicesSet :=
    (rawIndices (subseq n)).property
  have hselectedStrict : StrictMono (points ∘ indices) :=
    hpoints.comp hindicesStrict
  refine ⟨indices, hindicesStrict,
    typeLT_range_eq_omega_of_strictMono _ hselectedStrict, ?_⟩
  rcases hindicesColor with hredIndices | hcomplIndices
  · left
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    have hindexNe : indices i ≠ indices j := by
      intro hij
      exact hne (congrArg points hij)
    exact hredIndices (hindicesMem i) (hindicesMem j) hindexNe
  · right
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    have hindexNe : indices i ≠ indices j := by
      intro hij
      exact hne (congrArg points hij)
    have hedge := hcomplIndices (hindicesMem i) (hindicesMem j) hindexNe
    rw [SimpleGraph.compl_adj] at hedge
    rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
    exact ⟨hne, hedge.2⟩

/-- Consecutive strict ordering of nonempty arms propagates to every
ordered pair of arms. -/
private theorem ordered_arms_of_ordered_successors
    (arms : ℕ → Set W2) (witnesses : ℕ → W2)
    (hwitnessMem : ∀ n, witnesses n ∈ arms n)
    (hordered : ∀ n, ∀ z ∈ arms n, ∀ x ∈ arms (n + 1), z < x)
    {i j : ℕ} (hij : i < j) :
    ∀ z ∈ arms i, ∀ x ∈ arms j, z < x := by
  have hle : i + 1 ≤ j := Nat.succ_le_iff.mpr hij
  induction j, hle using Nat.le_induction with
  | base =>
      exact hordered i
  | succ j hj ih =>
      intro z hz x hx
      exact (ih (Nat.lt_of_succ_le hj) z hz
        (witnesses j) (hwitnessMem j)).trans
        (hordered j (witnesses j) (hwitnessMem j) x hx)

/-- Ramsey-homogeneous ladder extracted from the infinite arm failure
chain.  Both rails are independently homogeneous (red or blue), every
rung is a complete red star into a blue `ω₁ + 1` arm, and the rungs are
strictly interleaved in the ambient well-order. -/
theorem infiniteBlueRectangleFailureChain_has_homogeneous_ladder
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (hchain : InfiniteBlueRectangleFailureChain red blue) :
    ∃ (anchors companions : ℕ → W2) (companionArms : ℕ → Set W2),
      StrictMono anchors ∧ typeLT (Set.range anchors) = ω ∧
      (red.IsClique (Set.range anchors) ∨
        blue.IsClique (Set.range anchors)) ∧
      StrictMono companions ∧ typeLT (Set.range companions) = ω ∧
      (red.IsClique (Set.range companions) ∨
        blue.IsClique (Set.range companions)) ∧
      (∀ n, companions n ∈ companionArms n) ∧
      (∀ n, blue.IsClique (companionArms n) ∧
        typeLT (companionArms n) = ω_ 1 + 1) ∧
      (∀ n, ∀ x ∈ companionArms n,
        anchors n < x ∧ red.Adj (anchors n) x) ∧
      ∀ n, ∀ x ∈ companionArms n, x < anchors (n + 1) := by
  classical
  obtain ⟨m, centers, firstArm, fiber, arms, maxima, witnesses,
      failureFibers, -, -, -, -, -, -, -, -, -, harmsZero,
      harmsBlueType, hmembers, -, -, hordered, hredStars⟩ := hchain
  have hwitnessLtSucc (n : ℕ) : witnesses n < witnesses (n + 1) :=
    hordered n (witnesses n) (hmembers n).2
      (witnesses (n + 1)) (hmembers (n + 1)).2
  have hwitnessStrict : StrictMono witnesses :=
    strictMono_nat_of_lt_succ hwitnessLtSucc
  let rawAnchors : ℕ → W2 := fun n ↦ witnesses (2 * n)
  have hevenStrict : StrictMono (fun n : ℕ ↦ 2 * n) := by
    intro i j hij
    exact (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).2 hij
  have hrawAnchorsStrict : StrictMono rawAnchors :=
    hwitnessStrict.comp hevenStrict
  obtain ⟨firstIndices, hfirstIndicesStrict, -, hfirstAnchorColor⟩ :=
    exists_homogeneous_strict_subsequence red blue hcompl
      rawAnchors hrawAnchorsStrict
  let selectedAnchors : ℕ → W2 := rawAnchors ∘ firstIndices
  have hselectedAnchorsStrict : StrictMono selectedAnchors :=
    hrawAnchorsStrict.comp hfirstIndicesStrict
  let rawCompanions : ℕ → W2 :=
    fun n ↦ witnesses (2 * firstIndices n + 1)
  have hoddFirstStrict : StrictMono (fun n : ℕ ↦ 2 * firstIndices n + 1) := by
    intro i j hij
    exact Nat.add_lt_add_right
      ((Nat.mul_lt_mul_left (by norm_num : 0 < 2)).2
        (hfirstIndicesStrict hij)) 1
  have hrawCompanionsStrict : StrictMono rawCompanions :=
    hwitnessStrict.comp hoddFirstStrict
  obtain ⟨secondIndices, hsecondIndicesStrict, hcompanionType,
      hcompanionColor⟩ :=
    exists_homogeneous_strict_subsequence red blue hcompl
      rawCompanions hrawCompanionsStrict
  let blockIndices : ℕ → ℕ := firstIndices ∘ secondIndices
  have hblockIndicesStrict : StrictMono blockIndices :=
    hfirstIndicesStrict.comp hsecondIndicesStrict
  let anchors : ℕ → W2 := selectedAnchors ∘ secondIndices
  let companions : ℕ → W2 := rawCompanions ∘ secondIndices
  let companionArms : ℕ → Set W2 :=
    fun n ↦ arms (2 * blockIndices n + 1)
  have hanchorsStrict : StrictMono anchors :=
    hselectedAnchorsStrict.comp hsecondIndicesStrict
  have hcompanionsStrict : StrictMono companions :=
    hrawCompanionsStrict.comp hsecondIndicesStrict
  have hanchorColor :
      red.IsClique (Set.range anchors) ∨
        blue.IsClique (Set.range anchors) := by
    have hrangeSub : Set.range anchors ⊆ Set.range selectedAnchors := by
      rintro _ ⟨n, rfl⟩
      exact ⟨secondIndices n, rfl⟩
    exact hfirstAnchorColor.imp (fun h ↦ h.subset hrangeSub)
      (fun h ↦ h.subset hrangeSub)
  have hcompanionColor' :
      red.IsClique (Set.range companions) ∨
        blue.IsClique (Set.range companions) := hcompanionColor
  have hcompanionType' : typeLT (Set.range companions) = ω :=
    hcompanionType
  have hcompanionMem (n : ℕ) : companions n ∈ companionArms n := by
    exact (hmembers (2 * blockIndices n + 1)).2
  have hcompanionArms (n : ℕ) :
      blue.IsClique (companionArms n) ∧
        typeLT (companionArms n) = ω_ 1 + 1 :=
    harmsBlueType (2 * blockIndices n + 1)
  have hrung (n : ℕ) (x : W2) (hx : x ∈ companionArms n) :
      anchors n < x ∧ red.Adj (anchors n) x := by
    have hanchorMem : anchors n ∈ arms (2 * blockIndices n) :=
      (hmembers (2 * blockIndices n)).2
    exact ⟨hordered (2 * blockIndices n) (anchors n) hanchorMem x hx,
      hredStars (2 * blockIndices n) x hx⟩
  have hinterleave (n : ℕ) (x : W2) (hx : x ∈ companionArms n) :
      x < anchors (n + 1) := by
    have hindex : 2 * blockIndices n + 1 < 2 * blockIndices (n + 1) := by
      have hk : blockIndices n < blockIndices (n + 1) := by
        simpa only [Nat.succ_eq_add_one] using
          hblockIndicesStrict (Nat.lt_succ_self n)
      omega
    have hanchorMem : anchors (n + 1) ∈
        arms (2 * blockIndices (n + 1)) :=
      (hmembers (2 * blockIndices (n + 1))).2
    exact ordered_arms_of_ordered_successors arms witnesses
      (fun k ↦ (hmembers k).2) hordered hindex x hx
        (anchors (n + 1)) hanchorMem
  exact ⟨anchors, companions, companionArms, hanchorsStrict,
    typeLT_range_eq_omega_of_strictMono anchors hanchorsStrict,
    hanchorColor, hcompanionsStrict, hcompanionType',
    hcompanionColor', hcompanionMem, hcompanionArms, hrung,
    hinterleave⟩

/-- Global CH normal form after homogenizing the infinite blue-arm
failure chain.  If no exact target occurs, either the red uniform
rectangle remains or there is a strictly interleaved homogeneous ladder
with blue `ω₁ + 1` rungs and complete red rung stars. -/
theorem part3_exact_or_red_rectangle_or_homogeneous_failure_ladder
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red
        Erdos1172Part3FiniteStars.RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      UniformRedRectangle red blue ∨
      ∃ (anchors companions : ℕ → W2) (companionArms : ℕ → Set W2),
        StrictMono anchors ∧ typeLT (Set.range anchors) = ω ∧
        (red.IsClique (Set.range anchors) ∨
          blue.IsClique (Set.range anchors)) ∧
        StrictMono companions ∧ typeLT (Set.range companions) = ω ∧
        (red.IsClique (Set.range companions) ∨
          blue.IsClique (Set.range companions)) ∧
        (∀ n, companions n ∈ companionArms n) ∧
        (∀ n, blue.IsClique (companionArms n) ∧
          typeLT (companionArms n) = ω_ 1 + 1) ∧
        (∀ n, ∀ x ∈ companionArms n,
          anchors n < x ∧ red.Adj (anchors n) x) ∧
        ∀ n, ∀ x ∈ companionArms n, x < anchors (n + 1) := by
  obtain htarget | hredRectangle | hblueChain :=
    part3_exact_or_red_rectangle_or_infinite_blue_failure_chain
      hCH red blue hcompl
  · exact Or.inl htarget
  · exact Or.inr (Or.inl hredRectangle)
  · exact Or.inr (Or.inr
      (infiniteBlueRectangleFailureChain_has_homogeneous_ladder
        red blue hcompl hblueChain))

end Erdos1172Part3HomogeneousFailureLadder
