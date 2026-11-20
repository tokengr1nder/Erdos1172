/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CHAsymmetric
public import Erdos1172.Part3InfiniteStars

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3CHOmegaOneArmTower

open Erdos1172Part3Failure Erdos1172Part3FiniteStars
  Erdos1172Part3InfiniteStars Erdos1172Part3CHAsymmetric

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

/-- Relative to a blue `ω₁ + 1` base, failure of both exact targets gives
an ordered blue `ω` sequence of centres, nested `ℵ₂` reservoirs, and at
every stage a whole blue arm of type `ω₁ + 1` inside the corresponding
reservoir.  Every earlier centre is red-adjacent to every point of the
later arm. -/
theorem red_target_or_ordered_omega_by_omegaOne_blue_arm_tower
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {base : Set W2} (hbase : blue.IsClique base)
    (hbaseType : typeLT base = ω_ 1 + 1)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) :
    OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      ∃ (m : W2) (centers : ℕ → W2) (arms reservoirs : ℕ → Set W2),
        m ∈ base ∧ StrictMono centers ∧
        typeLT (Set.range centers) = ω ∧
        blue.IsClique (Set.range centers) ∧
        (∀ n, #(reservoirs n) = ℵ_ 2 ∧ reservoirs n ⊆ Set.Ioi m) ∧
        (∀ n, reservoirs (n + 1) ⊆ reservoirs n) ∧
        (∀ n, arms n ⊆ reservoirs n ∧ blue.IsClique (arms n) ∧
          typeLT (arms n) = ω_ 1 + 1) ∧
        ∀ i n, i ≤ n → ∀ x ∈ arms n, red.Adj (centers i) x := by
  classical
  by_cases hred : OrdinalRamsey.HasCliqueOfType red RedTarget
  · exact Or.inl hred
  · right
    obtain ⟨m, originalCenters, originalReservoirs, hm,
        hcentersInjective, -, hcentersBlue, hreservoirs,
        hreservoirsNested, hstar⟩ :=
      exists_coherent_infinite_center_reservoir_sequence red blue hcompl
        hbase hbaseType hred hnoBlue
    obtain ⟨subseq, hsubseqMono⟩ :=
      wellQuasiOrdered_le.exists_monotone_subseq originalCenters
    let centers : ℕ → W2 := fun n ↦ originalCenters (subseq n)
    have hcentersStrict : StrictMono centers := by
      intro i j hij
      have hle : centers i ≤ centers j := hsubseqMono i j hij.le
      exact lt_of_le_of_ne hle fun heq ↦ by
        have hindex : (subseq i : ℕ) = subseq j := hcentersInjective heq
        exact hij.ne (subseq.injective hindex)
    have hcentersRangeSub : Set.range centers ⊆ Set.range originalCenters := by
      rintro _ ⟨n, rfl⟩
      exact ⟨subseq n, rfl⟩
    have hcentersClique : blue.IsClique (Set.range centers) :=
      hcentersBlue.subset hcentersRangeSub
    have hcentersType : typeLT (Set.range centers) = ω :=
      typeLT_range_eq_omega_of_strictMono centers hcentersStrict
    let reservoirs : ℕ → Set W2 := fun n ↦ originalReservoirs (subseq n + 1)
    have horiginalAntitone : Antitone originalReservoirs :=
      antitone_nat_of_succ_le hreservoirsNested
    have hreservoirsSampled (n : ℕ) :
        #(reservoirs n) = ℵ_ 2 ∧ reservoirs n ⊆ Set.Ioi m :=
      hreservoirs (subseq n + 1)
    have hreservoirsSampledNested (n : ℕ) :
        reservoirs (n + 1) ⊆ reservoirs n := by
      apply horiginalAntitone
      exact Nat.add_le_add_right (subseq.monotone (Nat.le_succ n)) 1
    have harmsExists (n : ℕ) :
        ∃ arm : Set W2, arm ⊆ reservoirs n ∧ blue.IsClique arm ∧
          typeLT arm = ω_ 1 + 1 :=
      exists_blue_omegaOne_add_one_in_every_alephTwo_set
        hCH red blue hcompl hred (hreservoirsSampled n).1
    let arms : ℕ → Set W2 := fun n ↦ Classical.choose (harmsExists n)
    have harms (n : ℕ) :
        arms n ⊆ reservoirs n ∧ blue.IsClique (arms n) ∧
          typeLT (arms n) = ω_ 1 + 1 :=
      Classical.choose_spec (harmsExists n)
    refine ⟨m, centers, arms, reservoirs, hm, hcentersStrict,
      hcentersType, hcentersClique, hreservoirsSampled,
      hreservoirsSampledNested, harms, ?_⟩
    intro i n hin x hx
    apply hstar (subseq i) (subseq n + 1)
    · exact (subseq.monotone hin).trans_lt (Nat.lt_succ_self (subseq n))
    · exact (harms n).1 hx

/-- Global CH form of the `ω`-by-`ω₁ + 1` arm tower. -/
theorem part3_exact_or_ordered_omega_by_omegaOne_blue_arm_tower
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      ∃ (m : W2) (centers : ℕ → W2) (arms reservoirs : ℕ → Set W2),
        StrictMono centers ∧ typeLT (Set.range centers) = ω ∧
        blue.IsClique (Set.range centers) ∧
        (∀ n, #(reservoirs n) = ℵ_ 2 ∧ reservoirs n ⊆ Set.Ioi m) ∧
        (∀ n, reservoirs (n + 1) ⊆ reservoirs n) ∧
        (∀ n, arms n ⊆ reservoirs n ∧ blue.IsClique (arms n) ∧
          typeLT (arms n) = ω_ 1 + 1) ∧
        ∀ i n, i ≤ n → ∀ x ∈ arms n, red.Adj (centers i) x := by
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
    · obtain hred | ⟨m, centers, arms, reservoirs, -, hcentersStrict,
        hcentersType, hcentersBlue, hreservoirs, hreservoirsNested,
        harms, hstar⟩ :=
        red_target_or_ordered_omega_by_omegaOne_blue_arm_tower
          hCH red blue hcompl hbase hbaseType hnone.2
      · exact (hnone.1 hred).elim
      · exact ⟨m, centers, arms, reservoirs, hcentersStrict,
          hcentersType, hcentersBlue, hreservoirs, hreservoirsNested,
          harms, hstar⟩

end Erdos1172Part3CHOmegaOneArmTower
