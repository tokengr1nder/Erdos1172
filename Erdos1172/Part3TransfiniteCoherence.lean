/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CHOmegaOneArmTower

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3TransfiniteCoherence

open Erdos1172Part3Failure Erdos1172Part3FiniteStars
  Erdos1172Part3CHOmegaOneArmTower

/-- A transfinite red reservoir thread.  At every stage the reservoir is
still `ℵ₂`, later reservoirs are nested inside earlier ones, the chosen
point belongs to its current reservoir, and every later reservoir is
red-adjacent to every earlier chosen point. -/
structure RedReservoirThread (red : SimpleGraph W2) (κ : Ordinal.{0}) where
  points : κ.ToType → W2
  reservoirs : κ.ToType → Set W2
  points_strict : StrictMono points
  reservoir_large : ∀ ξ, #(reservoirs ξ) = ℵ_ 2
  reservoirs_antitone : Antitone reservoirs
  point_mem : ∀ ξ, points ξ ∈ reservoirs ξ
  prior_red : ∀ {ξ η}, ξ < η →
    ∀ x ∈ reservoirs η, red.Adj (points ξ) x

/-- A transfinite red reservoir thread collapses to a red clique of the
same exact order type.  Thus preserving the large nested reservoirs and
the prior-red invariant through all limit stages is sufficient for the
target extension. -/
theorem RedReservoirThread.hasCliqueOfType
    {red : SimpleGraph W2} {κ : Ordinal.{0}}
    (thread : RedReservoirThread red κ) :
    OrdinalRamsey.HasCliqueOfType red κ := by
  refine ⟨Set.range thread.points, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    have hij : i ≠ j := by
      intro hij
      exact hne (congrArg thread.points hij)
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact thread.prior_red hij _ (thread.point_mem j)
    · exact (thread.prior_red hji _ (thread.point_mem i)).symm
  · have htype :=
      ((thread.points_strict.strictMonoOn Set.univ).orderIso
        thread.points Set.univ).ordinalType_congr
    have himageRange :
        typeLT (thread.points '' Set.univ) =
          typeLT (Set.range thread.points) :=
      (OrderIso.setCongr (thread.points '' Set.univ)
        (Set.range thread.points) Set.image_univ).ordinalType_congr
    calc
      typeLT (Set.range thread.points) =
          typeLT (thread.points '' Set.univ) := himageRange.symm
      _ = typeLT (Set.univ : Set κ.ToType) := htype.symm
      _ = typeLT κ.ToType := OrderIso.Set.univ.ordinalType_congr
      _ = κ := Ordinal.type_toType κ

/-- In particular, a coherent thread indexed by the Part 3 red target
already gives the exact red target. -/
theorem has_exact_red_target_of_transfinite_reservoir_coherence
    {red : SimpleGraph W2}
    (thread : RedReservoirThread red RedTarget) :
    OrdinalRamsey.HasCliqueOfType red RedTarget :=
  thread.hasCliqueOfType

/-- The global ordered `ω`-by-`ω₁ + 1` blue-arm tower obstruction. -/
def OrderedOmegaByOmegaOneBlueArmTower
    (red blue : SimpleGraph W2) : Prop :=
  ∃ (m : W2) (centers : ℕ → W2) (arms reservoirs : ℕ → Set W2),
    StrictMono centers ∧ typeLT (Set.range centers) = ω ∧
    blue.IsClique (Set.range centers) ∧
    (∀ n, #(reservoirs n) = ℵ_ 2 ∧ reservoirs n ⊆ Set.Ioi m) ∧
    (∀ n, reservoirs (n + 1) ⊆ reservoirs n) ∧
    (∀ n, arms n ⊆ reservoirs n ∧ blue.IsClique (arms n) ∧
      typeLT (arms n) = ω_ 1 + 1) ∧
    ∀ i n, i ≤ n → ∀ x ∈ arms n, red.Adj (centers i) x

/-- Precise global gap theorem under CH.  If neither exact Part 3 target
occurs, the strong `ω`-by-`ω₁ + 1` arm tower exists, but no target-length
red reservoir thread can preserve the large nested reservoirs together
with the prior-red invariant. -/
theorem part3_exact_or_arm_tower_with_transfinite_coherence_gap
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      (OrderedOmegaByOmegaOneBlueArmTower red blue ∧
        ¬ Nonempty (RedReservoirThread red RedTarget)) := by
  by_cases htarget :
      OrdinalRamsey.HasCliqueOfType red RedTarget ∨
        OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)
  · exact Or.inl htarget
  · right
    have htower : OrderedOmegaByOmegaOneBlueArmTower red blue := by
      obtain hexact | htower :=
        part3_exact_or_ordered_omega_by_omegaOne_blue_arm_tower
          hCH red blue hcompl
      · exact (htarget hexact).elim
      · exact htower
    refine ⟨htower, ?_⟩
    rintro ⟨thread⟩
    exact (not_or.mp htarget).1 thread.hasCliqueOfType

end Erdos1172Part3TransfiniteCoherence
