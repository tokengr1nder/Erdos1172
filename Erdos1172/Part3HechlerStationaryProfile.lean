/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3RegressiveDecisions
public import Erdos1172.Part3ClubDecisions
public import Erdos1172.Part3CenteredStationaryLoss

@[expose] public section

/-!
# A stationary uniform domination profile in the concrete closed order

For any ground family of functions omegaOne -> omegaOne indexed by a
stationary subset of omegaTwo, CH gives a condition and one countable
initial profile such that stationarily many indices remain possible
below every strengthening. Those indices have the same initial profile,
and every later stem decision is strictly above their function values.

The common tail is still a system of decisions, not a ground total
function dominating omegaTwo many functions. In particular the theorem
does not assert BHT's Q principle under GCH, or construct an iteration
handling new function names.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3HechlerStationaryProfile

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3HechlerOrder
open Erdos1172Part3StationaryDecisions
open Erdos1172Part3CenteredStationaryLoss (exists_stationary_fiber_of_small)
open Erdos1172Part3ConvergentCore (mk_Iic_W1_lt)

/-- All future values decided past the bound dominate this function. -/
def DominatesAfter (p : Condition) (f : W1 → W1) (bound : W1) : Prop :=
  ∀ q : Condition, q ≤ p → ∀ i : W1, bound < i →
    ∀ v : W1, q.stem i = some v → f i < v

theorem dominatesAfter_mono {p q : Condition} {f : W1 → W1} {bound : W1}
    (hp : DominatesAfter p f bound) (hqp : q ≤ p) : DominatesAfter q f bound :=
  fun r hrq => hp r (hrq.trans hqp)

def TailMembers (S : Set W2) (F : W2 → W1 → W1) (bound : W1)
    (p : Condition) (a : W2) : Prop := a ∈ S ∧ DominatesAfter p (F a) bound

theorem tailMembers_persistent (S : Set W2) (F : W2 → W1 → W1) (bound : W1) :
    Persistent (TailMembers S F bound) :=
  fun hqp h => ⟨h.1, dominatesAfter_mono h.2 hqp⟩

/-- Freeze the tail bound on a stationary set of possible indices. This
uses the actual tracking conditions, not an assumed domination system. -/
theorem exists_stationary_uniform_tail (hCH : CH) (p0 : Condition)
    (S : Set W2) (hS : IsStationary S) (F : W2 → W1 → W1) :
    ∃ bound : W1, ∃ p : Condition, p ≤ p0 ∧ StationaryAt (TailMembers S F bound) p := by
  classical
  have witness (a : W2) : ∃ bound : W1, ∃ p : Condition,
      p ≤ p0 ∧ DominatesAfter p (F a) bound := by
    obtain ⟨bound, hb⟩ := tracked_eventual_lower_bound (track p0 (F a)) (F a)
      (Set.mem_insert _ _)
    exact ⟨bound, track p0 (F a), track_le p0 (F a), hb⟩
  let chosen (a : S) : W1 := (witness a.val).choose
  have hsmall : #W1 < ℵ_ 2 := by
    simp only [W1, Cardinal.mk_toType, Ordinal.card_omega]
    exact Cardinal.aleph_lt_aleph.mpr (by norm_num)
  obtain ⟨bound, hfiber⟩ := exists_stationary_fiber_of_small hsmall hS chosen
  have hpossible : IsStationary (possible (TailMembers S F bound) p0) := by
    apply hfiber.mono
    rintro a ⟨ha, heq⟩
    obtain ⟨p, hpp0, hp⟩ := (witness a).choose_spec
    change (witness a).choose = bound at heq
    rw [heq] at hp
    exact ⟨p, hpp0, ha, hp⟩
  obtain ⟨p, hpp0, hp⟩ := exists_stationary_refinement (hechler_omegaTwoCC hCH)
    (TailMembers S F bound) (tailMembers_persistent S F bound) p0 hpossible
  exact ⟨bound, p, hpp0, hp⟩

def ProfileMembers (S : Set W2) (F : W2 → W1 → W1) (bound : W1)
    (profile : Set.Iic bound → W1) (p : Condition) (a : W2) : Prop :=
  a ∈ S ∧ (∀ i : Set.Iic bound, F a i.val = profile i) ∧ DominatesAfter p (F a) bound

theorem profileMembers_persistent (S : Set W2) (F : W2 → W1 → W1) (bound : W1)
    (profile : Set.Iic bound → W1) : Persistent (ProfileMembers S F bound profile) :=
  fun hqp h => ⟨h.1, h.2.1, dominatesAfter_mono h.2.2 hqp⟩

/-- The ground initial profile is fixed as well as the tail threshold.
The stationary index set is represented by persistent possibilities;
it is not assumed to survive a completed omegaOne descending sequence. -/
theorem exists_stationary_uniform_profile (hCH : CH) (p0 : Condition)
    (S : Set W2) (hS : IsStationary S) (F : W2 → W1 → W1) :
    ∃ bound : W1, ∃ profile : Set.Iic bound → W1, ∃ p : Condition,
      p ≤ p0 ∧ StationaryAt (ProfileMembers S F bound profile) p := by
  classical
  obtain ⟨bound, p, hpp0, hp⟩ := exists_stationary_uniform_tail hCH p0 S hS F
  have hprofiles : #(Set.Iic bound → W1) < ℵ_ 2 := by
    rw [Cardinal.mk_arrow]
    simp only [Cardinal.lift_id, W1, Cardinal.mk_toType, Ordinal.card_omega]
    have hcount : #(Set.Iic bound) ≤ ℵ₀ := Cardinal.lt_aleph_one_iff.mp (mk_Iic_W1_lt bound)
    exact ((Cardinal.power_le_power_left (Cardinal.aleph0_pos.trans_le
      (Cardinal.aleph0_le_aleph 1)).ne' hcount).trans_eq
      hCH.aleph_one_power_aleph_zero).trans_lt
        (Cardinal.aleph_lt_aleph.mpr (by norm_num : (1 : Ordinal.{0}) < 2))
  let chosen (a : possible (TailMembers S F bound) p) : Set.Iic bound → W1 :=
    fun i => F a.val i.val
  obtain ⟨profile, hfiber⟩ := exists_stationary_fiber_of_small hprofiles (hp p le_rfl) chosen
  have hpossible : IsStationary (possible (ProfileMembers S F bound profile) p) := by
    apply hfiber.mono
    rintro a ⟨ha, heq⟩
    obtain ⟨q, hqp, haS, hq⟩ := ha
    refine ⟨q, hqp, haS, ?_, hq⟩
    intro i
    exact congrFun heq i
  obtain ⟨q, hqp, hq⟩ := exists_stationary_refinement (hechler_omegaTwoCC hCH)
    (ProfileMembers S F bound profile) (profileMembers_persistent S F bound profile) p hpossible
  exact ⟨bound, profile, q, hqp.trans hpp0, hq⟩

/-- A coordinate already decided by a condition bounds every index
which is still possible there, not just the indices already tracked. -/
theorem possible_profile_value_lt (S : Set W2) (F : W2 → W1 → W1) (bound : W1)
    (profile : Set.Iic bound → W1) {p : Condition} {i v : W1}
    (hi : bound < i) (hv : p.stem i = some v) {a : W2}
    (ha : a ∈ possible (ProfileMembers S F bound profile) p) : F a i < v := by
  obtain ⟨q, hqp, _, _, hq⟩ := ha
  exact hq q le_rfl i hi v (hqp.1 i v hv)

end Erdos1172Part3HechlerStationaryProfile
