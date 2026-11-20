/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3FullStationaryFiniteCores

@[expose] public section

/-!
# All finite-power partition bounds under GCH

The stationary factories are constructed uniformly in the finite depth.
Their actual ground clique extraction and the two-successor bootstrap
give every finite-power red target. The omega+2 exponent remains larger.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3FinitePowerRelations

open ErdosRadoCHAsym (W1 W2 IsOmegaOneSup)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularStageLocality (eventuallyLocal_ground)
open Erdos1172Part3TransfiniteStageLocality (Full Earlier restriction)
open Erdos1172Part3FiniteTraceSchemes (Index mk_index_le typeLT_index)
open Erdos1172Part3FullStationaryFiniteCores (finite_factory)
open Erdos1172Part3StationaryDecisions (StationaryAt)
open Erdos1172Part3TwoSuccessorBootstrap (ordinalRamsey_add_two_of_core)
open OrdinalRamsey (HasCliqueOfType)

theorem finite_power_pos (n : ℕ) : (0 : Ordinal.{0}) < (ω_ 1) ^ (↑n : Ordinal) :=
  Ordinal.opow_pos _ (Ordinal.omega0_pos.trans_le (Ordinal.omega0_le_omega 1))

theorem finite_power_lt_omegaTwo (n : ℕ) : (ω_ 1 : Ordinal.{0}) ^ (↑n : Ordinal) < ω_ 2 :=
  Ordinal.isPrincipal_opow_omega 2 (Ordinal.omega_lt_omega.mpr one_lt_two)
    ((Ordinal.natCast_lt_omega0 n).trans_le (Ordinal.omega0_le_omega 2))

theorem finite_power_add_two_le_omegaTwo (n : ℕ) :
    (ω_ 1 : Ordinal.{0}) ^ (↑n : Ordinal) + 2 ≤ ω_ 2 :=
  (Ordinal.isPrincipal_add_omega 2 (finite_power_lt_omegaTwo n)
    ((Ordinal.natCast_lt_omega0 2).trans_le (Ordinal.omega0_le_omega 2))).le

theorem isPrincipal_add_finite_power (n : ℕ) :
    Ordinal.IsPrincipal (· + ·) ((ω_ 1 : Ordinal.{0}) ^ (↑n : Ordinal)) :=
  Ordinal.isPrincipal_add_opow_of_isPrincipal_add (Ordinal.isPrincipal_add_omega 1) (↑n : Ordinal)

theorem exists_ground_finite_core (hGCH : GCH) (n : ℕ) (G H : SimpleGraph W2)
    (hcompl : IsCompl G H) (hred : ¬HasCliqueOfType G (ω_ 2))
    (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) :
    HasCliqueOfType G ((ω_ 1) ^ (↑(n + 1) : Ordinal.{0})) := by
  let source : RegularName (Full hGCH) W2 := ground {a : W2 | IsOmegaOneSup a}
  let p0 : Full hGCH := default
  have hstat : StationaryAt source.holds p0 := by
    intro p hp
    exact ErdosRadoCHAsym.isStationary_isOmegaOneSup_omegaTwo.mono
      (fun a ha => ⟨p, le_rfl, ha⟩)
  obtain ⟨a, q, _, _, N, _, _, _⟩ := finite_factory hGCH G H hcompl hred hblue n source
    (fun _ _ hp => hp) (eventuallyLocal_ground (Earlier hGCH) (restriction hGCH) _) p0 hstat
  obtain ⟨C, hC, ht⟩ := N.toClique.exists_clique_type
    (Erdos1172Part3TransfiniteHechlerClosure.full_countablyClosed hGCH) p0 (mk_index_le n)
  exact ⟨C, hC, ht.trans (typeLT_index n)⟩

theorem ordinalRamsey_positive_finite_power (hGCH : GCH) (n : ℕ) :
    OrdinalRamsey (ω_ 2 : Ordinal.{0}) ((ω_ 1) ^ (↑(n + 1) : Ordinal)) (ω_ 1 + 2) := by
  classical
  intro G H hcompl
  by_cases hblue : HasCliqueOfType H (ω_ 1 + 2)
  · exact Or.inr hblue
  by_cases hred : HasCliqueOfType G (ω_ 2)
  · obtain ⟨C, hC, htype⟩ := hred
    obtain ⟨D, hDC, hDtype⟩ := Ordinal.exists_subset_typeLT_eq C
      (show (ω_ 1 : Ordinal.{0}) ^ (↑(n + 1) : Ordinal) ≤ typeLT C by
        rw [htype]
        exact (finite_power_lt_omegaTwo (n + 1)).le)
    exact Or.inl ⟨D, hC.subset hDC, hDtype⟩
  · exact Or.inl (exists_ground_finite_core hGCH n G H hcompl hred hblue)

theorem ordinalRamsey_positive_finite_power_add_two (hGCH : GCH) (n : ℕ) :
    OrdinalRamsey (ω_ 2 : Ordinal.{0}) ((ω_ 1) ^ (↑(n + 1) : Ordinal) + 2) (ω_ 1 + 2) := by
  obtain hzero | ⟨e, he⟩ := Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.mp
    (isPrincipal_add_finite_power (n + 1))
  · exact ((finite_power_pos (n + 1)).ne' hzero).elim
  · change (ω : Ordinal.{0}) ^ e = (ω_ 1) ^ (↑(n + 1) : Ordinal) at he
    have hbound : ω ^ e + 2 ≤ ω_ 2 := by
      rw [he]
      exact finite_power_add_two_le_omegaTwo (n + 1)
    have hcore : OrdinalRamsey (ω_ 2 : Ordinal.{0}) (ω ^ e) (ω_ 1 + 2) := by
      rw [he]
      exact ordinalRamsey_positive_finite_power hGCH n
    simpa only [he] using ordinalRamsey_add_two_of_core hGCH e hbound hcore

theorem ordinalRamsey_finite_power_add_two (hGCH : GCH) (n : ℕ) :
    OrdinalRamsey (ω_ 2 : Ordinal.{0}) ((ω_ 1) ^ (↑n : Ordinal) + 2) (ω_ 1 + 2) := by
  cases n with
  | zero =>
    apply (ordinalRamsey_positive_finite_power_add_two hGCH 0).mono_targets _ le_rfl
    exact add_le_add (Ordinal.opow_le_opow_right
      (Ordinal.omega0_pos.trans_le (Ordinal.omega0_le_omega 1))
      (show (↑(0 : ℕ) : Ordinal.{0}) ≤ ↑(0 + 1 : ℕ) by norm_num)) le_rfl
  | succ n => exact ordinalRamsey_positive_finite_power_add_two hGCH n

theorem finite_target_lt_part3_target (n : ℕ) :
    (ω_ 1 : Ordinal.{0}) ^ (↑n : Ordinal) + 2 < (ω_ 1) ^ (ω + 2) + 2 := by
  have hk : (1 : Ordinal.{0}) < ω_ 1 :=
    Ordinal.one_lt_omega0.trans_le (Ordinal.omega0_le_omega 1)
  have hpow : (ω_ 1 : Ordinal.{0}) ^ (↑n : Ordinal) < (ω_ 1) ^ (ω + 2) :=
    (Ordinal.opow_lt_opow_iff_right hk).mpr ((Ordinal.natCast_lt_omega0 n).trans_le le_self_add)
  have hks : (ω_ 1 : Ordinal.{0}) ≤ (ω_ 1) ^ (ω + 2) := by
    simpa only [Ordinal.opow_one] using Ordinal.opow_le_opow_right (zero_lt_one.trans hk)
      (Ordinal.one_lt_omega0.le.trans le_self_add)
  exact (Ordinal.isPrincipal_add_opow_of_isPrincipal_add (Ordinal.isPrincipal_add_omega 1)
    (ω + 2) hpow ((Ordinal.natCast_lt_omega0 2).trans_le
      ((Ordinal.omega0_le_omega 1).trans hks))).trans_le le_self_add

end Erdos1172Part3FinitePowerRelations
