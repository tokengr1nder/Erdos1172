/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CountableHechlerLimitClosure

@[expose] public section

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3CountableHechlerLimitCentering

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3FiniteHechlerStages (stage)
open Erdos1172Part3CountableHechlerLimit
open Erdos1172Part3PrescribedBaseFusion
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)

variable {hGCH : GCH}

noncomputable def profile (p : Limit hGCH) : ℕ → W1 :=
  fun n => (stage hGCH n).centered.code (p.point n)

noncomputable def profileRank (hCH : CH) : (ℕ → W1) ↪ W1 := by
  apply Classical.choice
  apply (Cardinal.le_def _ _).mp
  simp only [Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.mk_nat, W1,
    Cardinal.mk_toType, Ordinal.card_omega, hCH.aleph_one_power_aleph_zero, le_refl]

/-- Countably many finite-stage centers form one omegaOne-sized profile
space under CH. Lower bounds for a fixed profile are fused with exact
base agreement, just as for chains. -/
noncomputable def centered : CountablyCenteredCode (Limit hGCH) where
  code p := profileRank hGCH.toCH (profile p)
  lower := by
    intro C hC value hvalue
    by_cases hne : C.Nonempty
    · obtain ⟨p0, hp0⟩ := hne
      have hprofiles : ∀ p ∈ C, ∀ n : ℕ,
          (stage hGCH n).centered.code (p.point n) =
            (stage hGCH n).centered.code (p0.point n) := by
        intro p hp n
        have heq := (profileRank hGCH.toCH).injective
          ((hvalue p hp).trans (hvalue p0 hp0).symm)
        exact congrFun heq n
      obtain ⟨first, hfirst⟩ := (stage hGCH 0).centered.lower ((atMap 0) '' C)
        (hC.image (atMap 0)) ((stage hGCH 0).centered.code (p0.point 0)) (by
          rintro _ ⟨p, hp, rfl⟩
          exact hprofiles p hp 0)
      obtain ⟨q, _, hq⟩ := exists_limit_starting_with
        (fun n p => ∀ c ∈ C, p ≤ c.point n) first
        (fun c hc => hfirst (c.point 0) ⟨c, hc, rfl⟩) (by
          intro n p hp
          have hstem : ∀ r ∈ (atMap (n + 1)) '' C,
              r.stem = (p0.point (n + 1)).stem := by
            rintro _ ⟨c, hc, rfl⟩
            exact same_stem_of_extend_code_eq (stage hGCH n).centered hGCH.toCH
              (hprofiles c hc (n + 1))
          have hbase : ∀ r ∈ (atMap (n + 1)) '' C, p ≤ r.base := by
            rintro _ ⟨c, hc, rfl⟩
            change p ≤ (c.point (n + 1)).base
            rw [c.coherent n]
            exact hp c hc
          obtain ⟨r, hrbase, hrlower⟩ := exists_same_stem_lower_with_base
            (p0.point (n + 1)) ((atMap (n + 1)) '' C)
            (hC.image (atMap (n + 1))) hstem p hbase
          exact ⟨r, hrbase, fun c hc => hrlower (c.point (n + 1)) ⟨c, hc, rfl⟩⟩)
      exact ⟨q, fun c hc n => hq n c hc⟩
    · exact ⟨default, fun _ hp => (hne ⟨_, hp⟩).elim⟩

theorem omegaTwoCC : Erdos1172Part3StationaryDecisions.OmegaTwoCC (Limit hGCH) :=
  centered.omegaTwoCC

end Erdos1172Part3CountableHechlerLimitCentering
