/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedDerivedDiagonal

@[expose] public section

/-!
# Both derived-ideal branches give the same named stationary loss

The displayed regular-family laws suffice. In the proper-derived branch
blue extraction is proved, not assumed; in the all-small branch the
condition-dependent diagonal-reflection theorem applies. The selected
row stays positive at the same condition as the stationary future.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedDerivedStationaryLoss

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularNamedIdeal (smallName)
open Erdos1172Part3GuardedTraceFamily (priorSource)
open Erdos1172Part3NamedBlueDerivedIdeal
open Erdos1172Part3NamedDerivedDiagonal (cutFuture exists_loss_of_all_blueSmall_general)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3StationaryDecisions (possible StationaryAt)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3NamedCenteredLoss (MonotoneSmallness)
open Erdos1172Part3NeighborhoodCode (alephZero_lt_cof_W2)
open Erdos1172Part3TwoSuccessorBootstrap (stationary_inter_club)
open OrdinalRamsey (HasCliqueOfType)

variable {P I : Type} [Preorder P] [LinearOrder I] {G : SimpleGraph W2}

theorem exists_positive_stationary_loss_general (hCH : CH) (hI : #I ≤ ℵ_ 1)
    (center : CountablyCenteredCode P) (hclosed : CountablyClosed P) (r : Code P I G ↪ W2)
    (σ : NiceCliqueName P I W2 G ↪ W2) (H : SimpleGraph W2) (hcompl : IsCompl G H)
    (source D : RegularName P W2) (J : W2 → RegularName P (RegularName P W2))
    (hmono : ∀ b, MonotoneSmallness (J b))
    (hgood : ∀ a p, D.holds p a → GoodCut r σ H source a)
    (hbase : ∀ b p, D.holds p b → ∀ U : RegularName P W2,
      (smallName r H b).holds p U → (J b).holds p U)
    (hpositive : ∀ a p, D.holds p a → (neg (J a)).holds p (priorSource source a))
    (p0 : P) (hstat : StationaryAt D.holds p0)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) :
    ∃ a : W2, ∃ p : P, p ≤ p0 ∧ D.holds p a ∧ ∃ X out : RegularName P W2,
      (∀ q x, X.holds q x → source.holds q x ∧ x < a) ∧
      (neg (J a)).holds p X ∧ StationaryAt out.holds p ∧
      ∀ q b, out.holds q b → D.holds q b ∧ a < b ∧ (J a).holds q (fiber H b X) := by
  classical
  by_cases hext : ∀ a p, p ≤ p0 → D.holds p a →
      (blueSmallName r H D J a).holds p (priorSource source a)
  · obtain ⟨a, p, hpp0, hDa, hf⟩ := exists_loss_of_all_blueSmall_general hCH center.omegaTwoCC hI
      r σ H source D J hmono (fun p a ha => (hgood a p ha).isOmegaOneSup) p0 hstat hext
    exact ⟨a, p, hpp0, hDa, priorSource source a, cutFuture H D J source a,
      fun q x hx => hx, hpositive a p hDa, hf, fun q b hb => hb⟩
  · push Not at hext
    obtain ⟨a, p, hpp0, hDa, hnot⟩ := hext
    have ha := hgood a p hDa
    obtain ⟨q, hqp, hq⟩ :=
      (not_holds_iff_exists_neg (blueSmallName r H D J a) p (priorSource source a)).mp hnot
    let rows := priorSource source a
    let future := meet D (ground {b | a < b})
    have hfuture : IsStationary (possible future.holds q) := by
      apply (stationary_inter_club (hstat q (hqp.trans hpp0))
        (Set.isClub_Ioi_of_aleph0_lt_cof alephZero_lt_cof_W2 a)).mono
      rintro b ⟨⟨s, hsq, hs⟩, hab⟩
      exact ⟨s, hsq, hs, hab⟩
    obtain ⟨t, htq, X, out, hXsub, hXpos, hout, hloss⟩ :=
      Erdos1172Part3NamedCenteredLoss.exists_stationary_small_loss center
        (blueSmallName r H D J a) (blueSmall_mono D J hmono)
        G H hcompl rows future q a (fun p hp x hx => hx.2) (fun p hp b hb => hb.2)
        hq hfuture hred hblue (blueExtraction_derived hclosed ha D J hbase rows q)
    obtain ⟨b, hba, v, hvt, hDb, hbpos, final, hfinal, hfinalLoss⟩ :=
      Erdos1172Part3NamedDerivedLoss.exists_earlier_positive_loss center hclosed ha
        D J X out t hXpos (hout t le_rfl) (fun q c hc => (hloss q c hc).2)
    refine ⟨b, v, ((hvt.trans htq).trans hqp).trans hpp0, hDb,
      blueSection H a b X, final, ?_, hbpos, hfinal, ?_⟩
    · intro s x hx
      exact ⟨(hXsub s x hx.1).1, hx.2.2⟩
    · intro s c hc
      have h := (hloss s c (hfinalLoss s c hc).1).1
      exact ⟨h.1, hba.trans h.2, (hfinalLoss s c hc).2⟩

theorem exists_positive_stationary_loss (hCH : CH) (center : CountablyCenteredCode P)
    (hclosed : CountablyClosed P) (r : Code P W1 G ↪ W2)
    (σ : NiceCliqueName P W1 W2 G ↪ W2) (H : SimpleGraph W2) (hcompl : IsCompl G H)
    (source D : RegularName P W2) (J : W2 → RegularName P (RegularName P W2))
    (hmono : ∀ b, MonotoneSmallness (J b))
    (hgood : ∀ a p, D.holds p a → GoodCut r σ H source a)
    (hbase : ∀ b p, D.holds p b → ∀ U : RegularName P W2,
      (smallName r H b).holds p U → (J b).holds p U)
    (hpositive : ∀ a p, D.holds p a → (neg (J a)).holds p (priorSource source a))
    (p0 : P) (hstat : StationaryAt D.holds p0)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) :
    ∃ a : W2, ∃ p : P, p ≤ p0 ∧ D.holds p a ∧ ∃ X out : RegularName P W2,
      (∀ q x, X.holds q x → source.holds q x ∧ x < a) ∧
      (neg (J a)).holds p X ∧ StationaryAt out.holds p ∧
      ∀ q b, out.holds q b → D.holds q b ∧ a < b ∧ (J a).holds q (fiber H b X) :=
  exists_positive_stationary_loss_general hCH
    (by simp only [W1, Cardinal.mk_toType, Ordinal.card_omega, le_refl])
    center hclosed r σ H hcompl source D J hmono hgood hbase hpositive p0 hstat hred hblue

end Erdos1172Part3NamedDerivedStationaryLoss
