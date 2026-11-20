/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedBlueDerivedIdeal

@[expose] public section

/-!
# Pulling named derived losses back to one earlier positive trace

The earlier cut, its positive trace, and its stationary future are
selected at one common condition. All membership predicates remain
regular names; only the earlier-cut index is frozen on a stationary set.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedDerivedLoss

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularNamedIdeal (smallName)
open Erdos1172Part3NamedBlueDerivedIdeal
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3StationaryDecisions (possible StationaryAt exists_stationary_refinement)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3NamedCenteredLoss (MonotoneSmallness)
open OrdinalRamsey (HasCliqueOfType)

variable {P I : Type} [Preorder P] [LinearOrder I] {G H : SimpleGraph W2}
variable {r : Code P I G ↪ W2} {σ : NiceCliqueName P I W2 G ↪ W2}
variable {source : RegularName P W2} {a : W2}

theorem exists_actual_earlier_loss (hclosed : CountablyClosed P)
    (ha : GoodCut r σ H source a) (D : RegularName P W2)
    (J : W2 → RegularName P (RegularName P W2)) (U : RegularName P W2) (p : P)
    (hU : (neg (blueSmallName r H D J a)).holds p U) (c : W2)
    (hloss : (blueSmallName r H D J a).holds p (fiber H c U)) :
    ∃ q : P, q ≤ p ∧ ∃ b : W2, b < a ∧ D.holds q b ∧
      (neg (J b)).holds q (blueSection H a b U) ∧
      (J b).holds q (fiber H c (blueSection H a b U)) := by
  obtain ⟨q, hqp, b, hba, hb, hnot, _⟩ :=
    Erdos1172Part3NamedAvoidance.exists_actual_extension_avoiding hclosed ha false
      (support H D J a U) (support H D J a (fiber H c U)) p hU hloss
      ∅ Set.countable_empty (Set.empty_subset _) (by simp)
  have hsmall : (J b).holds q (blueSection H a b (fiber H c U)) := by
    have hnegneg : (neg (neg (J b))).holds q (blueSection H a b (fiber H c U)) := by
      intro s hsq hs
      exact hnot s hsq ⟨hba, D.persistent hsq hb.2.1, hs⟩
    rwa [Erdos1172Part3RegularMembership.neg_neg] at hnegneg
  rw [blueSection_fiber_comm] at hsmall
  exact ⟨q, hqp, b, hba, hb.2.1, hb.2.2, hsmall⟩

noncomputable def earlierFuture (H : SimpleGraph W2) (D : RegularName P W2)
    (J : W2 → RegularName P (RegularName P W2)) (a : W2)
    (U future : RegularName P W2) (b : W2) : RegularName P W2 :=
  meet future (meet (reindex D (fun _ => b))
    (meet (reindex (neg (J b)) (fun _ => blueSection H a b U))
      (reindex (J b) (fun c => fiber H c (blueSection H a b U)))))

theorem exists_earlier_positive_loss (center : CountablyCenteredCode P)
    (hclosed : CountablyClosed P) (ha : GoodCut r σ H source a)
    (D : RegularName P W2) (J : W2 → RegularName P (RegularName P W2))
    (U future : RegularName P W2) (p0 : P)
    (hU : (neg (blueSmallName r H D J a)).holds p0 U)
    (hfuture : IsStationary (possible future.holds p0))
    (hloss : ∀ q c, future.holds q c → (blueSmallName r H D J a).holds q (fiber H c U)) :
    ∃ b : W2, b < a ∧ ∃ p : P, p ≤ p0 ∧ D.holds p b ∧
      (neg (J b)).holds p (blueSection H a b U) ∧ ∃ out : RegularName P W2,
        StationaryAt out.holds p ∧ ∀ q c, out.holds q c →
          future.holds q c ∧ (J b).holds q (fiber H c (blueSection H a b U)) := by
  classical
  let S := possible future.holds p0
  have witness (c : S) : ∃ b : Set.Iio a, ∃ q : P, q ≤ p0 ∧
      (earlierFuture H D J a U future b.val).holds q c.val := by
    obtain ⟨q, hqp0, hqc⟩ := c.property
    obtain ⟨s, hsq, b, hba, hb, hpositive, hsmall⟩ := exists_actual_earlier_loss
      hclosed ha D J U q ((neg (blueSmallName r H D J a)).persistent hqp0 hU)
      c.val (hloss q c.val hqc)
    exact ⟨⟨b, hba⟩, s, hsq.trans hqp0, future.persistent hsq hqc, hb, hpositive, hsmall⟩
  let chosen (c : S) : Set.Iio a := (witness c).choose
  have hsmall : #(Set.Iio a) < ℵ_ 2 := by
    simpa only [W2, Cardinal.mk_toType, Ordinal.card_omega] using
      Cardinal.mk_Iio_lt a (Cardinal.ord_cardinalMk (α := W2))
  obtain ⟨b, hb⟩ := Erdos1172Part3CenteredStationaryLoss.exists_stationary_fiber_of_small
    hsmall hfuture chosen
  let out := earlierFuture H D J a U future b.val
  have hout : IsStationary (possible out.holds p0) := by
    apply hb.mono
    rintro c ⟨hc, heq⟩
    obtain ⟨q, hqp0, hq⟩ := (witness ⟨c, hc⟩).choose_spec
    have hval : (witness ⟨c, hc⟩).choose.val = b.val := congrArg Subtype.val heq
    rw [hval] at hq
    exact ⟨q, hqp0, hq⟩
  obtain ⟨p, hpp0, hp⟩ := exists_stationary_refinement center.omegaTwoCC out.holds
    (fun hqp h => out.persistent hqp h) p0 hout
  have hDp : D.holds p b.val := by
    apply D.of_dense p b.val
    intro q hqp
    obtain ⟨c, s, hsq, hs⟩ := (hp q hqp).nonempty
    exact ⟨s, hsq, hs.2.1⟩
  have hpos : (neg (J b.val)).holds p (blueSection H a b.val U) := by
    apply (neg (J b.val)).of_dense p (blueSection H a b.val U)
    intro q hqp
    obtain ⟨c, s, hsq, hs⟩ := (hp q hqp).nonempty
    exact ⟨s, hsq, hs.2.2.1⟩
  exact ⟨b.val, b.property, p, hpp0, hDp, hpos, out, hp,
    fun q c hq => ⟨hq.1, hq.2.2.2⟩⟩

end Erdos1172Part3NamedDerivedLoss
