/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedDerivedStationaryLoss

@[expose] public section

/-!
# A constructed red core with stationary named trace losses

Guarded cores supply the trace family, including its decision origins.
Both derived-ideal branches then supply one positive row and stationary
small-loss future. An increasing-index red subsequence inherits the
losses in its own trace ideal. No initial core or ideal family is assumed.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedStationaryRedLoss

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularNamedIdeal (smallName)
open Erdos1172Part3GuardedRedCore (CoreData exists_club_guarded_red_cores_of_gch)
open Erdos1172Part3GuardedTraceFamily (priorSource base_small_to_trace prior_source_positive)
open Erdos1172Part3NamedTraceIdeal
open Erdos1172Part3NamedTraceSubsequence
open Erdos1172Part3RegularConeRestriction (onCone stationaryAt_onCone_iff)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3StationaryDecisions (possible StationaryAt stationaryAt_mono)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3NamedCenteredLoss (MonotoneSmallness)
open Erdos1172Part3TwoSuccessorBootstrap (stationary_inter_club)
open OrdinalRamsey (HasCliqueOfType)

variable {P : Type} [Preorder P] {G : SimpleGraph W2}

/-- The equality with a particular guarded trace name is retained, so
later positive-row extraction can reuse the same core's decision indices. -/
theorem exists_trace_family_with_origins (hGCH : GCH) (hP : #P ≤ ℵ_ 2)
    (hclosed : CountablyClosed P) (center : CountablyCenteredCode P)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) (source : RegularName P W2) :
    ∃ r : Code P W1 G ↪ W2, ∃ σ : NiceCliqueName P W1 W2 G ↪ W2,
      ∃ club : Set W2, ∃ J : W2 → RegularName P (RegularName P W2),
        IsClub club ∧ (∀ a, MonotoneSmallness (J a)) ∧
        ∀ a ∈ club, ErdosRadoCHAsym.IsOmegaOneSup a → (∃ p : P, source.holds p a) →
          GoodCut r σ H source a ∧ ∃ data : CoreData r H source a,
            J a = traceName data.name.toClique := by
  classical
  obtain ⟨r, σ, club, hclub, hcores⟩ := exists_club_guarded_red_cores_of_gch
    hGCH hP hclosed center G H hcompl hblue source
  let eligible : Set W2 := {a | a ∈ club ∧ ErdosRadoCHAsym.IsOmegaOneSup a ∧
    ∃ p : P, source.holds p a}
  let data (a : eligible) : CoreData r H source a.val :=
    Classical.choice ((hcores a.val a.property.1 a.property.2.1).2 a.property.2.2)
  let J (a : W2) : RegularName P (RegularName P W2) :=
    if ha : a ∈ eligible then traceName (data ⟨a, ha⟩).name.toClique else ground Set.univ
  refine ⟨r, σ, club, J, hclub, ?_, ?_⟩
  · intro a p U V hsub hV
    by_cases ha : a ∈ eligible
    · simp only [J, dif_pos ha] at hV ⊢
      exact traceName_mono (data ⟨a, ha⟩).name.toClique p U V hsub hV
    · simp only [J, dif_neg ha]
      trivial
  · intro a hac hasup hpossible
    let d : eligible := ⟨a, hac, hasup, hpossible⟩
    exact ⟨(hcores a hac hasup).1, data d, dif_pos d.property⟩

/-- The core is red and constructed from a stationary regular source.
There is no initial blue core, ideal family, or abstract extraction law
among the hypotheses. The conclusion is stationary small loss, not yet
a completely red-joined future. -/
theorem exists_stationary_red_trace_loss (hGCH : GCH) (hP : #P ≤ ℵ_ 2)
    (hclosed : CountablyClosed P) (center : CountablyCenteredCode P)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (source : RegularName P W2)
    (hsup : ∀ p a, source.holds p a → ErdosRadoCHAsym.IsOmegaOneSup a)
    (p0 : P) (hstat : StationaryAt source.holds p0) :
    ∃ a : W2, ∃ q : P, q ≤ p0 ∧ source.holds q a ∧
      ∃ next : CliqueDecisions (Set.Iic q) W1 W2 G,
        ∃ later : RegularName (Set.Iic q) W2,
          (∀ p i x, next.decides p i x → source.holds p.val x ∧ x < a ∧ G.Adj x a) ∧
          StationaryAt later.holds ⟨q, (show q ≤ q from le_rfl)⟩ ∧
          ∀ p b, later.holds p b → source.holds p.val b ∧ a < b ∧
            (traceName next).holds p (ground {x | H.Adj x b}) := by
  obtain ⟨r, σ, club, J, hclub, hmono, hcuts⟩ := exists_trace_family_with_origins
    hGCH hP hclosed center G H hcompl hblue source
  let D := meet source (ground club)
  have hat (a : W2) (p : P) (hp : D.holds p a) :
      GoodCut r σ H source a ∧ ∃ data : CoreData r H source a, J a = traceName data.name.toClique :=
    hcuts a hp.2 (hsup p a hp.1) ⟨p, hp.1⟩
  have hbase (a : W2) (p : P) (hp : D.holds p a) (U : RegularName P W2)
      (hU : (smallName r H a).holds p U) : (J a).holds p U := by
    obtain ⟨ha, data, hJ⟩ := hat a p hp
    rw [hJ]
    exact base_small_to_trace data ha p hp.1 U hU
  have hpositive (a : W2) (p : P) (hp : D.holds p a) :
      (neg (J a)).holds p (priorSource source a) := by
    obtain ⟨ha, data, hJ⟩ := hat a p hp
    rw [hJ]
    exact prior_source_positive data p hp.1
  have hDstat : StationaryAt D.holds p0 := by
    intro p hpp0
    apply (stationary_inter_club (hstat p hpp0) hclub).mono
    rintro b ⟨⟨q, hqp, hqb⟩, hbc⟩
    exact ⟨q, hqp, hqb, hbc⟩
  obtain ⟨a, p, hpp0, hDp, X, out, hXsub, hXpos, hout, hloss⟩ :=
    Erdos1172Part3NamedDerivedStationaryLoss.exists_positive_stationary_loss hGCH.toCH
      center hclosed r σ H hcompl source D J hmono (fun a p hp => (hat a p hp).1)
      hbase hpositive p0 hDstat hred hblue
  obtain ⟨ha, data, hJ⟩ := hat a p hDp
  rw [hJ] at hXpos
  obtain ⟨q, hqp, next, hnext⟩ := exists_cone_subsequence hclosed data.name.toClique p X
    (hXpos p le_rfl)
  let later := onCone q out
  have hlater : StationaryAt later.holds ⟨q, (show q ≤ q from le_rfl)⟩ :=
    (stationaryAt_onCone_iff q out ⟨q, (show q ≤ q from le_rfl)⟩).mpr
      (stationaryAt_mono hout hqp)
  refine ⟨a, q, hqp.trans hpp0, source.persistent hqp hDp.1, next, later, ?_, hlater, ?_⟩
  · intro s i x hx
    obtain ⟨j, hij, hdec⟩ := (hnext s i x hx).2
    exact ⟨(hXsub s.val x (hnext s i x hx).1).1, data.geometry s.val j x hdec⟩
  · intro s b hs
    have h := hloss s.val b hs
    refine ⟨h.1.1, h.2.1, ?_⟩
    have hsmall := h.2.2
    rw [hJ] at hsmall
    have htransfer := traceName_transfer data.name.toClique q next
      (fun p i x hx => (hnext p i x hx).2) s (meet X (ground {x | H.Adj x b})) hsmall
    apply traceName_mono_on_decisions next s (ground {x | H.Adj x b})
      (onCone q (meet X (ground {x | H.Adj x b}))) ?_ htransfer
    intro t hts i x hx hHxb
    exact ⟨(hnext t i x hx).1, hHxb⟩

end Erdos1172Part3NamedStationaryRedLoss
