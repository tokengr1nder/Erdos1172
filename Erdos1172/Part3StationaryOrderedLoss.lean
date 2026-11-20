/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3OrderedCoreTrace
public import Erdos1172.Part3OmegaSuccessorCore
public import Erdos1172.Part3NamedDerivedStationaryLoss

@[expose] public section

/-!
# Stationary losses small in the actual ordered core trace

The constructed omega-successor product supplies a regular ordered trace.
Its full-row convergence sends every base-small neighborhood into that
trace, while actual source membership makes the prior source positive.
These proved laws instantiate the derived stationary-loss theorem.

The final theorem uses the previously constructed club of guarded
omega-successor cores. No core factory or weak-trace-to-order-smallness
implication is assumed. Positivity of the selected source and hereditary
ordered smallness of every displayed loss hold at actual conditions.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3StationaryOrderedLoss

open ErdosRadoCHAsym (W1 W2 IsOmegaOneSup)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularNamedIdeal (smallName)
open Erdos1172Part3RankedCoreBlockAssembly (GoodCoreCut)
open Erdos1172Part3ControlledCoreProducts (ProductData)
open Erdos1172Part3OrderedCoreTrace
  (trace trace_mono base_small_to_ordered_trace prior_source_ordered_positive)
open Erdos1172Part3GuardedTraceFamily (priorSource)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3StationaryDecisions (StationaryAt)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3NamedCenteredLoss (MonotoneSmallness)
open Erdos1172Part3NamedBlueDerivedIdeal (fiber)
open Erdos1172Part3TwoSuccessorBootstrap (stationary_inter_club)
open Erdos1172Part3OmegaPowerIndex (OmegaIndex mk_omegaIndex_le)
open OrdinalRamsey (HasCliqueOfType)

variable {P : Type} [Preorder P] {G H : SimpleGraph W2}
variable {r : Code P OmegaIndex G ↪ W2}
  {σ : NiceCliqueName P OmegaIndex W2 G ↪ W2}
variable {source : RegularName P W2}

/-- Choose a coherent regular trace family on all cuts. Only eligible
cuts use a core; the unused cuts receive the all-small regular family. -/
theorem exists_ordered_trace_family (club : Set W2)
    (hcores : ∀ a ∈ club, IsOmegaOneSup a → GoodCoreCut r σ H source a ∧
      ((∃ p : P, source.holds p a) → Nonempty (ProductData r H source a))) :
    ∃ J : W2 → RegularName P (RegularName P W2),
      (∀ a, MonotoneSmallness (J a)) ∧
      ∀ a ∈ club, IsOmegaOneSup a → (∃ p : P, source.holds p a) →
        GoodCut r σ H source a ∧ ∃ data : ProductData r H source a,
          J a = trace data.name.toClique := by
  classical
  let eligible : Set W2 := {a | a ∈ club ∧ IsOmegaOneSup a ∧ ∃ p : P, source.holds p a}
  let data (a : eligible) : ProductData r H source a.val :=
    Classical.choice ((hcores a.val a.property.1 a.property.2.1).2 a.property.2.2)
  let J (a : W2) : RegularName P (RegularName P W2) :=
    if ha : a ∈ eligible then trace (data ⟨a, ha⟩).name.toClique else ground Set.univ
  refine ⟨J, ?_, ?_⟩
  · intro a p U V hsub hV
    by_cases ha : a ∈ eligible
    · simp only [J, dif_pos ha] at hV ⊢
      exact trace_mono (data ⟨a, ha⟩).name.toClique p U V hsub hV
    · simp only [J, dif_neg ha]
      trivial
  · intro a hac hsa hp
    let d : eligible := ⟨a, hac, hsa, hp⟩
    exact ⟨(hcores a hac hsa).1.goodCut, data d, dif_pos d.property⟩

/-- The actual ordered trace satisfies all the derived-loss hypotheses.
The selected source is positive at the same condition where the future
is stationary, and every actual future member has ordered-small loss. -/
theorem exists_positive_stationary_ordered_loss (hCH : CH)
    (center : CountablyCenteredCode P) (hclosed : CountablyClosed P)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (r : Code P OmegaIndex G ↪ W2) (σ : NiceCliqueName P OmegaIndex W2 G ↪ W2)
    (source : RegularName P W2) (hsup : ∀ p a, source.holds p a → IsOmegaOneSup a)
    (club : Set W2) (hclub : IsClub club)
    (hcores : ∀ a ∈ club, IsOmegaOneSup a → GoodCoreCut r σ H source a ∧
      ((∃ p : P, source.holds p a) → Nonempty (ProductData r H source a)))
    (p0 : P) (hstat : StationaryAt source.holds p0) :
    ∃ a : W2, ∃ q : P, q ≤ p0 ∧ source.holds q a ∧
      ∃ data : ProductData r H source a, ∃ X out : RegularName P W2,
        (∀ p x, X.holds p x → source.holds p x ∧ x < a) ∧
        (neg (trace data.name.toClique)).holds q X ∧ StationaryAt out.holds q ∧
        ∀ p b, out.holds p b → source.holds p b ∧ a < b ∧
          (trace data.name.toClique).holds p (fiber H b X) := by
  obtain ⟨J, hmono, hcuts⟩ := exists_ordered_trace_family club hcores
  let D := meet source (ground club)
  have hat (a : W2) (p : P) (hp : D.holds p a) :
      GoodCut r σ H source a ∧ ∃ data : ProductData r H source a,
        J a = trace data.name.toClique :=
    hcuts a hp.2 (hsup p a hp.1) ⟨p, hp.1⟩
  have hbase (a : W2) (p : P) (hp : D.holds p a) (U : RegularName P W2)
      (hU : (smallName r H a).holds p U) : (J a).holds p U := by
    obtain ⟨ha, data, hJ⟩ := hat a p hp
    rw [hJ]
    exact base_small_to_ordered_trace hclosed data ha p hp.1 U hU
  have hpositive (a : W2) (p : P) (hp : D.holds p a) :
      (neg (J a)).holds p (priorSource source a) := by
    obtain ⟨_, data, hJ⟩ := hat a p hp
    rw [hJ]
    exact prior_source_ordered_positive data p hp.1
  have hDstat : StationaryAt D.holds p0 := by
    intro p hpp0
    apply (stationary_inter_club (hstat p hpp0) hclub).mono
    rintro b ⟨⟨q, hqp, hqb⟩, hbc⟩
    exact ⟨q, hqp, hqb, hbc⟩
  obtain ⟨a, q, hqp0, hDq, X, out, hXsub, hXpos, hout, hloss⟩ :=
    Erdos1172Part3NamedDerivedStationaryLoss.exists_positive_stationary_loss_general
      hCH mk_omegaIndex_le center hclosed r σ H hcompl source D J hmono
      (fun a p hp => (hat a p hp).1) hbase hpositive p0 hDstat hred hblue
  obtain ⟨_, data, hJ⟩ := hat a q hDq
  refine ⟨a, q, hqp0, hDq.1, data, X, out, hXsub, ?_, hout, ?_⟩
  · rwa [← hJ]
  · intro p b hp
    have h := hloss p b hp
    exact ⟨h.1.1, h.2.1, by rw [← hJ]; exact h.2.2⟩

open Erdos1172Part3TransfiniteStageLocality (Full Earlier restriction)
open Erdos1172Part3TransfiniteHechlerOrder (mk_stage_le)
open Erdos1172Part3RegularStageLocality (EventuallyLocal)
open Erdos1172Part3OmegaSuccessorCore (exists_club_guarded_omega_successor)

/-- Fully instantiate the stationary ordered-loss construction in the
concrete full iteration. The required guarded cores are constructed,
not assumed through a core-factory hypothesis. -/
theorem exists_positive_stationary_omega_ordered_loss (hGCH : GCH)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (source : RegularName (Full hGCH) W2)
    (hsup : ∀ p a, source.holds p a → IsOmegaOneSup a)
    (hlocal : EventuallyLocal (Earlier hGCH) (restriction hGCH) source)
    (p0 : Full hGCH) (hstat : StationaryAt source.holds p0) :
    let r := rank hGCH (mk_stage_le hGCH ⊤) mk_omegaIndex_le G
    ∃ a : W2, ∃ q : Full hGCH, q ≤ p0 ∧ source.holds q a ∧
      ∃ data : ProductData r H source a, ∃ X out : RegularName (Full hGCH) W2,
        (∀ p x, X.holds p x → source.holds p x ∧ x < a) ∧
        (neg (trace data.name.toClique)).holds q X ∧ StationaryAt out.holds q ∧
        ∀ p b, out.holds p b → source.holds p b ∧ a < b ∧
          (trace data.name.toClique).holds p (fiber H b X) := by
  obtain ⟨club, hclub, hc⟩ := exists_club_guarded_omega_successor
    hGCH G H hcompl hred hblue source hsup hlocal
  exact exists_positive_stationary_ordered_loss hGCH.toCH
    (Erdos1172Part3TransfiniteHechlerCentering.centered hGCH ⊤)
    (Erdos1172Part3TransfiniteHechlerClosure.full_countablyClosed hGCH)
    G H hcompl hred hblue
    (rank hGCH (mk_stage_le hGCH ⊤) mk_omegaIndex_le G)
    (blockRank hGCH (mk_stage_le hGCH ⊤) mk_omegaIndex_le G)
    source hsup club hclub hc p0 hstat

end Erdos1172Part3StationaryOrderedLoss
