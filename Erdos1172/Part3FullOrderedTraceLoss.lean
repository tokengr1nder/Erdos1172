/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3StationaryOrderedLoss
public import Erdos1172.Part3OrderedCoreExtraction
public import Erdos1172.Part3OrderedTraceRestriction

@[expose] public section

/-!
# Global ordered trace losses and exact stage localization

Actual positivity for the hereditary ordered trace yields a full selected
subcore retaining every original small loss. Cone globalization and nice
normalization preserve its whole trace on the selected cone.

The resulting source, nice omega-successor core, and stationary trace
future factor through one earlier stage of the concrete full iteration.
Both condition orders are countably closed, so the exact ordered-trace
restriction theorem applies to the full omega-successor index.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3FullOrderedTraceLoss

open ErdosRadoCHAsym (W1 W2 IsOmegaOneSup)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularConeRestriction (onCone)
open Erdos1172Part3ClosedDecisionSystem (CliqueDecisions CountablyClosed)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName exists_nice_clique_name)
open Erdos1172Part3OmegaSuccessorCore (OmegaSuccessor mk_omegaSuccessor_le)
open Erdos1172Part3ExactOmegaIndex (typeLT_omegaSuccessor)
open Erdos1172Part3OrderedCoreTrace (trace trace_mono_on_decisions)
open Erdos1172Part3OrderedTraceRestriction (trace_lift_iff trace_of_onCone_refines)
open Erdos1172Part3CompleteRestriction (CompleteRestriction)
open Erdos1172Part3TraceCompleteRestriction (SameDecisions)
open Erdos1172Part3TransfiniteStageLocality (Full Earlier restriction exists_name_restriction)
open Erdos1172Part3RegularStageLocality (EventuallyLocal)
open Erdos1172Part3StationaryDecisions (StationaryAt)
open Erdos1172Part3NamedBlueDerivedIdeal (fiber)
open OrdinalRamsey (HasCliqueOfType)

variable {P Q : Type} [Preorder P] [Preorder Q] {G : SimpleGraph W2}

/-- Future source points whose blue neighborhood is hereditarily
order-small in the selected full omega-successor core. -/
noncomputable def traceFuture (source : RegularName P W2)
    (core : CliqueDecisions P OmegaSuccessor W2 G) (H : SimpleGraph W2) (a : W2) :
    RegularName P W2 :=
  meet source (meet (ground {b | a < b})
    (reindex (trace core) (fun b => ground {x | H.Adj x b})))

/-- The trace future is read exactly at an earlier complete restriction,
using the actual closure of both orders and the exact full index type. -/
theorem traceFuture_lift (r : CompleteRestriction P Q)
    (full : CliqueDecisions P OmegaSuccessor W2 G)
    (earlier : CliqueDecisions Q OmegaSuccessor W2 G)
    (hdec : SameDecisions r full earlier)
    (hclosedP : CountablyClosed P) (hclosedQ : CountablyClosed Q)
    (source : RegularName Q W2) (H : SimpleGraph W2) (a : W2) :
    r.liftRegular (traceFuture source earlier H a) =
      traceFuture (r.liftRegular source) full H a := by
  apply RegularName.ext
  intro p b
  exact (and_congr Iff.rfl (and_congr Iff.rfl
    (trace_lift_iff r full earlier hdec hclosedP hclosedQ
      mk_omegaSuccessor_le typeLT_omegaSuccessor p (ground {x | H.Adj x b})))).symm

/-- Construct a global nice full core with stationary actual ordered
losses. Neither a core factory nor an ordered-smallness transfer premise
is assumed: both are supplied by the constructed preceding theorems. -/
theorem exists_global_ordered_trace_loss (hGCH : GCH)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (source : RegularName (Full hGCH) W2)
    (hsup : ∀ p a, source.holds p a → IsOmegaOneSup a)
    (hlocal : EventuallyLocal (Earlier hGCH) (restriction hGCH) source)
    (p0 : Full hGCH) (hstat : StationaryAt source.holds p0) :
    ∃ a : W2, ∃ q : Full hGCH, q ≤ p0 ∧ source.holds q a ∧
      ∃ N : NiceCliqueName (Full hGCH) OmegaSuccessor W2 G,
        (∀ p z x, N.toClique.decides p z x → x < a ∧ G.Adj x a) ∧
        (∀ p : Full hGCH, p ≤ q → ∀ z x, N.toClique.decides p z x → source.holds p x) ∧
        StationaryAt (traceFuture source N.toClique H a).holds q := by
  obtain ⟨a, q, hqp0, hcut, data, X, out, hXsub, hXpos, hout, hloss⟩ :=
    Erdos1172Part3StationaryOrderedLoss.exists_positive_stationary_omega_ordered_loss
      hGCH G H hcompl hred hblue source hsup hlocal p0 hstat
  obtain ⟨start, hstart, sub, hmember, htransfer⟩ :=
    Erdos1172Part3OrderedCoreExtraction.exists_full_subcore data.name.toClique q X hXpos
  obtain ⟨global, hbelow, horigin⟩ :=
    Erdos1172Part3CliqueConeExtension.exists_global_clique_from_cone
      (Erdos1172Part3TransfiniteHechlerClosure.full_countablyClosed hGCH)
      start sub mk_omegaSuccessor_le
  obtain ⟨N, hN⟩ := exists_nice_clique_name
    (Erdos1172Part3TransfiniteHechlerCentering.omegaTwoCC hGCH ⊤) global
  have hNbelow (p : Set.Iic start) (z : OmegaSuccessor) (x : W2)
      (hx : N.toClique.decides p.val z x) : sub.decides p z x :=
    (hbelow p.val p.property z x).mp (hN p.val z x hx)
  refine ⟨a, start, hstart.trans hqp0, source.persistent hstart hcut, N, ?_, ?_, ?_⟩
  · intro p z x hx
    obtain ⟨s, hs⟩ := horigin p z x (hN p z x hx)
    obtain ⟨_, old, hdec⟩ := hmember s z x hs
    exact data.geometry s.val old x hdec
  · intro p hpstart z x hx
    exact (hXsub p x (hmember ⟨p, hpstart⟩ z x (hNbelow ⟨p, hpstart⟩ z x hx)).1).1
  · intro p hpstart
    apply (hout p (hpstart.trans hstart)).mono
    rintro b ⟨s, hsp, hs⟩
    have hb := hloss s b hs
    let t : Set.Iic start := ⟨s, hsp.trans hpstart⟩
    have htrans := htransfer t (fiber H b X) hb.2.2
    have hsmall : (trace sub).holds t (onCone start (ground {x | H.Adj x b})) := by
      apply trace_mono_on_decisions sub ?_ htrans
      intro v hvt z x hx hHxb
      exact ⟨(hmember v z x hx).1, hHxb⟩
    exact ⟨s, hsp, hb.1, hb.2.1,
      trace_of_onCone_refines start sub N.toClique hNbelow t (ground {x | H.Adj x b}) hsmall⟩

/-- A common actual earlier stage reads the source, every core decision,
and the complete ordered-trace future exactly. -/
theorem exists_ordered_trace_restriction (hGCH : GCH) {G : SimpleGraph W2}
    (source : RegularName (Full hGCH) W2)
    (hlocal : EventuallyLocal (Earlier hGCH) (restriction hGCH) source)
    (N : NiceCliqueName (Full hGCH) OmegaSuccessor W2 G) (H : SimpleGraph W2) (a : W2) :
    ∃ b : W2, ∃ V : RegularName (Earlier hGCH b) W2,
      ∃ M : NiceCliqueName (Earlier hGCH b) OmegaSuccessor W2 G,
        (restriction hGCH b).liftRegular V = source ∧
        SameDecisions (restriction hGCH b) N.toClique M.toClique ∧
        (restriction hGCH b).liftRegular (traceFuture V M.toClique H a) =
          traceFuture source N.toClique H a := by
  obtain ⟨nameBound, hname⟩ := exists_name_restriction hGCH N mk_omegaSuccessor_le
  obtain ⟨sourceBound, hsource⟩ := hlocal
  let b := max nameBound sourceBound
  obtain ⟨M, hM⟩ := hname b (le_max_left _ _)
  obtain ⟨V, hV⟩ := hsource b (le_max_right _ _)
  have hdec : SameDecisions (restriction hGCH b) N.toClique M.toClique :=
    fun p z x => (hM p z x).symm
  refine ⟨b, V, M, hV, hdec, ?_⟩
  rw [traceFuture_lift (restriction hGCH b) N.toClique M.toClique hdec
    (Erdos1172Part3TransfiniteHechlerClosure.full_countablyClosed hGCH)
    (Erdos1172Part3TransfiniteHechlerClosure.countablyClosed hGCH (b : WithTop W2)) V H a, hV]

end Erdos1172Part3FullOrderedTraceLoss
