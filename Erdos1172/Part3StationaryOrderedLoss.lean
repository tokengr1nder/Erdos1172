/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3OrderedCoreTrace

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

open ErdosRadoCHAsym (W2 IsOmegaOneSup)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3ControlledCoreProducts (ProductData)
open Erdos1172Part3OrderedCoreTrace
  (trace trace_mono base_small_to_ordered_trace prior_source_ordered_positive)
open Erdos1172Part3StationaryDecisions (StationaryAt)
open Erdos1172Part3NamedBlueDerivedIdeal (fiber)
open Erdos1172Part3OmegaPowerIndex (mk_omegaIndex_le)
open OrdinalRamsey (HasCliqueOfType)

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
  have hclosed := Erdos1172Part3TransfiniteHechlerClosure.full_countablyClosed hGCH
  exact Erdos1172Part3ProductStationaryTraceLoss.exists_positive_stationary_trace_loss hGCH.toCH
    mk_omegaIndex_le (Erdos1172Part3TransfiniteHechlerCentering.centered hGCH ⊤) hclosed
    G H hcompl hred hblue (rank hGCH (mk_stage_le hGCH ⊤) mk_omegaIndex_le G)
    (blockRank hGCH (mk_stage_le hGCH ⊤) mk_omegaIndex_le G) source hsup trace trace_mono
    (fun _ data ha p hp U hU => base_small_to_ordered_trace hclosed data ha p hp U hU)
    (fun _ data p hp => prior_source_ordered_positive data p hp) club hclub hc p0 hstat

end Erdos1172Part3StationaryOrderedLoss
