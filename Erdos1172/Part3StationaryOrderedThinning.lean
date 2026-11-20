/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedStationaryShortCovers
public import Erdos1172.Part3StationarySupportedThinning
public import Erdos1172.Part3OrderedCoreTrace

@[expose] public section

/-!
# Stationary thinning from hereditary ordered-small adjacency losses

Pull back the bad-edge neighborhood along the actual clique decisions.
Ordered trace smallness rules out a full embedding in each resulting
regular index loss. The stationary short-cover theorem constructs a
common short covering family and covering function names on a stationary
regular future subname.

The supported thinning theorem then supplies a full stationary subclique
on a selected cone. Cover families and covering function names are not
assumed in the final theorem; the actual ordered-small loss premise is
retained explicitly.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3StationaryOrderedThinning

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName ground)
open Erdos1172Part3RegularCliqueNeighborhoods (cliqueFunction)
open Erdos1172Part3RegularGreedyEnumeration (HasOrderedEmbeddingBelow)
open Erdos1172Part3StationaryDecisions (possible)
open Erdos1172Part3IteratedHechlerOrder (Condition liftBase liftBase_le stronger_refl)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3NamedCliqueThinning (StationaryCliqueDecisions)
open Erdos1172Part3OrderedCoreTrace (pullback pullback_holds_iff_of_decides trace trace_holds_iff)
open Erdos1172Part3SupportedCoverRealization (coverName)

variable {P V : Type} [Preorder P] [LinearOrder V] [WellFoundedLT V]

/-- Ordered-small actual bad-edge traces suffice for full stationary
omega-successor thinning. The conclusion retains the original future
and actual origins in the old core, entirely on the selected cone. -/
theorem exists_stationary_clique_from_ordered_losses
    (center : CountablyCenteredCode P) (hclosed : CountablyClosed P) (hCH : CH)
    (p0 : Condition P) (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (core : CliqueDecisions P V W2 G)
    (hcard : #V ≤ ℵ_ 1) (htype : typeLT V = (ω_ 1 : Ordinal.{0}) ^ (ω + 1))
    (future : RegularName P W2) (hs : IsStationary (possible future.holds p0.base))
    (hafter : ∀ p a, future.holds p a → ∀ i x, core.decides p i x → x < a)
    (hloss : ∀ p a, future.holds p a →
      (trace core).holds p (ground {x : W2 | H.Adj x a})) :
    ∃ p : Condition P, p ≤ p0 ∧
      ∃ sys : StationaryCliqueDecisions (Set.Iic p) V G,
        sys.start = (⟨p, stronger_refl (P := P) p⟩ : Set.Iic p) ∧
        (∀ q a, sys.future q a → future.holds q.val.base a) ∧
        ∀ q i x, sys.clique.decides q i x → ∃ z : V, core.decides q.val.base z x := by
  let loss (a : W2) : RegularName P V :=
    pullback (cliqueFunction core) (ground {x : W2 | H.Adj x a})
  have hno : ∀ p : P, p ≤ p0.base → ∀ a : W2, future.holds p a →
      ¬HasOrderedEmbeddingBelow (I := V) (loss a) p := by
    intro p _ a ha
    exact (trace_holds_iff core p _).mp (hloss p a ha) p le_rfl
  obtain ⟨base, hbase, T, hT, hTU, C, _hmono, _hsupported, hC, F, hF⟩ :=
    Erdos1172Part3NamedStationaryShortCovers.exists_stationary_short_cover
      hcard htype hclosed center.omegaTwoCC future p0.base hs loss hno
  have hafterT : ∀ p a, T.holds p a → ∀ i x, core.decides p i x → x < a :=
    fun p a ha i x hx => hafter p a (hTU p a ha) i x hx
  have hcovered : ∀ p a, T.holds p a → ∀ i x, core.decides p i x → ¬G.Adj x a →
      (coverName (F a) C).holds p i := by
    intro p a ha i x hx hbad
    have hbefore : x < a := hafterT p a ha i x hx
    have hblue : H.Adj x a := by
      rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
      exact ⟨hbefore.ne, hbad⟩
    apply hF p a i ha
    exact (pullback_holds_iff_of_decides (cliqueFunction core)
      (ground {z : W2 | H.Adj z a}) hx).mpr hblue
  obtain ⟨p, hp, sys, hstart, hfuture, horigin⟩ :=
    Erdos1172Part3StationarySupportedThinning.exists_stationary_clique_from_supported_losses
      center hclosed hCH (liftBase p0 base) G core hcard htype T.holds T.persistent
      (hT base le_rfl) hafterT F C hC hcovered
  refine ⟨p, hp.trans (liftBase_le p0 hbase), sys, hstart, ?_, horigin⟩
  exact fun q a ha => hTU q.val.base a (hfuture q a ha)

end Erdos1172Part3StationaryOrderedThinning
