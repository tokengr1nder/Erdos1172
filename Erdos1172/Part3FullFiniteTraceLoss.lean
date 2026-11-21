/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3StationaryFiniteThinning
public import Erdos1172.Part3FullRankedCoreReflection

@[expose] public section

/-!
# Finite successor trace loss and exact stage localization

A constructed inner stationary factory reflects to guarded product
names. Generic trace extraction yields a full successor core with
stationary small losses. Its source, name, and trace future all factor
through one actual earlier stage of the full transfinite order.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3FullFiniteTraceLoss

open ErdosRadoCHAsym (W1 W2 IsOmegaOneSup)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularConeRestriction (onCone)
open Erdos1172Part3ClosedDecisionSystem (CliqueDecisions)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName exists_nice_clique_name)
open Erdos1172Part3FiniteTraceSchemes (Index scheme scheme_extracts mk_index_le)
open Erdos1172Part3CompleteRestriction (CompleteRestriction)
open Erdos1172Part3TraceCompleteRestriction (SameDecisions)
open Erdos1172Part3TransfiniteStageLocality (Full Earlier restriction exists_name_restriction)
open Erdos1172Part3TransfiniteHechlerOrder (mk_stage_le)
open Erdos1172Part3RegularStageLocality (EventuallyLocal)
open Erdos1172Part3RegularNeighborhoodCode (rank blockRank)
open Erdos1172Part3RankedCoreBlockAssembly (GoodCoreCut)
open Erdos1172Part3ControlledCoreProducts (ProductData exists_guarded_source_product)
open Erdos1172Part3FullRankedCoreReflection (LocalCoreFactory exists_club_goodCoreCut)
open Erdos1172Part3StationaryDecisions (StationaryAt)
open Erdos1172Part3NamedBlueDerivedIdeal (fiber)
open Erdos1172Part3ProductTraceIdeal
  (productTrace productTrace_mono base_small_to_product_trace prior_source_product_positive)
open OrdinalRamsey (HasCliqueOfType)

variable {P Q : Type} [Preorder P] [Preorder Q] {G : SimpleGraph W2}

noncomputable def traceFuture (n : ℕ) (source : RegularName P W2)
    (core : CliqueDecisions P (Index n) W2 G) (H : SimpleGraph W2) (a : W2) : RegularName P W2 :=
  meet source (meet (ground {b | a < b})
    (reindex (((scheme G n).forOrder P).trace core) (fun b => ground {x | H.Adj x b})))

theorem traceFuture_lift (n : ℕ) (r : CompleteRestriction P Q)
    (full : CliqueDecisions P (Index n) W2 G) (earlier : CliqueDecisions Q (Index n) W2 G)
    (hdec : SameDecisions r full earlier) (source : RegularName Q W2) (H : SimpleGraph W2) (a : W2) :
    r.liftRegular (traceFuture n source earlier H a) = traceFuture n (r.liftRegular source) full H a := by
  apply RegularName.ext
  intro p b
  exact (and_congr Iff.rfl (and_congr Iff.rfl
    ((scheme G n).restrict r full earlier hdec p (ground {x | H.Adj x b})))).symm

theorem exists_club_guarded_finite_products (n : ℕ) (hGCH : GCH)
    (G H : SimpleGraph W2) (factory : LocalCoreFactory hGCH (Index n) G)
    (source : RegularName (Full hGCH) W2)
    (hsup : ∀ p a, source.holds p a → IsOmegaOneSup a)
    (hlocal : EventuallyLocal (Earlier hGCH) (restriction hGCH) source) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, IsOmegaOneSup a →
      GoodCoreCut (rank hGCH (mk_stage_le hGCH ⊤) (mk_index_le n) G)
        (blockRank hGCH (mk_stage_le hGCH ⊤) (mk_index_le n) G) H source a ∧
      ((∃ p : Full hGCH, source.holds p a) →
        Nonempty (ProductData (rank hGCH (mk_stage_le hGCH ⊤) (mk_index_le n) G) H source a)) := by
  obtain ⟨club, hclub, hc⟩ := exists_club_goodCoreCut hGCH (mk_index_le n) G H factory source hsup hlocal
  exact ⟨club, hclub, fun a ha hsa => ⟨hc a ha hsa,
    exists_guarded_source_product (Erdos1172Part3TransfiniteHechlerClosure.full_countablyClosed hGCH)
      (Erdos1172Part3TransfiniteHechlerCentering.omegaTwoCC hGCH ⊤) (mk_index_le n) (hc a ha hsa)⟩⟩

theorem exists_global_finite_trace_loss (n : ℕ) (hGCH : GCH)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (factory : LocalCoreFactory hGCH (Index n) G)
    (source : RegularName (Full hGCH) W2)
    (hsup : ∀ p a, source.holds p a → IsOmegaOneSup a)
    (hlocal : EventuallyLocal (Earlier hGCH) (restriction hGCH) source)
    (p0 : Full hGCH) (hstat : StationaryAt source.holds p0) :
    ∃ a : W2, ∃ q : Full hGCH, q ≤ p0 ∧ source.holds q a ∧
      ∃ N : NiceCliqueName (Full hGCH) (Index (n + 1)) W2 G,
        (∀ p z x, N.toClique.decides p z x → x < a ∧ G.Adj x a) ∧
        (∀ p : Full hGCH, p ≤ q → ∀ z x, N.toClique.decides p z x → source.holds p x) ∧
        StationaryAt (traceFuture (n + 1) source N.toClique H a).holds q := by
  obtain ⟨club, hclub, hc⟩ := exists_club_guarded_finite_products n hGCH G H factory source hsup hlocal
  obtain ⟨a, q, hqp0, hcut, data, X, out, hXsub, hXpos, hout, hloss⟩ :=
    Erdos1172Part3ProductStationaryTraceLoss.exists_positive_stationary_trace_loss
      hGCH.toCH (mk_index_le n) (Erdos1172Part3TransfiniteHechlerCentering.centered hGCH ⊤)
      (Erdos1172Part3TransfiniteHechlerClosure.full_countablyClosed hGCH)
      G H hcompl hred hblue (rank hGCH (mk_stage_le hGCH ⊤) (mk_index_le n) G)
      (blockRank hGCH (mk_stage_le hGCH ⊤) (mk_index_le n) G) source hsup
      (productTrace ((scheme G n).forOrder (Full hGCH))) (productTrace_mono _)
      (fun _ data ha p hp U hU => base_small_to_product_trace _ data ha p hp U hU)
      (fun _ data p hp => prior_source_product_positive _ data p hp) club hclub hc p0 hstat
  obtain ⟨start, hstart, sub, hmember, htransfer⟩ := scheme_extracts G (n + 1)
    (Erdos1172Part3TransfiniteHechlerClosure.full_countablyClosed hGCH)
    data.name.toClique q X (hXpos q le_rfl)
  obtain ⟨global, hbelow, horigin⟩ :=
    Erdos1172Part3CliqueConeExtension.exists_global_clique_from_cone
      (Erdos1172Part3TransfiniteHechlerClosure.full_countablyClosed hGCH) start sub (mk_index_le (n + 1))
  obtain ⟨N, hN⟩ := exists_nice_clique_name
    (Erdos1172Part3TransfiniteHechlerCentering.omegaTwoCC hGCH ⊤) global
  have hNbelow (p : Set.Iic start) (z : Index (n + 1)) (x : W2) (hx : N.toClique.decides p.val z x) :
      sub.decides p z x := (hbelow p.val p.property z x).mp (hN p.val z x hx)
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
    have hsmall : (((scheme G (n + 1)).forOrder (Set.Iic start)).trace sub).holds t
        (onCone start (ground {x | H.Adj x b})) := by
      apply ((scheme G (n + 1)).forOrder (Set.Iic start)).on_decisions sub t
        (onCone start (ground {x | H.Adj x b})) (onCone start (fiber H b X)) ?_ htrans
      intro v hvt z x hx hHxb
      exact ⟨(hmember v z x hx).1, hHxb⟩
    exact ⟨s, hsp, hb.1, hb.2.1,
      (scheme G (n + 1)).fromCone start sub N.toClique hNbelow t (ground {x | H.Adj x b}) hsmall⟩

theorem exists_finite_trace_restriction (n : ℕ) (hGCH : GCH) {G : SimpleGraph W2}
    (source : RegularName (Full hGCH) W2)
    (hlocal : EventuallyLocal (Earlier hGCH) (restriction hGCH) source)
    (N : NiceCliqueName (Full hGCH) (Index n) W2 G) (H : SimpleGraph W2) (a : W2) :
    ∃ b : W2, ∃ V : RegularName (Earlier hGCH b) W2,
      ∃ M : NiceCliqueName (Earlier hGCH b) (Index n) W2 G,
        (restriction hGCH b).liftRegular V = source ∧
        SameDecisions (restriction hGCH b) N.toClique M.toClique ∧
        (restriction hGCH b).liftRegular (traceFuture n V M.toClique H a) =
          traceFuture n source N.toClique H a := by
  obtain ⟨nameBound, hname⟩ := exists_name_restriction hGCH N (mk_index_le n)
  obtain ⟨sourceBound, hsource⟩ := hlocal
  let b := max nameBound sourceBound
  obtain ⟨M, hM⟩ := hname b (le_max_left _ _)
  obtain ⟨V, hV⟩ := hsource b (le_max_right _ _)
  have hdec : SameDecisions (restriction hGCH b) N.toClique M.toClique :=
    fun p z x => (hM p z x).symm
  refine ⟨b, V, M, hV, hdec, ?_⟩
  rw [traceFuture_lift n (restriction hGCH b) N.toClique M.toClique hdec V H a, hV]

end Erdos1172Part3FullFiniteTraceLoss
