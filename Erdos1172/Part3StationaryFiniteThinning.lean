/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3FiniteCutoffCoding

@[expose] public section

/-!
# Stationary loss elimination at every finite depth

After freezing the root cutoff on a stationary decision fiber, a single
dominating function controls all coded inner prefixes. The finite-path
selector then removes every blue loss and retains a stationary future.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3StationaryFiniteThinning

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership (RegularName ground)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3FiniteTraceSchemes (Index Prefix root scheme)
open Erdos1172Part3FiniteTraceCutoffs (Clears subBounds exists_finite_trace_cutoffs)
open Erdos1172Part3FiniteStemSelection (Selected thinningClique thinningClique_origin exists_clears_of_selected)
open Erdos1172Part3FiniteCutoffCoding
open Erdos1172Part3StationaryDecisions
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3IteratedHechlerOrder (Condition liftBase liftBase_le)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3NamedStationaryTail
open Erdos1172Part3NamedCliqueThinning (StationaryCliqueDecisions)
open Erdos1172Part3StationarySquareDecisions (tail tail_strict lt_tail)

variable {P : Type} [Preorder P]

theorem exists_stationary_finite_from_cutoffs (n : ℕ)
    (center : CountablyCenteredCode P) (hclosed : CountablyClosed P) (hCH : CH)
    (p0 : Condition P) (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (core : CliqueDecisions P (Index (n + 1)) W2 G) (U : P → W2 → Prop) (hU : Persistent U)
    (hs : IsStationary (possible U p0.base))
    (hafter : ∀ p a, U p a → ∀ z x, core.decides p z x → x < a)
    (B : W2 → FunctionDecisions P (Prefix (n + 1)) W1)
    (hloss : ∀ p a, U p a → ∀ z x, core.decides p z x → Clears (n + 1) (B a) p z → ¬H.Adj x a) :
    ∃ sys : StationaryCliqueDecisions (Condition P) (Index (n + 1)) G,
      sys.start ≤ p0 ∧ (∀ q a, sys.future q a → U q.base a) ∧
        ∀ q z x, sys.clique.decides q z x → ∃ old : Index (n + 1), core.decides q.base old x := by
  classical
  let K := Erdos1172Part3NamedCubeTraceBounds.transposeDecisions B (root (n + 1))
  have hsmall : #W1 < ℵ_ 2 := by
    simp only [W1, Cardinal.mk_toType, Ordinal.card_omega]
    exact Cardinal.aleph_lt_aleph.mpr (by norm_num)
  obtain ⟨cutoff, base, hbase, hb⟩ :=
    Erdos1172Part3NamedCutoffRefinement.exists_stationary_small_decision_fiber
      hsmall center.omegaTwoCC p0.base U hU hs K
  let V : P → W2 → Prop := fun p a => U p a ∧ K.decides p a cutoff
  have hV : Persistent V := fun hqp ha => ⟨hU hqp ha.1, K.persistent hqp ha.2⟩
  let M (a : W2) := encodedBounds n (B a)
  obtain ⟨bound, p, hpp0, hp⟩ := exists_stationary_uniform_tail center hCH (liftBase p0 base)
    V hV (hb base le_rfl) M
  obtain ⟨codeBound, hcodeBound⟩ := exists_late_rows_above_code_bound n bound
  let row : W1 → W1 := tail (max cutoff codeBound)
  let clique := thinningClique hclosed n core row (tail_strict _) (prefixCode n)
  have hcross : ∀ q a, TailMembers V M bound q a → ∀ z x,
      clique.decides q z x → x < a ∧ G.Adj x a := by
    intro q a ha z x hx
    obtain ⟨old, hsel, hx⟩ := hx
    have hrowCut : cutoff < row (ofLex z).1 := (le_max_left _ _).trans_lt (lt_tail _ _)
    have hrowCode : codeBound < row (ofLex z).1 := (le_max_right _ _).trans_lt (lt_tail _ _)
    have hbefore : x < a := hafter q.base a ha.1.1 _ x hx
    refine ⟨hbefore, ?_⟩
    rw [← hcompl.symm.compl_eq, SimpleGraph.compl_adj]
    refine ⟨hbefore.ne, ?_⟩
    obtain ⟨next, hnext, hclear⟩ := exists_clears_of_selected n
      (subBounds (B a) (row (ofLex z).1)) (fun e => prefixCode n (row (ofLex z).1, e))
      q (ofLex z).2 old hsel
      (fun e v hv => encodedBounds_bound n (ha.2 q le_rfl _ (hcodeBound _ hrowCode e) v hv)) q.base le_rfl
    apply hloss next a (hU hnext ha.1.1) (toLex (row (ofLex z).1, old)) x
      (core.persistent hnext hx)
    exact ⟨cutoff, K.persistent hnext ha.1.2, hrowCut, hclear⟩
  refine ⟨{
    start := p
    clique := clique
    future := TailMembers V M bound
    persistent := tailMembers_persistent V hV M bound
    stationary := hp
    cross := hcross }, hpp0.trans (liftBase_le p0 hbase), fun _ _ h => h.1.1, ?_⟩
  exact thinningClique_origin hclosed n core row (tail_strict _) (prefixCode n)

theorem exists_stationary_finite_from_trace_losses (n : ℕ)
    (center : CountablyCenteredCode P) (hclosed : CountablyClosed P) (hCH : CH)
    (p0 : Condition P) (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (core : CliqueDecisions P (Index (n + 1)) W2 G) (future : RegularName P W2)
    (hs : IsStationary (possible future.holds p0.base))
    (hafter : ∀ p a, future.holds p a → ∀ z x, core.decides p z x → x < a)
    (hloss : ∀ p a, future.holds p a →
      (((scheme G (n + 1)).forOrder P).trace core).holds p (ground {x | H.Adj x a})) :
    ∃ sys : StationaryCliqueDecisions (Condition P) (Index (n + 1)) G,
      sys.start ≤ p0 ∧ (∀ q a, sys.future q a → future.holds q.base a) ∧
        ∀ q z x, sys.clique.decides q z x → ∃ old : Index (n + 1), core.decides q.base old x := by
  obtain ⟨B, hB⟩ := exists_finite_trace_cutoffs (n + 1) core future hloss
  exact exists_stationary_finite_from_cutoffs n center hclosed hCH p0 G H hcompl core
    future.holds future.persistent hs hafter B hB

end Erdos1172Part3StationaryFiniteThinning
