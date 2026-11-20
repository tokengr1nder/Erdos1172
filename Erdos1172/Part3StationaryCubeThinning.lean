/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedCubeThinning

@[expose] public section

/-!
# Eliminating stationary cubic trace losses at a Hechler successor

One combined earlier function controls the middle cutoff and the coded
inner cutoffs. Bounded code sets meet only boundedly many outer rows, so
every selected coordinate is beyond the same domination threshold. The
result is a full cubic name with a stationary common-red future.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3StationaryCubeThinning

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership (RegularName ground)
open Erdos1172Part3ProductTraceIdeal (cubeTrace)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3StationaryDecisions
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3IteratedHechlerOrder (Condition liftBase liftBase_le)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3NamedStationaryTail
open Erdos1172Part3NamedCliqueThinning (StationaryCliqueDecisions)
open Erdos1172Part3NamedCubeThinning (thinningClique thinningClique_origin selectedPair)
open Erdos1172Part3CubeDominationCoding
open Erdos1172Part3StationarySquareDecisions (Square tail tail_strict lt_tail)
open Erdos1172Part3FullSourceCubes (Cube)

variable {P : Type} [Preorder P]

theorem exists_stationary_cube_from_named_row_bounds
    (center : CountablyCenteredCode P) (hclosed : CountablyClosed P) (hCH : CH)
    (p0 : Condition P) (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (core : CliqueDecisions P Cube W2 G) (U : P → W2 → Prop) (hU : Persistent U)
    (hs : IsStationary (possible U p0.base))
    (hafter : ∀ p a, U p a → ∀ z x, core.decides p z x → x < a)
    (cutoff : W1) (F : W2 → FunctionDecisions P W1 W1) (B : W2 → FunctionDecisions P Square W1)
    (hloss : ∀ p a, U p a → ∀ i : W1, cutoff < i →
      ∀ middle : W1, (F a).decides p i middle → ∀ j : W1, middle < j →
        ∀ k : W1, ∀ x : W2, core.decides p (toLex (i, toLex (j, k))) x → H.Adj x a →
          ∀ v : W1, (B a).decides p (toLex (i, j)) v → k < v) :
    ∃ sys : StationaryCliqueDecisions (Condition P) Cube G,
      sys.start ≤ p0 ∧ (∀ q a, sys.future q a → U q.base a) ∧
        ∀ q z x, sys.clique.decides q z x → ∃ old : Cube, core.decides q.base old x := by
  classical
  let M (a : W2) := combinedBounds (F a) (B a)
  obtain ⟨bound, p, hpp0, hp⟩ := exists_stationary_uniform_tail center hCH p0 U hU hs M
  obtain ⟨codeBound, hcodeBound⟩ := exists_late_rows_above_code_bound bound
  let row : W1 → W1 := tail (max cutoff (max bound codeBound))
  let clique := thinningClique hclosed core row (tail_strict _)
  have hcross : ∀ q a, TailMembers U M bound q a → ∀ z x,
      clique.decides q z x → x < a ∧ G.Adj x a := by
    intro q a ha z x hx
    obtain ⟨v, hv, w, hw, hx⟩ := hx
    have hrowCut : cutoff < row (ofLex z).1 :=
      (le_max_left _ _).trans_lt (lt_tail _ _)
    have hrowBound : bound < row (ofLex z).1 :=
      ((le_max_left bound codeBound).trans (le_max_right cutoff _)).trans_lt (lt_tail _ _)
    have hrowCode : codeBound < row (ofLex z).1 :=
      ((le_max_right bound codeBound).trans (le_max_right cutoff _)).trans_lt (lt_tail _ _)
    have hpairBound : bound < pairEquiv (selectedPair row v z) :=
      hcodeBound _ hrowCode _
    have hbefore : x < a := hafter q.base a ha.1 _ x hx
    refine ⟨hbefore, ?_⟩
    rw [← hcompl.symm.compl_eq, SimpleGraph.compl_adj]
    refine ⟨hbefore.ne, ?_⟩
    intro hblue
    obtain ⟨base, hbase, middle, hmiddle⟩ := (F a).dense q.base (row (ofLex z).1)
    obtain ⟨next, hnext, inner, hinner⟩ := (B a).dense base (selectedPair row v z)
    have hmiddleBound : middle < v := combinedBounds_left
      (ha.2 q le_rfl _ hrowBound v hv) base hbase middle hmiddle
    have hinnerBound : inner < w := combinedBounds_right
      (ha.2 q le_rfl _ hpairBound w hw) next (hnext.trans hbase) inner hinner
    have hsmall := hloss next a (hU (hnext.trans hbase) ha.1) _ hrowCut middle
      ((F a).persistent hnext hmiddle) _ (hmiddleBound.trans (lt_tail v _)) _ x
      (core.persistent (hnext.trans hbase) hx) hblue inner hinner
    exact (hinnerBound.trans (lt_tail w (ofLex (ofLex z).2).2)).asymm hsmall
  refine ⟨{
    start := p
    clique := clique
    future := TailMembers U M bound
    persistent := tailMembers_persistent U hU M bound
    stationary := hp
    cross := hcross }, hpp0, fun _ _ h => h.1, ?_⟩
  exact thinningClique_origin hclosed core row (tail_strict _)

theorem exists_stationary_cube_from_named_cutoffs
    (center : CountablyCenteredCode P) (hclosed : CountablyClosed P) (hCH : CH)
    (p0 : Condition P) (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (core : CliqueDecisions P Cube W2 G) (U : P → W2 → Prop) (hU : Persistent U)
    (hs : IsStationary (possible U p0.base))
    (hafter : ∀ p a, U p a → ∀ z x, core.decides p z x → x < a)
    (K : FunctionDecisions P W2 W1) (F : W2 → FunctionDecisions P W1 W1)
    (B : W2 → FunctionDecisions P Square W1)
    (hloss : ∀ p a, U p a → ∀ cutoff : W1, K.decides p a cutoff →
      ∀ i : W1, cutoff < i → ∀ middle : W1, (F a).decides p i middle →
        ∀ j : W1, middle < j → ∀ k : W1, ∀ x : W2,
          core.decides p (toLex (i, toLex (j, k))) x → H.Adj x a →
            ∀ v : W1, (B a).decides p (toLex (i, j)) v → k < v) :
    ∃ sys : StationaryCliqueDecisions (Condition P) Cube G,
      sys.start ≤ p0 ∧ (∀ q a, sys.future q a → U q.base a) ∧
        ∀ q z x, sys.clique.decides q z x → ∃ old : Cube, core.decides q.base old x := by
  have hsmall : #W1 < ℵ_ 2 := by
    simp only [W1, Cardinal.mk_toType, Ordinal.card_omega]
    exact Cardinal.aleph_lt_aleph.mpr (by norm_num)
  obtain ⟨cutoff, base, hbase, hb⟩ :=
    Erdos1172Part3NamedCutoffRefinement.exists_stationary_small_decision_fiber
      hsmall center.omegaTwoCC p0.base U hU hs K
  let V : P → W2 → Prop := fun p a => U p a ∧ K.decides p a cutoff
  have hV : Persistent V := fun hqp ha => ⟨hU hqp ha.1, K.persistent hqp ha.2⟩
  obtain ⟨sys, hsys, hfuture, horigin⟩ := exists_stationary_cube_from_named_row_bounds
    center hclosed hCH (liftBase p0 base) G H hcompl core V hV (hb base le_rfl)
    (fun p a ha => hafter p a ha.1) cutoff F B (fun p a ha => hloss p a ha.1 cutoff ha.2)
  exact ⟨sys, hsys.trans (liftBase_le p0 hbase), fun q a ha => (hfuture q a ha).1, horigin⟩

theorem exists_stationary_cube_from_trace_losses
    (center : CountablyCenteredCode P) (hclosed : CountablyClosed P) (hCH : CH)
    (p0 : Condition P) (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (core : CliqueDecisions P Cube W2 G) (future : RegularName P W2)
    (hs : IsStationary (possible future.holds p0.base))
    (hafter : ∀ p a, future.holds p a → ∀ z x, core.decides p z x → x < a)
    (hloss : ∀ p a, future.holds p a → (cubeTrace.trace core).holds p (ground {x | H.Adj x a})) :
    ∃ sys : StationaryCliqueDecisions (Condition P) Cube G,
      sys.start ≤ p0 ∧ (∀ q a, sys.future q a → future.holds q.base a) ∧
        ∀ q z x, sys.clique.decides q z x → ∃ old : Cube, core.decides q.base old x := by
  obtain ⟨K, F, B, hbounds⟩ :=
    Erdos1172Part3NamedCubeTraceBounds.exists_named_cube_trace_cutoffs core future hloss
  exact exists_stationary_cube_from_named_cutoffs center hclosed hCH p0 G H hcompl core
    future.holds future.persistent hs hafter K F B hbounds

end Erdos1172Part3StationaryCubeThinning
