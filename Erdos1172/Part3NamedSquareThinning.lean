/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedCliqueThinning

@[expose] public section

/-!
# The stationary square-loss step for earlier-stage names

The input square, future membership, and row bounds are all persistent
decision systems over an earlier order. A further dominating-function
stage supplies a thinned square joined to stationary future decisions.
The input geometric row-bound condition is explicit and remains to be
constructed in the higher-core recursion.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedSquareThinning

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3StationaryDecisions
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3IteratedHechlerOrder (Condition)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3NamedStationaryTail
open Erdos1172Part3NamedCliqueThinning
open Erdos1172Part3StationarySquareDecisions (Square tail tail_strict lt_tail)

variable {P : Type} [Preorder P]

/-- Named ordinal row bounds suffice, with no assumption that the core
or its loss functions are fixed ground objects. The output preserves
membership in the earlier future and pointwise origin in the earlier core. -/
theorem exists_stationary_square_from_named_row_bounds
    (c : CountablyCenteredCode P) (hclosed : CountablyClosed P) (hCH : CH)
    (p0 : Condition P) (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (core : CliqueDecisions P Square W2 G) (U : P → W2 → Prop) (hU : Persistent U)
    (hs : IsStationary (possible U p0.base))
    (hafter : ∀ p a, U p a → ∀ z x, core.decides p z x → x < a)
    (cutoff : W1) (F : W2 → FunctionDecisions P W1 W1)
    (hloss : ∀ p a, U p a → ∀ i : W1, cutoff < i → ∀ j : W1, ∀ x : W2,
      core.decides p (toLex (i, j)) x → H.Adj x a →
        ∀ v : W1, (F a).decides p i v → j < v) :
    ∃ sys : StationaryCliqueDecisions (Condition P) Square G,
      sys.start ≤ p0 ∧ (∀ q a, sys.future q a → U q.base a) ∧
        ∀ q i x, sys.clique.decides q i x → ∃ z : Square, core.decides q.base z x := by
  classical
  obtain ⟨bound, p, hpp0, hp⟩ := exists_stationary_uniform_tail c hCH p0 U hU hs F
  let row : W1 → W1 := tail (max cutoff bound)
  let clique := thinningClique hclosed core row (tail_strict _)
  have hcross : ∀ q a, TailMembers U F bound q a → ∀ i x,
      clique.decides q i x → x < a ∧ G.Adj x a := by
    intro q a ha i x hx
    obtain ⟨v, hv, hx⟩ := hx
    have hrowCut : cutoff < row (ofLex i).1 :=
      (le_max_left cutoff bound).trans_lt (lt_tail _ _)
    have hrowBound : bound < row (ofLex i).1 :=
      (le_max_right cutoff bound).trans_lt (lt_tail _ _)
    have hbefore : x < a := hafter q.base a ha.1 _ x hx
    refine ⟨hbefore, ?_⟩
    rw [← hcompl.symm.compl_eq, SimpleGraph.compl_adj]
    refine ⟨hbefore.ne, ?_⟩
    intro hblue
    obtain ⟨base, hbase, w, hw⟩ := (F a).dense q.base (row (ofLex i).1)
    have hsmall : tail v (ofLex i).2 < w := hloss base a (hU hbase ha.1)
      _ hrowCut _ x (core.persistent hbase hx) hblue w hw
    have hlarge : w < v := ha.2 q le_rfl _ hrowBound v hv base hbase w hw
    exact (hlarge.trans (lt_tail v (ofLex i).2)).asymm hsmall
  refine ⟨{
    start := p
    clique := clique
    future := TailMembers U F bound
    persistent := tailMembers_persistent U hU F bound
    stationary := hp
    cross := hcross }, hpp0, fun _ _ h => h.1, ?_⟩
  exact thinningClique_origin hclosed core row (tail_strict _)

end Erdos1172Part3NamedSquareThinning
