/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3ConstrainedDecisionFusion

@[expose] public section

/-!
# Coherent omegaOne clique decisions from countable extension

At each coordinate the countable preceding family is decided together.
A fresh vertex is chosen with actual membership, and uniqueness of the
earlier names preserves all cross edges at subsequent strengthenings.
There is no lower bound of the completed omegaOne sequence. This is the
constrained construction with a trivial coordinate requirement.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3CountableDecisionFusion

open ErdosRadoCHAsym (W1)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)

variable {P V : Type} [Preorder P] [LinearOrder V]

def CountableExtension (G : SimpleGraph V) (R : P → V → Prop) : Prop :=
  ∀ p : P, ∀ s : Set V, s.Countable → (∀ x ∈ s, R p x) →
    ∃ q : P, q ≤ p ∧ ∃ y : V, R q y ∧ ∀ x ∈ s, x < y ∧ G.Adj x y

/-- The extension hypothesis is used to construct all point decisions;
no clique-decision system is supplied as an input. -/
theorem exists_clique_decisions_of_countable_extension (hclosed : CountablyClosed P)
    (G : SimpleGraph V) (R : P → V → Prop)
    (hpersistent : ∀ {p q v}, q ≤ p → R p v → R q v)
    (hextend : CountableExtension G R) :
    ∃ core : CliqueDecisions P W1 V G, ∀ p i v, core.decides p i v → R p v := by
  obtain ⟨core, hcore⟩ := Erdos1172Part3ConstrainedDecisionFusion.exists_controlled_clique
    hclosed G R (fun _ _ _ => True) hpersistent (fun _ h => h) fun _ p s hs hR => by
      obtain ⟨q, hq, y, hy, hxy⟩ := hextend p s hs hR
      exact ⟨q, hq, y, hy, trivial, hxy⟩
  exact ⟨core, fun p i v hv => (hcore p i v hv).1⟩

end Erdos1172Part3CountableDecisionFusion
