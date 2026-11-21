/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3RelationalDecisionFusion

@[expose] public section

/-!
# Coherent clique decisions with coordinate-specific requirements

The extra requirement at a coordinate is persistent. Countable extension
meets it together with every earlier point, and antichain selection retains
it at the actual deciding condition. This is the relational construction for
the relation "earlier, smaller, and adjacent".
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3ConstrainedDecisionFusion

open ErdosRadoCHAsym (W1)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)

variable {P V : Type} [Preorder P] [LinearOrder V]

def ControlledExtension (G : SimpleGraph V) (R : P → V → Prop)
    (K : W1 → P → V → Prop) : Prop :=
  ∀ i : W1, ∀ p : P, ∀ s : Set V, s.Countable → (∀ x ∈ s, R p x) →
    ∃ q : P, q ≤ p ∧ ∃ y : V, R q y ∧ K i q y ∧ ∀ x ∈ s, x < y ∧ G.Adj x y

theorem exists_controlled_clique (hclosed : CountablyClosed P) (G : SimpleGraph V)
    (R : P → V → Prop) (K : W1 → P → V → Prop)
    (hR : ∀ {p q v}, q ≤ p → R p v → R q v)
    (hK : ∀ {i p q v}, q ≤ p → K i p v → K i q v)
    (hextend : ControlledExtension G R K) :
    ∃ core : CliqueDecisions P W1 V G, ∀ p i v, core.decides p i v → R p v ∧ K i p v := by
  obtain ⟨F, hF, hJ⟩ := Erdos1172Part3RelationalDecisionFusion.exists_relational_decisions
    hclosed R K (fun _ w v => w < v ∧ G.Adj w v) hR hK (fun _ h => h) hextend
  exact ⟨⟨F.decides, F.dense, F.persistent, F.unique, fun hij hv hw => (hJ _ _ _ _ _ hij hv hw).1,
    fun {p i j v w} hij hv hw => (lt_or_gt_of_ne hij).elim (fun h => (hJ p i j v w h hv hw).2)
      (fun h => (hJ p j i w v h hw hv).2.symm)⟩, hF⟩

end Erdos1172Part3ConstrainedDecisionFusion
