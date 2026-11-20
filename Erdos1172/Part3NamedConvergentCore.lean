/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedNeighborhoodStep
public import Erdos1172.Part3CliqueConeExtension

@[expose] public section

/-!
# Convergent core names

Every local neighborhood has a ground cutoff after which its truth at
the cut transfers to every actual point decision. The cutoff is uniform
over conditions below the start. The whole produced name need not be
locally coded, and its possible-value cover is not asserted to be a clique.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedConvergentCore

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularNamedIdeal
open Erdos1172Part3NamedPositiveExtension (colorGraph)
open Erdos1172Part3NamedNeighborhoodStep
open Erdos1172Part3ConstrainedDecisionFusion (ControlledExtension exists_controlled_clique)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName exists_nice_clique_name)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3StationaryDecisions (OmegaTwoCC)
open Erdos1172Part3CountableRankClosure (Local mk_local_le)

variable {P I : Type} [Preorder P] [LinearOrder I]
variable {G H : SimpleGraph W2} {r : Code P I G ↪ W2}
variable {σ : NiceCliqueName P I W2 G ↪ W2} {source : RegularName P W2} {a : W2}

def ConvergesBelow {K : SimpleGraph W2} (r : Code P I G ↪ W2) (H : SimpleGraph W2)
    (a : W2) (p0 : P) (core : CliqueDecisions P W1 W2 K) : Prop :=
  ∀ c : Code P I G, r c < a → ∃ bound : W1,
    ∀ p : P, p ≤ p0 → (eval G H c).holds p a →
      ∀ i : W1, bound < i → ∀ x : W2, core.decides p i x → (eval G H c).holds p x

end Erdos1172Part3NamedConvergentCore
