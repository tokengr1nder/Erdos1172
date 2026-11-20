/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedStationaryRedBlock

@[expose] public section

/-!
# Regular availability of locally coded red blocks

A witness has one locally ranked nice name, all its possible values
below the cut, actual source membership at all compatible decisions,
and an actual common-red cut. Availability means such witnesses are
dense below the current condition.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3RegularLocalBlock

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularCliqueNeighborhoods (afterClique containedIn cliqueFunction)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)

variable {P : Type} [Preorder P] {G : SimpleGraph W2}

def WitnessBlock (σ : NiceCliqueName P W1 W2 G ↪ W2)
    (source : RegularName P W2) (p : P) (a : W2) : Prop :=
  ∃ N : NiceCliqueName P W1 W2 G, σ N < a ∧
    (∀ q i x, N.toClique.decides q i x → x < a) ∧
    (containedIn (cliqueFunction N.toClique) source).holds p () ∧
    (afterClique N.toClique).holds p a

theorem witnessBlock_persistent {σ : NiceCliqueName P W1 W2 G ↪ W2}
    {source : RegularName P W2} {p q : P} {a : W2} (hqp : q ≤ p)
    (h : WitnessBlock σ source p a) : WitnessBlock σ source q a := by
  obtain ⟨N, hN, hbelow, hsource, hafter⟩ := h
  exact ⟨N, hN, hbelow, (containedIn (cliqueFunction N.toClique) source).persistent hqp hsource,
    (afterClique N.toClique).persistent hqp hafter⟩

def localBlockName (σ : NiceCliqueName P W1 W2 G ↪ W2) (source : RegularName P W2) :
    RegularName P W2 := regularize (WitnessBlock σ source)

theorem localBlock_of_witness {σ : NiceCliqueName P W1 W2 G ↪ W2}
    {source : RegularName P W2} {p : P} {a : W2} (h : WitnessBlock σ source p a) :
    (localBlockName σ source).holds p a :=
  fun q hqp => ⟨q, le_rfl, witnessBlock_persistent hqp h⟩

theorem exists_block_refinement {σ : NiceCliqueName P W1 W2 G ↪ W2}
    {source : RegularName P W2} {p : P} {a : W2}
    (h : (localBlockName σ source).holds p a) :
    ∃ q : P, q ≤ p ∧ WitnessBlock σ source q a := h p le_rfl

end Erdos1172Part3RegularLocalBlock
