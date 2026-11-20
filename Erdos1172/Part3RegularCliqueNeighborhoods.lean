/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3RegularMembership
public import Erdos1172.Part3CliqueNameCoding

@[expose] public section

/-!
# Actual membership at decisions of named blocks

Universal assertions about a function name and regular membership predicates
are again regular. Dense normalization therefore preserves these assertions
even when membership depends on the condition. Ground common red
neighborhoods of square names are instances of this construction.
-/

open Set

namespace Erdos1172Part3RegularCliqueNeighborhoods

open Erdos1172Part3RegularMembership
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3ClosedDecisionSystem (CliqueDecisions)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)

variable {P I V X : Type} [Preorder P]

def allDecisions (F : FunctionDecisions P I V)
    (B : I → V → RegularName P X) : RegularName P X where
  holds p x := ∀ q : P, q ≤ p → ∀ i v, F.decides q i v → (B i v).holds q x
  persistent hqp h r hrq := h r (hrq.trans hqp)
  of_dense p x h q hqp i v hv := by
    apply (B i v).of_dense q x
    intro r hrq
    obtain ⟨s, hsr, hs⟩ := h r (hrq.trans hqp)
    exact ⟨s, hsr, hs s le_rfl i v (F.persistent (hsr.trans hrq) hv)⟩

def containedIn (F : FunctionDecisions P I V) (source : RegularName P V) :
    RegularName P Unit := allDecisions F (fun _ v => reindex source (fun _ => v))

variable [LinearOrder I] [LinearOrder V] {G : SimpleGraph V}

def cliqueFunction (core : CliqueDecisions P I V G) : FunctionDecisions P I V :=
  ⟨core.decides, core.dense, core.persistent, core.unique⟩

def afterClique (core : CliqueDecisions P I V G) : RegularName P V :=
  allDecisions (cliqueFunction core) (fun _ v => ground {x | v < x ∧ G.Adj v x})

end Erdos1172Part3RegularCliqueNeighborhoods
