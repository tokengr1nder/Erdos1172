/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3RegularMembership
public import Erdos1172.Part3LocalNamedSquare

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

/-- This is stronger than preservation of ground pointwise properties.
Regularity recovers truth at the original condition from its dense
refinements; persistence alone would not justify that step. -/
theorem allDecisions_eq_of_refines (F N : FunctionDecisions P I V)
    (href : ∀ p i v, N.decides p i v → F.decides p i v)
    (B : I → V → RegularName P X) : allDecisions N B = allDecisions F B := by
  apply RegularName.ext
  intro p x
  constructor
  · intro h q hqp i v hv
    apply (B i v).of_dense q x
    intro r hrq
    obtain ⟨s, hsr, w, hw⟩ := N.dense r i
    have heq : v = w := F.unique (F.persistent (hsr.trans hrq) hv) (href s i w hw)
    subst w
    exact ⟨s, hsr, h s ((hsr.trans hrq).trans hqp) i v hw⟩
  · intro h q hqp i v hv
    exact h q hqp i v (href q i v hv)

def containedIn (F : FunctionDecisions P I V) (source : RegularName P V) :
    RegularName P Unit := allDecisions F (fun _ v => reindex source (fun _ => v))

theorem containedIn_eq_of_refines (F N : FunctionDecisions P I V)
    (href : ∀ p i v, N.decides p i v → F.decides p i v)
    (source : RegularName P V) : containedIn N source = containedIn F source :=
  allDecisions_eq_of_refines F N href _

variable [LinearOrder I] [LinearOrder V] {G : SimpleGraph V}

def cliqueFunction (core : CliqueDecisions P I V G) : FunctionDecisions P I V :=
  ⟨core.decides, core.dense, core.persistent, core.unique⟩

def afterClique (core : CliqueDecisions P I V G) : RegularName P V :=
  allDecisions (cliqueFunction core) (fun _ v => ground {x | v < x ∧ G.Adj v x})

theorem nice_clique_regular_property_iff (core : CliqueDecisions P I V G)
    (N : NiceCliqueName P I V G)
    (href : ∀ p i v, N.toClique.decides p i v → core.decides p i v)
    (B : I → V → RegularName P X) (p : P) (x : X) :
    (∀ q : P, q ≤ p → ∀ i v, N.toClique.decides q i v → (B i v).holds q x) ↔
      (∀ q : P, q ≤ p → ∀ i v, core.decides q i v → (B i v).holds q x) := by
  have h := allDecisions_eq_of_refines (cliqueFunction core)
    (cliqueFunction N.toClique) href B
  change (allDecisions (cliqueFunction N.toClique) B).holds p x ↔
    (allDecisions (cliqueFunction core) B).holds p x
  rw [h]

theorem afterClique_square_iff
    {G : SimpleGraph ErdosRadoCHAsym.W2}
    (N : Erdos1172Part3CliqueNameCoding.SquareName G)
    (p : Erdos1172Part3HechlerOrder.Condition) (a : ErdosRadoCHAsym.W2) :
    (afterClique N.toClique).holds p a ↔
      Erdos1172Part3LocalNamedSquare.JoinedAt N p a := Iff.rfl

end Erdos1172Part3RegularCliqueNeighborhoods
