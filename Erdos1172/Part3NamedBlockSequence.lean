/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3RelationalDecisionFusion
public import Erdos1172.Part3CountableBlockExtension

@[expose] public section

/-!
# Coherent omegaOne sequences of locally ranked red block names

Each outer coordinate chooses a whole inner omegaOne block. At every
compatible pair of outer decisions the earlier block is completely red
to, and before, the later block. The extension law is supplied by the
constructed local environment, not retained as an extra premise.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedBlockSequence

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularBlockEnvironment (GoodBlockCut)
open Erdos1172Part3CountableBlockExtension (BlockAt blockAt_persistent joinedName exists_block_after_countable)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RelationalDecisionFusion (RelationalExtension exists_relational_decisions)

variable {P : Type} [Preorder P] {G H : SimpleGraph W2}
variable {r : Code P W1 G ↪ W2} {σ : NiceCliqueName P W1 W2 G ↪ W2}
variable {source : RegularName P W2} {a : W2}

theorem exists_block_sequence (hclosed : CountablyClosed P) (ha : GoodBlockCut r σ H source a)
    (p0 : P) (hp0 : source.holds p0 a) :
    ∃ F : FunctionDecisions (Set.Iic p0) W1 (NiceCliqueName P W1 W2 G),
      (∀ p i N, F.decides p i N → BlockAt σ source a p.val N) ∧
      ∀ p i j N M, i < j → F.decides p i N → F.decides p j M →
        (joinedName N M).holds p.val () := by
  let R (p : Set.Iic p0) (N : NiceCliqueName P W1 W2 G) := BlockAt σ source a p.val N
  let K (_ : W1) (_ : Set.Iic p0) (_ : NiceCliqueName P W1 W2 G) : Prop := True
  let J (p : Set.Iic p0) (N M : NiceCliqueName P W1 W2 G) := (joinedName N M).holds p.val ()
  have hextend : RelationalExtension R K J := by
    intro i p selected hcount hselected
    obtain ⟨q, hqp, M, hM, hjoined⟩ := exists_block_after_countable ha p.val
      (source.persistent p.property hp0) selected hcount hselected
    exact ⟨⟨q, hqp.trans p.property⟩, hqp, M, hM, trivial, hjoined⟩
  obtain ⟨F, hF, hcross⟩ := exists_relational_decisions
    (Erdos1172Part3ClosedDenseRequirements.countablyClosed_Iic hclosed p0) R K J
    (fun hqp h => blockAt_persistent hqp h) (fun _ h => h)
    (fun {p q N M} hqp h => (joinedName N M).persistent hqp h) hextend
  exact ⟨F, fun p i N hN => (hF p i N hN).1, hcross⟩

end Erdos1172Part3NamedBlockSequence
