/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3TransfiniteRankedFailures

@[expose] public section

/-!
# Assembling arbitrary locally ranked cores into an omegaOne product

The inner index is any linear order, not only omegaOne. Locally ranked
availability supplies a fresh whole block after every countable family
of earlier blocks. Countably closed relational fusion chooses omegaOne
many compatible blocks, and flattening retains all cross-block order and
edges. No final omegaOne-chain lower bound is assumed.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3RankedCoreBlockAssembly

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularCliqueNeighborhoods (afterClique containedIn cliqueFunction)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName exists_nice_clique_name)
open Erdos1172Part3RankedWitnessRestriction (rankedAvailability)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3StationaryDecisions (OmegaTwoCC)
open Erdos1172Part3NamedBlockFlattening (joinedCores onConeCore joinedCores_onCone flatten)
open Erdos1172Part3RelationalDecisionFusion (RelationalExtension exists_relational_decisions)

variable {P I : Type} [Preorder P] [LinearOrder I] {G H : SimpleGraph W2}

structure GoodCoreCut (r : Code P I G ↪ W2) (σ : NiceCliqueName P I W2 G ↪ W2)
    (H : SimpleGraph W2) (source : RegularName P W2) (a : W2) : Prop where
  goodCut : GoodCut r σ H source a
  blocks : ∀ c : Code P I G, r c < a → ∀ p : P,
    source.holds p a → (eval G H c).holds p a →
      (rankedAvailability σ (meet source (eval G H c))).holds p a

def BlockAt (σ : NiceCliqueName P I W2 G ↪ W2) (source : RegularName P W2)
    (a : W2) (p : P) (N : NiceCliqueName P I W2 G) : Prop :=
  σ N < a ∧ (∀ q i x, N.toClique.decides q i x → x < a) ∧
    (containedIn (cliqueFunction N.toClique) source).holds p () ∧
    (afterClique N.toClique).holds p a

noncomputable def joinedName (N M : NiceCliqueName P I W2 G) : RegularName P Unit :=
  joinedCores N.toClique M.toClique

variable {r : Code P I G ↪ W2} {σ : NiceCliqueName P I W2 G ↪ W2}
variable {source : RegularName P W2} {a : W2}

theorem blockAt_persistent {p q : P} {N : NiceCliqueName P I W2 G}
    (hqp : q ≤ p) (h : BlockAt σ source a p N) : BlockAt σ source a q N :=
  ⟨h.1, h.2.1, (containedIn (cliqueFunction N.toClique) source).persistent hqp h.2.2.1,
    (afterClique N.toClique).persistent hqp h.2.2.2⟩

theorem mk_product_le (hI : #I ≤ ℵ_ 1) : #(W1 ×ₗ I) ≤ ℵ_ 1 := by
  change #(W1 × I) ≤ ℵ_ 1
  rw [Cardinal.mk_prod]
  simp only [Cardinal.lift_id, W1, Cardinal.mk_toType, Ordinal.card_omega]
  exact (mul_le_mul' le_rfl hI).trans_eq (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1))

end Erdos1172Part3RankedCoreBlockAssembly
