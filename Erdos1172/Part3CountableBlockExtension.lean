/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3LocalCountableIntersection

@[expose] public section

/-!
# A fresh red block after countably many named blocks

The cut's actual source membership and the earlier blocks' actual
common-red cut predicates are retained under one strengthening. The
new block is wholly in each earlier block's regular common-red future.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3CountableBlockExtension

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularCliqueNeighborhoods (afterClique containedIn cliqueFunction)
open Erdos1172Part3RegularBlockEnvironment (GoodBlockCut)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)

variable {P : Type} [Preorder P] {G H : SimpleGraph W2}
variable {r : Code P W1 G ↪ W2} {σ : NiceCliqueName P W1 W2 G ↪ W2}
variable {source : RegularName P W2} {a : W2}

def BlockAt (σ : NiceCliqueName P W1 W2 G ↪ W2) (source : RegularName P W2)
    (a : W2) (p : P) (N : NiceCliqueName P W1 W2 G) : Prop :=
  σ N < a ∧ (∀ q i x, N.toClique.decides q i x → x < a) ∧
    (containedIn (cliqueFunction N.toClique) source).holds p () ∧
    (afterClique N.toClique).holds p a

theorem blockAt_persistent {p q : P} {N : NiceCliqueName P W1 W2 G}
    (hqp : q ≤ p) (h : BlockAt σ source a p N) : BlockAt σ source a q N :=
  ⟨h.1, h.2.1, (containedIn (cliqueFunction N.toClique) source).persistent hqp h.2.2.1,
    (afterClique N.toClique).persistent hqp h.2.2.2⟩

noncomputable def joinedName (N M : NiceCliqueName P W1 W2 G) : RegularName P Unit :=
  containedIn (cliqueFunction M.toClique) (afterClique N.toClique)

theorem joinedName_cross {N M : NiceCliqueName P W1 W2 G} {p : P}
    (h : (joinedName N M).holds p ()) {i j : W1} {x y : W2}
    (hx : N.toClique.decides p i x) (hy : M.toClique.decides p j y) : x < y ∧ G.Adj x y :=
  h p le_rfl j y hy p le_rfl i x hx

theorem exists_block_after_countable (ha : GoodBlockCut r σ H source a)
    (p : P) (hp : source.holds p a)
    (selected : Set (NiceCliqueName P W1 W2 G)) (hcount : selected.Countable)
    (hselected : ∀ N ∈ selected, BlockAt σ source a p N) :
    ∃ q : P, q ≤ p ∧ ∃ M : NiceCliqueName P W1 W2 G,
      BlockAt σ source a q M ∧ ∀ N ∈ selected, (joinedName N M).holds q () := by
  obtain ⟨c, hc, hcode⟩ := Erdos1172Part3LocalCountableIntersection.exists_local_after_code
    ha.goodCut selected hcount (fun N hN => (hselected N hN).1)
  have hca : (eval G H c).holds p a :=
    (hcode p a).mpr (fun N hN => (hselected N hN).2.2.2)
  obtain ⟨q, hqp, M, hM, hbelow, hsource, hafter⟩ :=
    Erdos1172Part3RegularLocalBlock.exists_block_refinement (ha.blocks c hc p hp hca)
  refine ⟨q, hqp, M, ⟨hM, hbelow, ?_, hafter⟩, ?_⟩
  · intro t htq i x hx
    exact (hsource t htq i x hx).1
  · intro N hN t htq i x hx
    exact (hcode t x).mp (hsource t htq i x hx).2 N hN

end Erdos1172Part3CountableBlockExtension
