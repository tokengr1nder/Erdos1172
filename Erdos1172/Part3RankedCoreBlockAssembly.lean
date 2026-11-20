/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3LocalSquareReflection
public import Erdos1172.Part3NamedBlockFlattening

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

theorem exists_block_after_countable (ha : GoodCoreCut r σ H source a)
    (p : P) (hp : source.holds p a)
    (selected : Set (NiceCliqueName P I W2 G)) (hcount : selected.Countable)
    (hselected : ∀ N ∈ selected, BlockAt σ source a p N) :
    ∃ q : P, q ≤ p ∧ ∃ M : NiceCliqueName P I W2 G,
      BlockAt σ source a q M ∧ ∀ N ∈ selected, (joinedName N M).holds q () := by
  obtain ⟨c, hc, hcode⟩ := Erdos1172Part3LocalCountableIntersection.exists_local_after_code
    ha.goodCut selected hcount (fun N hN => (hselected N hN).1)
  have hca : (eval G H c).holds p a :=
    (hcode p a).mpr (fun N hN => (hselected N hN).2.2.2)
  obtain ⟨q, hqp, M, hM, hbelow, hsource, hafter⟩ := (ha.blocks c hc p hp hca) p le_rfl
  refine ⟨q, hqp, M, ⟨hM, hbelow, ?_, hafter⟩, ?_⟩
  · intro t htq i x hx
    exact (hsource t htq i x hx).1
  · intro N hN t htq i x hx
    exact (hcode t x).mp (hsource t htq i x hx).2 N hN

theorem exists_block_sequence (hclosed : CountablyClosed P) (ha : GoodCoreCut r σ H source a)
    (p0 : P) (hp0 : source.holds p0 a) :
    ∃ F : FunctionDecisions (Set.Iic p0) W1 (NiceCliqueName P I W2 G),
      (∀ p i N, F.decides p i N → BlockAt σ source a p.val N) ∧
      ∀ p i j N M, i < j → F.decides p i N → F.decides p j M →
        (joinedName N M).holds p.val () := by
  let R (p : Set.Iic p0) (N : NiceCliqueName P I W2 G) := BlockAt σ source a p.val N
  let K (_ : W1) (_ : Set.Iic p0) (_ : NiceCliqueName P I W2 G) : Prop := True
  let J (p : Set.Iic p0) (N M : NiceCliqueName P I W2 G) := (joinedName N M).holds p.val ()
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

theorem exists_cone_source_product (hclosed : CountablyClosed P)
    (ha : GoodCoreCut r σ H source a) (p0 : P) (hp0 : source.holds p0 a) :
    ∃ core : CliqueDecisions (Set.Iic p0) (W1 ×ₗ I) W2 G,
      ∀ p z x, core.decides p z x → source.holds p.val x ∧ x < a ∧ G.Adj x a := by
  obtain ⟨F, hF, hcross⟩ := exists_block_sequence hclosed ha p0 hp0
  let blocks (N : NiceCliqueName P I W2 G) := onConeCore p0 N.toClique
  have hj : ∀ p i j N M, i < j → F.decides p i N → F.decides p j M →
      (joinedCores (blocks N) (blocks M)).holds p () :=
    fun p i j N M hij hN hM => joinedCores_onCone p0 N.toClique M.toClique p
      (hcross p i j N M hij hN hM)
  refine ⟨flatten blocks F hj, ?_⟩
  rintro p z x ⟨N, hN, hx⟩
  have h := hF p (ofLex z).1 N hN
  exact ⟨h.2.2.1 p.val le_rfl (ofLex z).2 x hx,
    h.2.2.2 p.val le_rfl (ofLex z).2 x hx⟩

theorem mk_product_le (hI : #I ≤ ℵ_ 1) : #(W1 ×ₗ I) ≤ ℵ_ 1 := by
  change #(W1 × I) ≤ ℵ_ 1
  rw [Cardinal.mk_prod]
  simp only [Cardinal.lift_id, W1, Cardinal.mk_toType, Ordinal.card_omega]
  exact (mul_le_mul' le_rfl hI).trans_eq (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1))

theorem exists_nice_source_product (hclosed : CountablyClosed P) (hcc : OmegaTwoCC P)
    (hI : #I ≤ ℵ_ 1) (ha : GoodCoreCut r σ H source a) (p0 : P) (hp0 : source.holds p0 a) :
    ∃ N : NiceCliqueName P (W1 ×ₗ I) W2 G,
      (∀ p z x, N.toClique.decides p z x → x < a ∧ G.Adj x a) ∧
      (∀ p : P, p ≤ p0 → ∀ z x, N.toClique.decides p z x → source.holds p x) := by
  obtain ⟨core, hcore⟩ := exists_cone_source_product hclosed ha p0 hp0
  obtain ⟨global, hbelow, horigin⟩ :=
    Erdos1172Part3CliqueConeExtension.exists_global_clique_from_cone hclosed p0 core (mk_product_le hI)
  obtain ⟨N, hN⟩ := exists_nice_clique_name hcc global
  refine ⟨N, ?_, ?_⟩
  · intro p z x hx
    obtain ⟨q, hq⟩ := horigin p z x (hN p z x hx)
    exact (hcore q z x hq).2
  · intro p hpp0 z x hx
    exact (hcore ⟨p, hpp0⟩ z x ((hbelow p hpp0 z x).mp (hN p z x hx))).1

end Erdos1172Part3RankedCoreBlockAssembly
