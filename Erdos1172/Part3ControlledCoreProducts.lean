/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3RankedCoreBlockAssembly

@[expose] public section

/-!
# Neighborhood-convergent products of locally ranked cores

Countably many active local predicates are decided before each whole
block is chosen. Every later strengthening then retains all of those
neighborhood implications. The product convergence conclusion concerns
whole inner blocks, for any small linearly ordered inner index.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3ControlledCoreProducts

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularCliqueNeighborhoods (containedIn cliqueFunction)
open Erdos1172Part3RankedCoreBlockAssembly
open Erdos1172Part3LocalCountableIntersection (exists_local_intersection_code)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName exists_nice_clique_name)
open Erdos1172Part3CountableRankClosure (Local mk_local_le)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions DenseBelow)
open Erdos1172Part3NamedNeighborhoodStep (Active mk_active_le)
open Erdos1172Part3NamedBlockFlattening (joinedCores onConeCore joinedCores_onCone flatten)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3StationaryDecisions (OmegaTwoCC exists_predense_antichain)
open Erdos1172Part3RelationalDecisionFusion (RelationalExtension exists_relational_decisions)
open Erdos1172Part3NamedCliqueMixing (mixCore decides_on_branch)

variable {P I : Type} [Preorder P] [LinearOrder I] {G H : SimpleGraph W2}
variable {r : Code P I G ↪ W2} {σ : NiceCliqueName P I W2 G ↪ W2}
variable {source : RegularName P W2} {a : W2}

theorem exists_block_in_code (ha : GoodCoreCut r σ H source a)
    (p : P) (hp : source.holds p a)
    (selected : Set (NiceCliqueName P I W2 G)) (hcount : selected.Countable)
    (hselected : ∀ N ∈ selected, BlockAt σ source a p N)
    (d : Code P I G) (hd : r d < a) (hda : (eval G H d).holds p a) :
    ∃ q : P, q ≤ p ∧ ∃ M : NiceCliqueName P I W2 G,
      BlockAt σ source a q M ∧ (∀ N ∈ selected, (joinedName N M).holds q ()) ∧
        (containedIn (cliqueFunction M.toClique) (eval G H d)).holds q () := by
  have hindex : #(Option selected) ≤ ℵ₀ := by
    rw [Cardinal.mk_option]
    exact (add_le_add (Cardinal.le_aleph0_iff_set_countable.mpr hcount)
      Cardinal.one_le_aleph0).trans_eq (Cardinal.add_eq_self le_rfl)
  let codes : Option selected → Code P I G
    | none => d
    | some N => blockName N.val
  obtain ⟨c, hc, heval⟩ := exists_local_intersection_code ha.goodCut hindex codes (by
    intro j
    cases j with
    | none => exact hd
    | some N => exact ha.goodCut.block_lt N.val (hselected N.val N.property).1)
  have hca : (eval G H c).holds p a := by
    rw [heval]
    intro j
    cases j with
    | none => exact hda
    | some N => exact (hselected N.val N.property).2.2.2
  obtain ⟨q, hqp, M, hM, hbelow, hsource, hafter⟩ := (ha.blocks c hc p hp hca) p le_rfl
  have hcontains (t : P) (htq : t ≤ q) (i : I) (x : W2) (hx : M.toClique.decides t i x) :
      ∀ j, (eval G H (codes j)).holds t x := by
    have h := (hsource t htq i x hx).2
    rwa [heval] at h
  exact ⟨q, hqp, M, ⟨hM, hbelow, fun t htq i x hx => (hsource t htq i x hx).1, hafter⟩,
    fun N hN t htq i x hx => hcontains t htq i x hx (some ⟨N, hN⟩),
    fun t htq i x hx => hcontains t htq i x hx none⟩

def BlockControl (H : SimpleGraph W2) (index : Local r a ↪ W1)
    (i : W1) (p : P) (N : NiceCliqueName P I W2 G) : Prop :=
  ∀ c : Local r a, index c < i → ∀ q : P, q ≤ p → (eval G H c.val).holds q a →
    (containedIn (cliqueFunction N.toClique) (eval G H c.val)).holds q ()

theorem blockControl_persistent {index : Local r a ↪ W1} {i : W1} {p q : P}
    {N : NiceCliqueName P I W2 G} (hqp : q ≤ p) (h : BlockControl H index i p N) :
    BlockControl H index i q N := fun c hc s hsq => h c hc s (hsq.trans hqp)

theorem exists_controlled_block_extension (hclosed : CountablyClosed P)
    (ha : GoodCoreCut r σ H source a) (index : Local r a ↪ W1) (i : W1)
    (p : P) (hp : source.holds p a)
    (selected : Set (NiceCliqueName P I W2 G)) (hcount : selected.Countable)
    (hselected : ∀ N ∈ selected, BlockAt σ source a p N) :
    ∃ q : P, q ≤ p ∧ ∃ M : NiceCliqueName P I W2 G,
      BlockAt σ source a q M ∧ (∀ N ∈ selected, (joinedName N M).holds q ()) ∧
        BlockControl H index i q M := by
  classical
  let D (q : P) (c : Active index i) : Prop :=
    (eval G H c.val.val).holds q a ∨ (neg (eval G H c.val.val)).holds q a
  obtain ⟨q, hqp, hdec⟩ := Erdos1172Part3RegularNamedIdeal.exists_common_countable_witnesses
    hclosed p D (by
      intro p q c hqp h
      rcases h with h | h
      · exact Or.inl ((eval G H c.val.val).persistent hqp h)
      · exact Or.inr ((neg (eval G H c.val.val)).persistent hqp h))
    (fun s _ c => exists_deciding_refinement (eval G H c.val.val) s a) (mk_active_le index i)
  let codes (c : Active index i) : Code P I G :=
    if (eval G H c.val.val).holds q a then c.val.val else SmallUnionCode.compl SmallUnionCode.empty
  have hcodes (c : Active index i) : r (codes c) < a := by
    dsimp only [codes]
    split_ifs
    · exact c.val.property
    · exact ha.goodCut.compl_lt _ ha.goodCut.empty_lt
  obtain ⟨d, hd, heval⟩ := exists_local_intersection_code ha.goodCut (mk_active_le index i) codes hcodes
  have hda : (eval G H d).holds q a := by
    rw [heval]
    intro c
    dsimp only [codes]
    split_ifs with h
    · exact h
    · rw [eval_compl, eval_empty]
      intro s hsq hs
      exact hs
  obtain ⟨s, hsq, M, hM, hjoined, hcontains⟩ := exists_block_in_code ha q
    (source.persistent hqp hp) selected hcount
    (fun N hN => blockAt_persistent hqp (hselected N hN)) d hd hda
  refine ⟨s, hsq.trans hqp, M, hM, hjoined, ?_⟩
  intro c hci t hts hct
  let j : Active index i := ⟨c, hci⟩
  by_cases hcq : (eval G H c.val).holds q a
  · intro v hvt k x hx
    change (eval G H c.val).holds v x
    have h := hcontains v (hvt.trans hts) k x hx
    rw [heval] at h
    have hj := h j
    simpa only [codes, j, if_pos hcq] using hj
  · exact ((hdec j).resolve_left hcq t (hts.trans hsq) hct).elim

def ProductConvergesBelow (r : Code P I G ↪ W2) (H : SimpleGraph W2) (a : W2)
    (p0 : P) (core : CliqueDecisions P (W1 ×ₗ I) W2 G) : Prop :=
  ∀ c : Code P I G, r c < a → ∃ bound : W1,
    ∀ p : P, p ≤ p0 → (eval G H c).holds p a →
      ∀ z : W1 ×ₗ I, bound < (ofLex z).1 → ∀ x : W2,
        core.decides p z x → (eval G H c).holds p x

theorem exists_controlled_block_sequence (hclosed : CountablyClosed P)
    (ha : GoodCoreCut r σ H source a) (index : Local r a ↪ W1)
    (p0 : P) (hp0 : source.holds p0 a) :
    ∃ F : FunctionDecisions (Set.Iic p0) W1 (NiceCliqueName P I W2 G),
      (∀ p i N, F.decides p i N → BlockAt σ source a p.val N ∧ BlockControl H index i p.val N) ∧
      ∀ p i j N M, i < j → F.decides p i N → F.decides p j M →
        (joinedName N M).holds p.val () := by
  let R (p : Set.Iic p0) (N : NiceCliqueName P I W2 G) := BlockAt σ source a p.val N
  let K (i : W1) (p : Set.Iic p0) (N : NiceCliqueName P I W2 G) := BlockControl H index i p.val N
  let J (p : Set.Iic p0) (N M : NiceCliqueName P I W2 G) := (joinedName N M).holds p.val ()
  have hextend : RelationalExtension R K J := by
    intro i p selected hcount hselected
    obtain ⟨q, hqp, M, hM, hjoined, hcontrol⟩ := exists_controlled_block_extension hclosed ha index i
      p.val (source.persistent p.property hp0) selected hcount hselected
    exact ⟨⟨q, hqp.trans p.property⟩, hqp, M, hM, hcontrol, hjoined⟩
  exact exists_relational_decisions
    (Erdos1172Part3ClosedDenseRequirements.countablyClosed_Iic hclosed p0) R K J
    (fun hqp h => blockAt_persistent hqp h) (fun hqp h => blockControl_persistent hqp h)
    (fun {p q N M} hqp h => (joinedName N M).persistent hqp h) hextend

theorem exists_cone_convergent_product (hclosed : CountablyClosed P)
    (ha : GoodCoreCut r σ H source a) (p0 : P) (hp0 : source.holds p0 a) :
    ∃ core : CliqueDecisions (Set.Iic p0) (W1 ×ₗ I) W2 G,
      (∀ p z x, core.decides p z x → source.holds p.val x ∧ x < a ∧ G.Adj x a) ∧
      ∀ c : Code P I G, r c < a → ∃ bound : W1,
        ∀ p : Set.Iic p0, (eval G H c).holds p.val a →
          ∀ z : W1 ×ₗ I, bound < (ofLex z).1 → ∀ x : W2,
            core.decides p z x → (eval G H c).holds p.val x := by
  obtain ⟨index⟩ : Nonempty (Local r a ↪ W1) := (Cardinal.le_def _ _).mp (by
    simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using mk_local_le r a)
  obtain ⟨F, hF, hcross⟩ := exists_controlled_block_sequence hclosed ha index p0 hp0
  let blocks (N : NiceCliqueName P I W2 G) := onConeCore p0 N.toClique
  have hj : ∀ p i j N M, i < j → F.decides p i N → F.decides p j M →
      (joinedCores (blocks N) (blocks M)).holds p () :=
    fun p i j N M hij hN hM => joinedCores_onCone p0 N.toClique M.toClique p
      (hcross p i j N M hij hN hM)
  refine ⟨flatten blocks F hj, ?_, ?_⟩
  · rintro p z x ⟨N, hN, hx⟩
    have h := (hF p (ofLex z).1 N hN).1
    exact ⟨h.2.2.1 p.val le_rfl (ofLex z).2 x hx,
      h.2.2.2 p.val le_rfl (ofLex z).2 x hx⟩
  · intro c hc
    refine ⟨index ⟨c, hc⟩, ?_⟩
    rintro p hca z hz x ⟨N, hN, hx⟩
    exact (hF p (ofLex z).1 N hN).2 ⟨c, hc⟩ hz p.val le_rfl hca
      p.val le_rfl (ofLex z).2 x hx

theorem exists_nice_convergent_product (hclosed : CountablyClosed P) (hcc : OmegaTwoCC P)
    (hI : #I ≤ ℵ_ 1) (ha : GoodCoreCut r σ H source a) (p0 : P) (hp0 : source.holds p0 a) :
    ∃ N : NiceCliqueName P (W1 ×ₗ I) W2 G,
      (∀ p z x, N.toClique.decides p z x → x < a ∧ G.Adj x a) ∧
      (∀ p : P, p ≤ p0 → ∀ z x, N.toClique.decides p z x → source.holds p x) ∧
      ProductConvergesBelow r H a p0 N.toClique := by
  obtain ⟨core, hcore, hconv⟩ := exists_cone_convergent_product hclosed ha p0 hp0
  obtain ⟨global, hbelow, horigin⟩ :=
    Erdos1172Part3CliqueConeExtension.exists_global_clique_from_cone hclosed p0 core (mk_product_le hI)
  obtain ⟨N, hN⟩ := exists_nice_clique_name hcc global
  refine ⟨N, ?_, ?_, ?_⟩
  · intro p z x hx
    obtain ⟨q, hq⟩ := horigin p z x (hN p z x hx)
    exact (hcore q z x hq).2
  · intro p hpp0 z x hx
    exact (hcore ⟨p, hpp0⟩ z x ((hbelow p hpp0 z x).mp (hN p z x hx))).1
  · intro c hc
    obtain ⟨bound, hbound⟩ := hconv c hc
    refine ⟨bound, ?_⟩
    intro p hpp0 hca z hz x hx
    exact hbound ⟨p, hpp0⟩ hca z hz x ((hbelow p hpp0 z x).mp (hN p z x hx))

def GuardedProductConverges (r : Code P I G ↪ W2) (H : SimpleGraph W2)
    (source : RegularName P W2) (a : W2) (core : CliqueDecisions P (W1 ×ₗ I) W2 G) : Prop :=
  ∀ c : Code P I G, r c < a → ∀ p : P,
    source.holds p a → (eval G H c).holds p a → ∀ q : P, q ≤ p →
      ∃ s : P, s ≤ q ∧ ∃ bound : W1, ∀ t : P, t ≤ s →
        ∀ z : W1 ×ₗ I, bound < (ofLex z).1 → ∀ x : W2,
          core.decides t z x → (eval G H c).holds t x

structure ProductData (r : Code P I G ↪ W2) (H : SimpleGraph W2)
    (source : RegularName P W2) (a : W2) where
  name : NiceCliqueName P (W1 ×ₗ I) W2 G
  geometry : ∀ p z x, name.toClique.decides p z x → x < a ∧ G.Adj x a
  actual_source : ∀ p : P, source.holds p a → ∀ z x,
    name.toClique.decides p z x → source.holds p x
  converges : GuardedProductConverges r H source a name.toClique

theorem exists_guarded_source_product (hclosed : CountablyClosed P) (hcc : OmegaTwoCC P)
    (hI : #I ≤ ℵ_ 1) (ha : GoodCoreCut r σ H source a) (hpossible : ∃ p : P, source.holds p a) :
    Nonempty (ProductData r H source a) := by
  classical
  obtain ⟨p0, hp0⟩ := hpossible
  obtain ⟨fallback, hgeometry, _⟩ := exists_nice_convergent_product hclosed hcc hI ha p0 hp0
  let D : Set P := {p | source.holds p a ∨ (neg source).holds p a}
  have hD : DenseBelow D := by
    intro p
    obtain ⟨q, hqp, hq⟩ := exists_deciding_refinement source p a
    exact ⟨q, hq, hqp⟩
  obtain ⟨A, hAD, hA, hpredense⟩ := exists_predense_antichain D hD
  have hex (b : A) : ∃ N : NiceCliqueName P (W1 ×ₗ I) W2 G,
      (∀ p z x, N.toClique.decides p z x → x < a ∧ G.Adj x a) ∧
      (source.holds b.val a →
        (∀ p : P, p ≤ b.val → ∀ z x, N.toClique.decides p z x → source.holds p x) ∧
        ProductConvergesBelow r H a b.val N.toClique) := by
    by_cases hb : source.holds b.val a
    · obtain ⟨N, hg, hs, hc⟩ := exists_nice_convergent_product hclosed hcc hI ha b.val hb
      exact ⟨N, hg, fun _ => ⟨hs, hc⟩⟩
    · exact ⟨fallback, hgeometry, fun h => (hb h).elim⟩
  choose names hnames using hex
  let blocks (b : A) := (names b).toClique
  let core := mixCore hA hpredense blocks
  have hpositive (b : A) (p : P) (hpb : p ≤ b.val) (hp : source.holds p a) :
      source.holds b.val a :=
    (hAD b.property).resolve_right (fun hn => hn p hpb hp)
  obtain ⟨N, hN⟩ := exists_nice_clique_name hcc core
  refine ⟨⟨N, fun p z x hx => ?_, fun p hp z x hx => ?_, fun c hc p hp hca q hqp => ?_⟩⟩
  · obtain ⟨b, _, hb⟩ := hN p z x hx
    exact (hnames b).1 p z x hb
  · obtain ⟨b, hpb, hb⟩ := hN p z x hx
    exact ((hnames b).2 (hpositive b p hpb hp)).1 p hpb z x hb
  · obtain ⟨b, hbA, s, hsq, hsb⟩ := hpredense q
    let branch : A := ⟨b, hbA⟩
    obtain ⟨bound, hbound⟩ := ((hnames branch).2
      (hpositive branch s hsb (source.persistent (hsq.trans hqp) hp))).2 c hc
    exact ⟨s, hsq, bound, fun t hts z hz x hx => hbound t (hts.trans hsb)
      ((eval G H c).persistent ((hts.trans hsq).trans hqp) hca) z hz x
      (decides_on_branch hA blocks branch t (hts.trans hsb) z x (hN t z x hx))⟩

end Erdos1172Part3ControlledCoreProducts
