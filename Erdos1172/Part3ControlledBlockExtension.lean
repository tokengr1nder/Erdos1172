/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CountableBlockExtension
public import Erdos1172.Part3NamedNeighborhoodStep

@[expose] public section

/-!
# Countable block extension with local-neighborhood control

The new block follows a further actual local neighborhood as well as all
earlier blocks. Deciding countably many active cut predicates then gives
uniform control over every later strengthening of the resulting block.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3ControlledBlockExtension

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularCliqueNeighborhoods (containedIn cliqueFunction)
open Erdos1172Part3RegularBlockEnvironment (GoodBlockCut)
open Erdos1172Part3CountableBlockExtension (BlockAt blockAt_persistent joinedName)
open Erdos1172Part3LocalCountableIntersection (exists_local_intersection_code)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3CountableRankClosure (Local)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3NamedNeighborhoodStep (Active mk_active_le)

variable {P : Type} [Preorder P] {G H : SimpleGraph W2}
variable {r : Code P W1 G ↪ W2} {σ : NiceCliqueName P W1 W2 G ↪ W2}
variable {source : RegularName P W2} {a : W2}

theorem exists_block_after_countable_in_code (ha : GoodBlockCut r σ H source a)
    (p : P) (hp : source.holds p a)
    (selected : Set (NiceCliqueName P W1 W2 G)) (hcount : selected.Countable)
    (hselected : ∀ N ∈ selected, BlockAt σ source a p N)
    (d : Code P W1 G) (hd : r d < a) (hda : (eval G H d).holds p a) :
    ∃ q : P, q ≤ p ∧ ∃ M : NiceCliqueName P W1 W2 G,
      BlockAt σ source a q M ∧ (∀ N ∈ selected, (joinedName N M).holds q ()) ∧
        (containedIn (cliqueFunction M.toClique) (eval G H d)).holds q () := by
  have hindex : #(Option selected) ≤ ℵ₀ := by
    rw [Cardinal.mk_option]
    exact (add_le_add (Cardinal.le_aleph0_iff_set_countable.mpr hcount)
      Cardinal.one_le_aleph0).trans_eq (Cardinal.add_eq_self le_rfl)
  let codes : Option selected → Code P W1 G
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
  obtain ⟨q, hqp, M, hM, hbelow, hsource, hafter⟩ :=
    Erdos1172Part3RegularLocalBlock.exists_block_refinement (ha.blocks c hc p hp hca)
  have hcontains (t : P) (htq : t ≤ q) (i : W1) (x : W2) (hx : M.toClique.decides t i x) :
      ∀ j, (eval G H (codes j)).holds t x := by
    have h := (hsource t htq i x hx).2
    rwa [heval] at h
  exact ⟨q, hqp, M, ⟨hM, hbelow, fun t htq i x hx => (hsource t htq i x hx).1, hafter⟩,
    fun N hN t htq i x hx => hcontains t htq i x hx (some ⟨N, hN⟩),
    fun t htq i x hx => hcontains t htq i x hx none⟩

def BlockControl (H : SimpleGraph W2) (index : Local r a ↪ W1)
    (i : W1) (p : P) (N : NiceCliqueName P W1 W2 G) : Prop :=
  ∀ c : Local r a, index c < i → ∀ q : P, q ≤ p → (eval G H c.val).holds q a →
    (containedIn (cliqueFunction N.toClique) (eval G H c.val)).holds q ()

theorem blockControl_persistent {index : Local r a ↪ W1} {i : W1} {p q : P}
    {N : NiceCliqueName P W1 W2 G} (hqp : q ≤ p) (h : BlockControl H index i p N) :
    BlockControl H index i q N := fun c hc s hsq => h c hc s (hsq.trans hqp)

theorem exists_controlled_block_extension (hclosed : CountablyClosed P)
    (ha : GoodBlockCut r σ H source a) (index : Local r a ↪ W1) (i : W1)
    (p : P) (hp : source.holds p a)
    (selected : Set (NiceCliqueName P W1 W2 G)) (hcount : selected.Countable)
    (hselected : ∀ N ∈ selected, BlockAt σ source a p N) :
    ∃ q : P, q ≤ p ∧ ∃ M : NiceCliqueName P W1 W2 G,
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
  let codes (c : Active index i) : Code P W1 G :=
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
  obtain ⟨s, hsq, M, hM, hjoined, hcontains⟩ := exists_block_after_countable_in_code ha q
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

end Erdos1172Part3ControlledBlockExtension
