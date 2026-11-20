/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3LocalRedBlock

@[expose] public section

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3WholeBlockFusion

open Erdos1172Part3CoreObjectCode Erdos1172Part3LocalRedBlock
open Erdos1172Part3NeighborhoodCode (W2)
open ErdosRadoCHAsym (W1)
open Erdos1172Part3ConvergentCore (mk_Iio_W1_lt)

theorem exists_local_countable_union {r : Code ↪ W2} {σ : Obj ↪ W2}
    {G H : SimpleGraph W2} {a : W2} (ha : GoodCut r σ G H a)
    {I : Type} (hI : #I < ℵ_ 1) (s : I → Obj) (hs : ∀ i, σ (s i) < a) :
    ∃ u : Obj, σ u < a ∧ ∀ x : W2, x ∈ u.val ↔ ∃ i : I, x ∈ (s i).val := by
  classical
  obtain ⟨e⟩ : Nonempty (I ↪ ℕ) := (Cardinal.le_def _ _).mp
    (by simpa only [Cardinal.mk_nat] using Cardinal.lt_aleph_one_iff.mp hI)
  let seq (n : ℕ) : Obj := if h : ∃ i, e i = n then s h.choose else objEmpty
  have hseq : ∀ n, σ (seq n) < a := by
    intro n
    dsimp only [seq]
    split_ifs with h
    · exact hs h.choose
    · exact ha.object_empty_lt
  refine ⟨objUnion seq, ha.object_union_lt seq hseq, ?_⟩
  intro x
  change x ∈ ⋃ n, (seq n).val ↔ _
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    dsimp only [seq] at hn
    split_ifs at hn with h
    · exact ⟨h.choose, hn⟩
    · exact hn.elim
  · rintro ⟨i, hi⟩
    apply Set.mem_iUnion.mpr
    refine ⟨e i, ?_⟩
    have hex : ∃ j, e j = e i := ⟨i, rfl⟩
    have heq : hex.choose = i := e.injective hex.choose_spec
    simpa only [seq, dif_pos hex, heq] using hi

/-- Assemble omegaOne many whole omegaOne blocks below a single local
cut. The union of the earlier blocks is named at every countable stage;
there is no intersection of decreasing stationary sets. -/
theorem exists_red_square_core {r : Code ↪ W2} {σ : Obj ↪ W2}
    {G H : SimpleGraph W2} {source : Set W2} {a : W2}
    (ha : GoodCut r σ G H a) (hlocal : LocalRedBlock r σ G H source a) :
    ∃ core : Set W2, core ⊆ source ∧ G.IsClique core ∧
      typeLT core = (ω_ 1) ^ (2 : Ordinal.{0}) ∧
        ∀ x ∈ core, x < a ∧ G.Adj x a := by
  classical
  let Block := {s : Obj // σ s < a ∧ s.val ⊆ source ∧ G.IsClique s.val ∧
    typeLT s.val = ω_ 1 ∧ a ∈ afterRed G s}
  have step (i : W1) (previous : ∀ j, j < i → Block) :
      ∃ next : Block, ∀ j (hj : j < i), ∀ x ∈ (previous j hj).val.val,
        ∀ y ∈ next.val.val, x < y ∧ G.Adj x y := by
    obtain ⟨u, hu, humem⟩ := exists_local_countable_union ha (mk_Iio_W1_lt i)
      (fun j : Set.Iio i => (previous j.val j.property).val)
      (fun j => (previous j.val j.property).property.1)
    have hau : a ∈ afterRed G u := by
      intro x hx
      obtain ⟨j, hj⟩ := (humem x).mp hx
      exact (previous j.val j.property).property.2.2.2.2 x hj
    obtain ⟨c, hc, hcs, hcl, hct, hca⟩ := hlocal (objectName u) (ha.object_name_lt u hu) hau
    refine ⟨⟨c, hc, hcs.trans Set.inter_subset_left, hcl, hct, hca⟩, ?_⟩
    intro j hj x hx y hy
    exact (hcs hy).2 x ((humem x).mpr ⟨⟨j, hj⟩, hx⟩)
  let next (i : W1) (previous : ∀ j, j < i → Block) : Block := (step i previous).choose
  let branch : W1 → Block := WellFoundedLT.fix next
  have hbranch (i : W1) : (step i (fun j _ => branch j)).choose = branch i := by
    change next i (fun j _ => WellFoundedLT.fix next j) = WellFoundedLT.fix next i
    rw [WellFoundedLT.fix_eq]
  have hcross (i j : W1) (hij : i < j) : ∀ x ∈ (branch i).val.val,
      ∀ y ∈ (branch j).val.val, x < y ∧ G.Adj x y := by
    have h := (step j (fun k _ => branch k)).choose_spec i hij
    rwa [hbranch] at h
  let blocks (i : W1) : Set W2 := (branch i).val.val
  have hclique : G.IsClique (⋃ i, blocks i) := SimpleGraph.IsClique.iUnion_of_lt_cross
    G blocks (fun i => (branch i).property.2.2.1)
    (fun i j hij x hx y hy => (hcross i j hij x hx y hy).2)
  have embeddings (i : W1) : Nonempty (W1 ↪o blocks i) := by
    have htype : typeLT W1 ≤ typeLT (blocks i) := by
      rw [(branch i).property.2.2.2.1]
      simp only [W1, Ordinal.type_toType, le_refl]
    obtain ⟨e⟩ := Ordinal.type_le_iff.mp htype
    exact ⟨e.toOrderEmbedding⟩
  let maps (i : W1) : W1 ↪o blocks i := Classical.choice (embeddings i)
  let points (p : W1 ×ₗ W1) : W2 := (maps (ofLex p).1 (ofLex p).2).val
  have hstrict : StrictMono points := by
    intro p q hpq
    rw [Prod.Lex.lt_iff] at hpq
    rcases hpq with hout | ⟨heq, hinner⟩
    · exact (hcross _ _ hout _ (maps _ _).property _ (maps _ _).property).1
    · dsimp only [points]
      rw [heq]
      exact (maps (ofLex q).1).strictMono hinner
  have hrange : Set.range points ⊆ ⋃ i, blocks i := by
    rintro x ⟨p, rfl⟩
    exact Set.mem_iUnion.mpr ⟨(ofLex p).1, (maps _ _).property⟩
  refine ⟨Set.range points, ?_, hclique.subset hrange, ?_, ?_⟩
  · rintro x ⟨p, rfl⟩
    exact (branch (ofLex p).1).property.2.1 (maps _ _).property
  · rw [Ordinal.typeLT_range_of_strictMono points hstrict]
    change Ordinal.type (Prod.Lex ((· < ·) : W1 → W1 → Prop)
      ((· < ·) : W1 → W1 → Prop)) = _
    rw [Ordinal.type_prod_lex]
    simp only [W1, Ordinal.type_toType]
    rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, Ordinal.opow_add_one, Ordinal.opow_one]
  · rintro x ⟨p, rfl⟩
    exact (branch (ofLex p).1).property.2.2.2.2 _ (maps _ _).property

end Erdos1172Part3WholeBlockFusion
