/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3WholeBlockFusion
public import Erdos1172.Part3SquareLossBounds

@[expose] public section

/-!
# Square cores with ordinal-small traces

Whole-block fusion can be arranged to converge to every locally named
neighborhood. A locally small set then meets only a bounded initial
collection of rows. Its trace has order type strictly below omegaOne
squared, without any assertion that the trace is countable.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3ConvergentSquareCore

open Erdos1172Part3CoreObjectCode Erdos1172Part3CoreObjectIdeal
open Erdos1172Part3LocalRedBlock
open Erdos1172Part3WholeBlockFusion (exists_local_countable_union)
open Erdos1172Part3CountableRankClosure (Local mk_local_le)
open Erdos1172Part3ConvergentCore (mk_Iio_W1_lt)
open Erdos1172Part3StationarySquareDecisions (Square tail lt_tail)
open Erdos1172Part3SquareLossBounds (typeLT_square)
open ErdosRadoCHAsym (W1 W2)

variable {r : Code ↪ W2} {σ : Obj ↪ W2} {G H : SimpleGraph W2} {a : W2}

theorem exists_convergent_square_map (ha : GoodCut r σ G H a) (source : Set W2)
    (hlocal : LocalRedBlock r σ G H source a) :
    ∃ f : Square → W2, StrictMono f ∧ Set.range f ⊆ source ∧
      G.IsClique (Set.range f) ∧ (∀ z, f z < a ∧ G.Adj (f z) a) ∧
      ∀ c : Code, r c < a → a ∈ eval G H c →
        ∃ i : W1, ∀ z : Square, i < (ofLex z).1 → f z ∈ eval G H c := by
  classical
  obtain ⟨index⟩ : Nonempty (Local r a ↪ W1) := (Cardinal.le_def _ _).mp (by
    simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using mk_local_le r a)
  let Block := {s : Obj // σ s < a ∧ s.val ⊆ source ∧ G.IsClique s.val ∧
    typeLT s.val = ω_ 1 ∧ a ∈ afterRed G s}
  have step (i : W1) (previous : ∀ j, j < i → Block) :
      ∃ next : Block,
        (∀ j (hj : j < i), ∀ x ∈ (previous j hj).val.val,
          ∀ y ∈ next.val.val, x < y ∧ G.Adj x y) ∧
        ∀ c : Local r a, index c < i → a ∈ eval G H c.val →
          next.val.val ⊆ eval G H c.val := by
    obtain ⟨u, hu, humem⟩ := exists_local_countable_union ha (mk_Iio_W1_lt i)
      (fun j : Set.Iio i => (previous j.val j.property).val)
      (fun j => (previous j.val j.property).property.1)
    have hau : a ∈ afterRed G u := by
      intro x hx
      obtain ⟨j, hj⟩ := (humem x).mp hx
      exact (previous j.val j.property).property.2.2.2.2 x hj
    let active := {c : Local r a // index c < i ∧ a ∈ eval G H c.val}
    have hactive : #active < ℵ_ 1 := by
      let e : active ↪ Set.Iio i :=
        ⟨fun c => ⟨index c.val, c.property.1⟩,
          fun _ _ h => Subtype.ext (index.injective (congrArg Subtype.val h))⟩
      exact (Cardinal.mk_le_of_injective e.injective).trans_lt (mk_Iio_W1_lt i)
    let avoid : Set W2 := ⋃ c : active, (eval G H c.val.val)ᶜ
    have havoid : Small r G H a avoid := iUnion_small ha _ hactive
      (fun c => named_compl_small ha c.val.property c.property.2)
    have hsmall : Small r G H a (avoid ∪ (afterRed G u)ᶜ) :=
      union_small ha havoid (named_compl_small ha (ha.object_name_lt u hu) hau)
    obtain ⟨c, hc, hac, hcover⟩ := hsmall
    obtain ⟨block, hb, hbs, hbc, hbt, hba⟩ := hlocal (SmallUnionCode.compl c)
      (ha.compl_lt c hc) hac
    have hsafe (y : W2) (hy : y ∈ block.val) : y ∉ eval G H c := (hbs hy).2
    refine ⟨⟨block, hb, hbs.trans Set.inter_subset_left, hbc, hbt, hba⟩, ?_, ?_⟩
    · intro j hj x hx y hy
      have hyu : y ∈ afterRed G u := by
        by_contra h
        exact hsafe y hy (hcover (Or.inr h))
      exact hyu x ((humem x).mpr ⟨⟨j, hj⟩, hx⟩)
    · intro d hdi had y hy
      by_contra h
      exact hsafe y hy (hcover (Or.inl (Set.mem_iUnion.mpr ⟨⟨d, hdi, had⟩, h⟩)))
  let next (i : W1) (previous : ∀ j, j < i → Block) : Block := (step i previous).choose
  let branch : W1 → Block := WellFoundedLT.fix next
  have hbranch (i : W1) : (step i (fun j _ => branch j)).choose = branch i := by
    change next i (fun j _ => WellFoundedLT.fix next j) = WellFoundedLT.fix next i
    rw [WellFoundedLT.fix_eq]
  have hcross (i j : W1) (hij : i < j) : ∀ x ∈ (branch i).val.val,
      ∀ y ∈ (branch j).val.val, x < y ∧ G.Adj x y := by
    have h := (step j (fun k _ => branch k)).choose_spec.1 i hij
    rwa [hbranch] at h
  have hfilter (i : W1) (c : Local r a) (hci : index c < i)
      (hac : a ∈ eval G H c.val) : (branch i).val.val ⊆ eval G H c.val := by
    have h := (step i (fun k _ => branch k)).choose_spec.2 c hci hac
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
  let points (z : Square) : W2 := (maps (ofLex z).1 (ofLex z).2).val
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
  refine ⟨points, hstrict, ?_, hclique.subset hrange, ?_, ?_⟩
  · rintro x ⟨p, rfl⟩
    exact (branch (ofLex p).1).property.2.1 (maps _ _).property
  · intro p
    exact (branch (ofLex p).1).property.2.2.2.2 _ (maps _ _).property
  · intro c hc hac
    refine ⟨index ⟨c, hc⟩, ?_⟩
    intro z hz
    exact hfilter (ofLex z).1 ⟨c, hc⟩ hz hac (maps _ _).property

/-- A trace bounded strictly below a point of the core has strictly
smaller order type than the core. -/
theorem typeLT_trace_lt_of_bounded {core x : Set W2} {y : W2} (hy : y ∈ core)
    (hbound : ∀ z ∈ core ∩ x, z < y) :
    typeLT (core ∩ x : Set W2) < typeLT core := by
  let top : core := ⟨y, hy⟩
  let f (z : (core ∩ x : Set W2)) : Set.Iio top :=
    ⟨⟨z.val, z.property.1⟩, hbound z.val z.property⟩
  have hf : StrictMono f := by intro p q hpq; exact hpq
  have he := (RelEmbedding.ofMonotone f hf).ordinal_type_le
  exact he.trans_lt (by
    rw [Ordinal.type_Iio_lt]
    exact Ordinal.typein_lt_type (· < ·) top)

def SquareTraceSmall (core x : Set W2) : Prop :=
  typeLT (core ∩ x : Set W2) < (ω_ 1) ^ (2 : Ordinal.{0})

theorem small_trace_of_convergent_square (ha : GoodCut r σ G H a)
    (f : Square → W2) (hf : StrictMono f)
    (hconv : ∀ c : Code, r c < a → a ∈ eval G H c →
      ∃ i : W1, ∀ z : Square, i < (ofLex z).1 → f z ∈ eval G H c)
    {x : Set W2} (hx : Small r G H a x) : SquareTraceSmall (Set.range f) x := by
  obtain ⟨c, hc, hac, hxc⟩ := hx
  obtain ⟨i, hi⟩ := hconv (SmallUnionCode.compl c) (ha.compl_lt c hc) hac
  let top : Square := toLex (tail i i, i)
  have hbound : ∀ y ∈ Set.range f ∩ x, y < f top := by
    rintro y ⟨⟨z, rfl⟩, hzx⟩
    have hrow : (ofLex z).1 ≤ i :=
      le_of_not_gt (fun hiz => (hi z hiz) (hxc hzx))
    apply hf
    exact Prod.Lex.left _ _ (hrow.trans_lt (lt_tail i i))
  have htype : typeLT (Set.range f) = (ω_ 1) ^ (2 : Ordinal.{0}) := by
    rw [Ordinal.typeLT_range_of_strictMono f hf, typeLT_square]
  exact (typeLT_trace_lt_of_bounded (core := Set.range f) (x := x)
    (y := f top) ⟨top, rfl⟩ hbound).trans_eq htype

/-- These are the data required to put the ordinal-small trace ideal on
the square, rather than the countable trace ideal on a single row. -/
theorem exists_cofinal_square_with_small_traces (ha : GoodCut r σ G H a)
    (source : Set W2) (hlocal : LocalRedBlock r σ G H source a) :
    ∃ core : Set W2, core ⊆ source ∩ Set.Iio a ∧ G.IsClique core ∧
      typeLT core = (ω_ 1) ^ (2 : Ordinal.{0}) ∧ IsLUB core a ∧
      ∀ x : Set W2, Small r G H a x → SquareTraceSmall core x := by
  obtain ⟨f, hf, hfs, hfc, hfa, hconv⟩ := exists_convergent_square_map ha source hlocal
  have htype : typeLT (Set.range f) = (ω_ 1) ^ (2 : Ordinal.{0}) := by
    rw [Ordinal.typeLT_range_of_strictMono f hf, typeLT_square]
  have htraces := fun x hx => small_trace_of_convergent_square ha f hf hconv (x := x) hx
  refine ⟨Set.range f, ?_, hfc, htype, ?_, htraces⟩
  · rintro y ⟨z, rfl⟩
    exact ⟨hfs ⟨z, rfl⟩, (hfa z).1⟩
  · refine ⟨?_, ?_⟩
    · rintro y ⟨z, rfl⟩
      exact (hfa z).1.le
    · intro upper hupper
      by_contra h
      have hua : upper < a := lt_of_not_ge h
      have ht := htraces (Set.Iic upper) (bounded_interval_small ha hua)
      change typeLT (Set.range f ∩ Set.Iic upper : Set W2) < _ at ht
      have hrange : Set.range f ∩ Set.Iic upper = Set.range f := Set.inter_eq_left.mpr hupper
      rw [hrange, htype] at ht
      exact ht.false

end Erdos1172Part3ConvergentSquareCore
