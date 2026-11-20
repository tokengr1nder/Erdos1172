/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

/-!
# Infinite Ramsey's theorem for graphs

This file proves the countably infinite case of Ramsey's theorem in a form that is useful for
ordinal partition relations.  Every graph on an infinite type has either an infinite clique or
an infinite clique in its complement.

The proof is the usual reservoir construction.  At each stage, choose one vertex from an
infinite reservoir and retain an infinite set of vertices which are either all adjacent or all
nonadjacent to it.  An infinite subsequence of stages makes the same choice, and its selected
vertices form the required homogeneous set.
-/

open Set

namespace SimpleGraph

universe u

variable {V : Type u}

private structure RamseyState (G : SimpleGraph V) where
  vertex : V
  color : Bool
  reservoir : Set V
  infinite_reservoir : reservoir.Infinite
  avoids_vertex : vertex ∉ reservoir
  uniform : ∀ ⦃y⦄, y ∈ reservoir → (G.Adj vertex y ↔ color = true)

private theorem exists_ramseyState_of_infinite (G : SimpleGraph V) (S : Set V)
    (hS : S.Infinite) :
    ∃ q : RamseyState G, q.vertex ∈ S ∧ q.reservoir ⊆ S := by
  classical
  obtain ⟨x, hx⟩ := hS.nonempty
  let S' : Set V := S \ {x}
  let A : Set V := {y ∈ S' | G.Adj x y}
  let B : Set V := {y ∈ S' | ¬G.Adj x y}
  have hS' : S'.Infinite := hS.sdiff (Set.finite_singleton x)
  have hAB : A ∪ B = S' := by
    ext y
    by_cases hxy : G.Adj x y <;> simp [A, B, hxy]
  have hABinf : (A ∪ B).Infinite := hAB.symm ▸ hS'
  rcases Set.infinite_union.mp hABinf with hA | hB
  · refine ⟨{
      vertex := x
      color := true
      reservoir := A
      infinite_reservoir := hA
      avoids_vertex := ?_
      uniform := ?_ }, hx, ?_⟩
    · simp [A, S']
    · intro y hy
      exact ⟨fun _ ↦ rfl, fun _ ↦ hy.2⟩
    · intro y hy
      exact hy.1.1
  · refine ⟨{
      vertex := x
      color := false
      reservoir := B
      infinite_reservoir := hB
      avoids_vertex := ?_
      uniform := ?_ }, hx, ?_⟩
    · simp [B, S']
    · intro y hy
      exact ⟨fun hxy ↦ (hy.2 hxy).elim, fun h ↦ (Bool.false_ne_true h).elim⟩
    · intro y hy
      exact hy.1.1

private noncomputable def chooseRamseyState (G : SimpleGraph V) (S : Set V)
    (hS : S.Infinite) : RamseyState G :=
  Classical.choose (exists_ramseyState_of_infinite G S hS)

private theorem chooseRamseyState_vertex_mem (G : SimpleGraph V) (S : Set V)
    (hS : S.Infinite) : (chooseRamseyState G S hS).vertex ∈ S :=
  (Classical.choose_spec (exists_ramseyState_of_infinite G S hS)).1

private theorem chooseRamseyState_reservoir_subset (G : SimpleGraph V) (S : Set V)
    (hS : S.Infinite) : (chooseRamseyState G S hS).reservoir ⊆ S :=
  (Classical.choose_spec (exists_ramseyState_of_infinite G S hS)).2

private noncomputable def ramseyStateSeq (G : SimpleGraph V) [Infinite V] :
    ℕ → RamseyState G
  | 0 => chooseRamseyState G Set.univ Set.infinite_univ
  | n + 1 =>
      chooseRamseyState G (ramseyStateSeq G n).reservoir
        (ramseyStateSeq G n).infinite_reservoir

private theorem ramseyStateSeq_succ_vertex_mem (G : SimpleGraph V) [Infinite V] (n : ℕ) :
    (ramseyStateSeq G (n + 1)).vertex ∈ (ramseyStateSeq G n).reservoir := by
  exact chooseRamseyState_vertex_mem G _ _

private theorem ramseyStateSeq_succ_reservoir_subset (G : SimpleGraph V) [Infinite V] (n : ℕ) :
    (ramseyStateSeq G (n + 1)).reservoir ⊆ (ramseyStateSeq G n).reservoir := by
  exact chooseRamseyState_reservoir_subset G _ _

private theorem ramseyStateSeq_reservoir_antitone (G : SimpleGraph V) [Infinite V]
    {i j : ℕ} (hij : i ≤ j) :
    (ramseyStateSeq G j).reservoir ⊆ (ramseyStateSeq G i).reservoir := by
  induction j, hij using Nat.le_induction with
  | base => exact Subset.rfl
  | succ j _ ih =>
      exact (ramseyStateSeq_succ_reservoir_subset G j).trans ih

private theorem ramseyStateSeq_later_vertex_mem (G : SimpleGraph V) [Infinite V]
    {i j : ℕ} (hij : i < j) :
    (ramseyStateSeq G j).vertex ∈ (ramseyStateSeq G i).reservoir := by
  cases j with
  | zero => omega
  | succ j =>
      exact ramseyStateSeq_reservoir_antitone G (Nat.lt_succ_iff.mp hij)
        (ramseyStateSeq_succ_vertex_mem G j)

private theorem ramseyStateSeq_vertex_injective (G : SimpleGraph V) [Infinite V] :
    Function.Injective (fun n ↦ (ramseyStateSeq G n).vertex) := by
  intro i j hv
  change (ramseyStateSeq G i).vertex = (ramseyStateSeq G j).vertex at hv
  by_contra hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hmem := ramseyStateSeq_later_vertex_mem G hij
    rw [← hv] at hmem
    exact (ramseyStateSeq G i).avoids_vertex hmem
  · have hmem := ramseyStateSeq_later_vertex_mem G hji
    rw [hv] at hmem
    exact (ramseyStateSeq G j).avoids_vertex hmem

private theorem ramseyStateSeq_adj_iff_color_of_lt (G : SimpleGraph V) [Infinite V]
    {i j : ℕ} (hij : i < j) :
    G.Adj (ramseyStateSeq G i).vertex (ramseyStateSeq G j).vertex ↔
      (ramseyStateSeq G i).color = true :=
  (ramseyStateSeq G i).uniform (ramseyStateSeq_later_vertex_mem G hij)

/-- **Infinite Ramsey theorem for graphs.** A graph on an infinite type has an infinite clique,
or its complement has an infinite clique. -/
theorem exists_infinite_clique_or_compl [Infinite V] (G : SimpleGraph V) :
    (∃ s : Set V, s.Infinite ∧ G.IsClique s) ∨
      ∃ s : Set V, s.Infinite ∧ Gᶜ.IsClique s := by
  classical
  let vertices : ℕ → V := fun n ↦ (ramseyStateSeq G n).vertex
  let redStages : Set ℕ := {n | (ramseyStateSeq G n).color = true}
  let blueStages : Set ℕ := {n | (ramseyStateSeq G n).color = false}
  have hcover : redStages ∪ blueStages = Set.univ := by
    ext n
    cases (ramseyStateSeq G n).color <;> simp [redStages, blueStages]
  have hstage : redStages.Infinite ∨ blueStages.Infinite := by
    rw [← Set.infinite_union, hcover]
    exact Set.infinite_univ
  rcases hstage with hred | hblue
  · refine Or.inl ⟨vertices '' redStages,
      hred.image (ramseyStateSeq_vertex_injective G).injOn, ?_⟩
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ hv
    have hij : i ≠ j := fun h ↦ hv (congrArg vertices h)
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact (ramseyStateSeq_adj_iff_color_of_lt G hij).2 hi
    · rw [G.adj_comm]
      exact (ramseyStateSeq_adj_iff_color_of_lt G hji).2 hj
  · refine Or.inr ⟨vertices '' blueStages,
      hblue.image (ramseyStateSeq_vertex_injective G).injOn, ?_⟩
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ hv
    rw [G.compl_adj]
    refine ⟨hv, ?_⟩
    have hij : i ≠ j := fun h ↦ hv (congrArg vertices h)
    rcases lt_or_gt_of_ne hij with hij | hji
    · intro hadj
      have htrue := (ramseyStateSeq_adj_iff_color_of_lt G hij).1 hadj
      rw [hi] at htrue
      exact Bool.false_ne_true htrue
    · intro hadj
      have hadj' : G.Adj (ramseyStateSeq G j).vertex (ramseyStateSeq G i).vertex :=
        (G.adj_comm _ _).mp hadj
      have htrue := (ramseyStateSeq_adj_iff_color_of_lt G hji).1 hadj'
      rw [hj] at htrue
      exact Bool.false_ne_true htrue

end SimpleGraph
