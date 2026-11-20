/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Order.Hom.Lex
public import Erdos1172.ForMathlib.SetTheory.Ordinal.PartitionRelationAPI

@[expose] public section

open Ordinal Set

universe u

namespace Ordinal

/-- Adjoining a point strictly above every member of a well-ordered set adds
one point on the right of its ordinal order type. -/
theorem typeLT_insert_of_forall_lt
    {V : Type u} [LinearOrder V] [WellFoundedLT V]
    {s : Set V} {x : V} (hx : ∀ y ∈ s, y < x) :
    typeLT (Set.insert x s : Set V) = typeLT s + 1 := by
  classical
  have hxnot : x ∉ s := by
    intro hxs
    exact (lt_irrefl x) (hx x hxs)
  have hwf_lex : WellFounded (fun a b : s ⊕ₗ PUnit.{u + 1} => a < b) := by
    refine Subrelation.wf (r := InvImage (Sum.Lex (· < ·) (· < ·)) ofLex) (fun h => h) ?_
    exact InvImage.wf ofLex (Sum.lex_wf wellFounded_lt wellFounded_lt)
  letI : WellFoundedLT (s ⊕ₗ PUnit.{u + 1}) := hwf_lex
  let e : (s ⊕ₗ PUnit.{u + 1}) ≃o (Set.insert x s : Set V) :=
    { toEquiv := ofLex.trans (Equiv.Set.insert hxnot).symm
      map_rel_iff' := by
        intro a b
        induction a using Lex.rec with
        | _ a =>
          induction b using Lex.rec with
          | _ b =>
            cases a with
            | inl a =>
              cases b with
              | inl b =>
                change (a : V) ≤ b ↔
                  (Sum.inlₗ a : s ⊕ₗ PUnit.{u + 1}) ≤ Sum.inlₗ b
                exact (Sum.Lex.inl_le_inl_iff
                  (α := s) (β := PUnit.{u + 1})).symm
              | inr b =>
                change (a : V) ≤ x ↔
                  (Sum.inlₗ a : s ⊕ₗ PUnit.{u + 1}) ≤ Sum.inrₗ b
                exact iff_of_true (hx a a.property).le (Sum.Lex.inl_le_inr a b)
            | inr a =>
              cases b with
              | inl b =>
                change x ≤ (b : V) ↔
                  (Sum.inrₗ a : s ⊕ₗ PUnit.{u + 1}) ≤ Sum.inlₗ b
                exact iff_of_false (not_le_of_gt (hx b b.property))
                  Sum.Lex.not_inr_le_inl
              | inr b =>
                change x ≤ x ↔
                  (Sum.inrₗ a : s ⊕ₗ PUnit.{u + 1}) ≤ Sum.inrₗ b
                exact iff_of_true le_rfl le_rfl }
  have he := e.ordinalType_congr
  have hpunit : typeLT PUnit.{u + 1} = 1 :=
    type_eq_one_of_unique _
  have hsum : typeLT (s ⊕ₗ PUnit.{u + 1}) =
      typeLT s + typeLT PUnit.{u + 1} :=
    type_sum_lex (· < ·) (· < ·)
  calc
    typeLT (Set.insert x s : Set V) = typeLT (s ⊕ₗ PUnit.{u + 1}) := he.symm
    _ = typeLT s + typeLT PUnit.{u + 1} := hsum
    _ = typeLT s + 1 := by rw [hpunit]

end Ordinal

namespace SimpleGraph

/-- Extend a clique of type `β` by one point when a common neighbor lies
strictly above every point of the clique. -/
theorem exists_clique_type_add_one_of_common_later
    {V : Type u} [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) {s : Set V} {β : Ordinal.{u}}
    (hs : G.IsClique s) (htype : typeLT s = β)
    {x : V} (hlater : ∀ y ∈ s, y < x)
    (hadj : ∀ y ∈ s, G.Adj y x) :
    ∃ t : Set V, G.IsClique t ∧ typeLT t = β + 1 := by
  refine ⟨insert x s, ?_, ?_⟩
  · apply hs.insert
    intro y hy _
    rw [G.adj_comm]
    exact hadj y hy
  · change typeLT (Set.insert x s : Set V) = β + 1
    rw [Ordinal.typeLT_insert_of_forall_lt hlater, htype]

/-- Reservoir formulation of one-point clique extension: it suffices that the
set of common later neighbors is nonempty. -/
theorem exists_clique_type_add_one_of_common_later_reservoir
    {V : Type u} [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) {s : Set V} {β : Ordinal.{u}}
    (hs : G.IsClique s) (htype : typeLT s = β)
    (hreservoir : Set.Nonempty
      {x : V | (∀ y ∈ s, y < x) ∧ ∀ y ∈ s, G.Adj y x}) :
    ∃ t : Set V, G.IsClique t ∧ typeLT t = β + 1 := by
  obtain ⟨x, hlater, hadj⟩ := hreservoir
  exact G.exists_clique_type_add_one_of_common_later hs htype hlater hadj

end SimpleGraph
