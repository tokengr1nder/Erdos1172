/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.ForMathlib.SetTheory.Ordinal.CliqueExtension

@[expose] public section

open Ordinal Set

universe u

namespace Ordinal

/-- If every point of `s` lies strictly before every point of `t`, then their
union has ordinal order type `typeLT s + typeLT t`. -/
theorem typeLT_union_of_forall_lt
    {V : Type u} [LinearOrder V] [WellFoundedLT V]
    {s t : Set V} (hst : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    typeLT (s ∪ t : Set V) = typeLT s + typeLT t := by
  classical
  have hdisj : Disjoint s t := by
    rw [Set.disjoint_left]
    intro x hxs hxt
    exact (lt_irrefl x) (hst x hxs x hxt)
  have hwf_lex : WellFounded (fun a b : s ⊕ₗ t => a < b) := by
    refine Subrelation.wf (r := InvImage (Sum.Lex (· < ·) (· < ·)) ofLex) (fun h => h) ?_
    exact InvImage.wf ofLex (Sum.lex_wf wellFounded_lt wellFounded_lt)
  letI : WellFoundedLT (s ⊕ₗ t) := hwf_lex
  let e : (s ⊕ₗ t) ≃o (s ∪ t : Set V) :=
    { toEquiv := ofLex.trans (Equiv.Set.union hdisj).symm
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
                change (a : V) ≤ b ↔ (Sum.inlₗ a : s ⊕ₗ t) ≤ Sum.inlₗ b
                exact (Sum.Lex.inl_le_inl_iff (α := s) (β := t)).symm
              | inr b =>
                change (a : V) ≤ b ↔ (Sum.inlₗ a : s ⊕ₗ t) ≤ Sum.inrₗ b
                exact iff_of_true (hst a a.property b b.property).le (Sum.Lex.inl_le_inr a b)
            | inr a =>
              cases b with
              | inl b =>
                change (a : V) ≤ b ↔ (Sum.inrₗ a : s ⊕ₗ t) ≤ Sum.inlₗ b
                exact iff_of_false
                  (not_le_of_gt (hst b b.property a a.property))
                  Sum.Lex.not_inr_le_inl
              | inr b =>
                change (a : V) ≤ b ↔ (Sum.inrₗ a : s ⊕ₗ t) ≤ Sum.inrₗ b
                exact (Sum.Lex.inr_le_inr_iff (α := s) (β := t)).symm }
  have he := e.ordinalType_congr
  have hsum : typeLT (s ⊕ₗ t) = typeLT s + typeLT t := type_sum_lex (· < ·) (· < ·)
  exact he.symm.trans hsum

end Ordinal

namespace SimpleGraph

/-- The union of two cliques is a clique when all cross edges are present. -/
theorem IsClique.union_of_cross
    {V : Type u} (G : SimpleGraph V) {s t : Set V}
    (hs : G.IsClique s) (ht : G.IsClique t)
    (hcross : ∀ x ∈ s, ∀ y ∈ t, G.Adj x y) :
    G.IsClique (s ∪ t) := by
  intro x hx y hy hxy
  rcases hx with hxs | hxt
  · rcases hy with hys | hyt
    · exact hs hxs hys hxy
    · exact hcross x hxs y hyt
  · rcases hy with hys | hyt
    · rw [G.adj_comm]
      exact hcross y hys x hxt
    · exact ht hxt hyt hxy

/-- Extend a clique block of type `β` by a later clique block of type `γ`,
with all cross edges present, to obtain a clique of type `β + γ`. -/
theorem exists_clique_type_add_of_later_block
    {V : Type u} [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) {s t : Set V} {β γ : Ordinal.{u}}
    (hs : G.IsClique s) (ht : G.IsClique t)
    (hstype : typeLT s = β) (httype : typeLT t = γ)
    (hlater : ∀ x ∈ s, ∀ y ∈ t, x < y)
    (hcross : ∀ x ∈ s, ∀ y ∈ t, G.Adj x y) :
    ∃ u : Set V, G.IsClique u ∧ typeLT u = β + γ := by
  refine ⟨s ∪ t, SimpleGraph.IsClique.union_of_cross G hs ht hcross, ?_⟩
  rw [Ordinal.typeLT_union_of_forall_lt hlater, hstype, httype]

end SimpleGraph
