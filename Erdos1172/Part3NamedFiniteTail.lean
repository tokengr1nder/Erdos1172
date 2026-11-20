/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedShortEnumeration
public import Erdos1172.Part3NamedFinalTail
public import Erdos1172.Part3BoundedPrefixCovers

@[expose] public section

/-!
# Finite-power named tails of short cofinal regular sources

The shorter complete enumeration has a fixed finite-power final summand.
An actual embedding of that summand reindexes the decisions. The resulting
regular tail remains cofinal and its complement is bounded after one
decision. This reduces named covering to the still separate task of lifting
the finite-power cover construction at every finite rank.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedFiniteTail

open Erdos1172Part3FiniteTraceSchemes (Index typeLT_index)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName)
open Erdos1172Part3NamedCofinality (OrderedDecisions CofinalDecisions)
open Erdos1172Part3NamedFinalTail
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)

theorem exists_finite_tail_embedding {K : Type} [LinearOrder K] [WellFoundedLT K]
    (ζ : Ordinal.{0}) (n : ℕ)
    (htype : typeLT K = ζ + (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal)) :
    ∃ e : Index n ↪o K, IsCofinal (Set.range e) ∧
      ∀ i : K, i ∉ Set.range e → ∀ j : Index n, i < e j := by
  classical
  have hwf_lex : WellFounded (fun a b : ζ.ToType ⊕ₗ Index n => a < b) := by
    refine Subrelation.wf (r := InvImage (Sum.Lex (· < ·) (· < ·)) ofLex) (fun h => h) ?_
    exact InvImage.wf ofLex (Sum.lex_wf wellFounded_lt wellFounded_lt)
  letI : WellFoundedLT (ζ.ToType ⊕ₗ Index n) := hwf_lex
  have hsum : typeLT (ζ.ToType ⊕ₗ Index n) = typeLT K := by
    calc
      typeLT (ζ.ToType ⊕ₗ Index n) = typeLT ζ.ToType + typeLT (Index n) :=
        Ordinal.type_sum_lex _ _
      _ = _ := by rw [Ordinal.type_toType, typeLT_index, htype]
  obtain ⟨iso⟩ := Ordinal.type_eq.mp hsum
  let e : Index n ↪o K := OrderEmbedding.ofStrictMono
    (fun j => iso (Sum.inrₗ j))
    (fun _ _ h => iso.map_rel_iff.mpr (Sum.Lex.inr_lt_inr_iff.mpr h))
  refine ⟨e, ?_, ?_⟩
  · intro i
    obtain ⟨s, rfl⟩ := iso.surjective i
    induction s using Lex.rec with
    | _ s =>
      cases s with
      | inl a =>
          let j := Erdos1172Part3CofinalFiniteCuts.basePoint n
          exact ⟨e j, Set.mem_range_self j,
            (iso.map_rel_iff.mpr (Sum.Lex.inl_lt_inr a j)).le⟩
      | inr j => exact ⟨e j, Set.mem_range_self j, le_rfl⟩
  · intro i hi j
    obtain ⟨s, rfl⟩ := iso.surjective i
    induction s using Lex.rec with
    | _ s =>
      cases s with
      | inl a => exact iso.map_rel_iff.mpr (Sum.Lex.inl_lt_inr a j)
      | inr a => exact (hi (Set.mem_range_self a)).elim

variable {P I V : Type} [Preorder P] [LinearOrder I] [WellFoundedLT I]
  [LinearOrder V] [WellFoundedLT V]

/-- No full omega-successor embedding implies, on a strengthening, an
actual cofinal finite-power tail name and a bounded discarded prefix.
This theorem constructs the tail; it does not assume a covering name. -/
theorem exists_cofinal_finite_tail (U : RegularName P V) (p0 : P)
    (hclosed : CountablyClosed P) (hI : #I ≤ ℵ_ 1)
    (hItype : typeLT I = (ω_ 1 : Ordinal.{0}) ^ (ω + 1))
    (hVcof : Order.cof V = ℵ_ 1)
    (hcofinal : ∀ p : P, p ≤ p0 → ∀ cut : V,
      ∃ q : P, q ≤ p ∧ ∃ x : V, U.holds q x ∧ cut ≤ x)
    (hno : ¬Erdos1172Part3RegularGreedyEnumeration.HasOrderedEmbeddingBelow (I := I) U p0) :
    ∃ q : P, q ≤ p0 ∧ ∃ n : ℕ,
      ∃ E : FunctionDecisions (Set.Iic q) (Index n) V,
      ∃ T : RegularName (Set.Iic q) V,
        OrderedDecisions E ∧ CofinalDecisions E ∧ DenseCoverage E T ∧
        (∀ p : Set.Iic q, ∀ j x, E.decides p j x → T.holds p x) ∧
        (∀ p : Set.Iic q, ∀ x, T.holds p x → U.holds p.val x) ∧
        ∃ r : Set.Iic q, ∃ cut : V, T.holds r cut ∧
          ∀ s : Set.Iic q, s ≤ r → ∀ x : V, U.holds s.val x → x < cut ∨ T.holds s x := by
  obtain ⟨q, hqp0, i, E, horder, hcof, hmem, hcover, ζ, n, htype⟩ :=
    Erdos1172Part3NamedShortEnumeration.exists_shorter_cofinal_enumeration
      U p0 hclosed hI hItype hVcof hcofinal hno
  obtain ⟨e, hecof, hsep⟩ := exists_finite_tail_embedding ζ n htype
  let source : RegularName (Set.Iic q) V :=
    Erdos1172Part3RegularConeRestriction.onCone q U
  obtain ⟨hord, hcofinalTail, hcoverage, hsub, r, -, cut, hcut, hbound⟩ :=
    exists_cofinal_tail_with_bounded_prefix E source e
      ⟨Erdos1172Part3CofinalFiniteCuts.basePoint n⟩ horder hcover hmem hcof hecof hsep
      ⟨q, le_rfl⟩
  exact ⟨q, hqp0, n, tailE E e, tailU E e, hord, hcofinalTail, hcoverage,
    fun _ _ _ h => tailU_holds_of_decision E e h, hsub, r, cut, hcut, hbound⟩

end Erdos1172Part3NamedFiniteTail
