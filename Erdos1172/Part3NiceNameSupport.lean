/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CompleteRestriction

@[expose] public section

/-!
# Bounded support of small nice names

A nice name on at most omegaOne inputs uses at most omegaOne deciding
conditions. If every condition has countable coordinate support in
omegaTwo, the union of all these supports has a strict bound in omegaTwo.

The localization corollary retains its actual restriction maps and the
assertion that bounded-support conditions belong to the inclusion range.
Neither property is inferred merely from a cardinality bound.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3NiceNameSupport

open ErdosRadoCHAsym (W2)
open Erdos1172Part3NiceFunctionNames (NiceFunctionName)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3CompleteRestriction (CompleteRestriction Supported restrictClique)

variable {P I V : Type} [Preorder P]

def decidingConditions (N : NiceFunctionName P I V) : Set P :=
  ⋃ i : I, Prod.fst '' N.graph i

theorem decidingConditions_card_le (N : NiceFunctionName P I V) (hI : #I ≤ ℵ_ 1) :
    #(decidingConditions N) ≤ ℵ_ 1 := by
  calc
    #(decidingConditions N) ≤ Cardinal.sum (fun i : I => #(Prod.fst '' N.graph i)) :=
      Cardinal.mk_iUnion_le_sum_mk
    _ ≤ Cardinal.sum (fun _ : I => ℵ_ 1) :=
      Cardinal.sum_le_sum _ _ (fun i => Cardinal.mk_image_le.trans (N.small i))
    _ = #I * ℵ_ 1 := Cardinal.sum_const' _ _
    _ ≤ ℵ_ 1 * ℵ_ 1 := mul_le_mul' hI le_rfl
    _ = ℵ_ 1 := Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1)

def nameSupport (conditionSupport : P → Set W2) (N : NiceFunctionName P I V) : Set W2 :=
  ⋃ p : decidingConditions N, conditionSupport p.val

theorem nameSupport_card_le (conditionSupport : P → Set W2)
    (hsmall : ∀ p, (conditionSupport p).Countable)
    (N : NiceFunctionName P I V) (hI : #I ≤ ℵ_ 1) :
    #(nameSupport conditionSupport N) ≤ ℵ_ 1 := by
  calc
    #(nameSupport conditionSupport N)
        ≤ Cardinal.sum (fun p : decidingConditions N => #(conditionSupport p.val)) :=
      Cardinal.mk_iUnion_le_sum_mk
    _ ≤ Cardinal.sum (fun _ : decidingConditions N => ℵ_ 1) :=
      Cardinal.sum_le_sum _ _ (fun p =>
        (Cardinal.le_aleph0_iff_set_countable.mpr (hsmall p.val)).trans (Cardinal.aleph0_le_aleph 1))
    _ = #(decidingConditions N) * ℵ_ 1 := Cardinal.sum_const' _ _
    _ ≤ ℵ_ 1 * ℵ_ 1 := mul_le_mul' (decidingConditions_card_le N hI) le_rfl
    _ = ℵ_ 1 := Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1)

theorem support_mem_of_graph (conditionSupport : P → Set W2)
    (N : NiceFunctionName P I V) {i : I} {p : P} {v : V}
    (hp : (p, v) ∈ N.graph i) {a : W2} (ha : a ∈ conditionSupport p) :
    a ∈ nameSupport conditionSupport N := by
  have hdec : p ∈ decidingConditions N := Set.mem_iUnion.mpr ⟨i, (p, v), hp, rfl⟩
  exact Set.mem_iUnion.mpr ⟨⟨p, hdec⟩, ha⟩

theorem exists_support_bound (conditionSupport : P → Set W2)
    (hsmall : ∀ p, (conditionSupport p).Countable)
    (N : NiceFunctionName P I V) (hI : #I ≤ ℵ_ 1) :
    ∃ bound : W2, ∀ i p v, (p, v) ∈ N.graph i →
      ∀ a ∈ conditionSupport p, a < bound := by
  obtain ⟨bound, hb⟩ := Erdos1172Part3CoreObjectCode.exists_objectBound
    ⟨nameSupport conditionSupport N, nameSupport_card_le conditionSupport hsmall N hI⟩
  exact ⟨bound, fun i p v hp a ha => hb a (support_mem_of_graph conditionSupport N hp ha)⟩

variable [LinearOrder I] [LinearOrder V] {G : SimpleGraph V}

theorem exists_supported_restriction
    (conditionSupport : P → Set W2) (hsmall : ∀ p, (conditionSupport p).Countable)
    (Stage : W2 → Type) [∀ a, Preorder (Stage a)]
    (restriction : ∀ a, CompleteRestriction P (Stage a))
    (hlocal : ∀ a p, (∀ b ∈ conditionSupport p, b < a) →
      p ∈ Set.range (restriction a).embed)
    (N : NiceCliqueName P I V G) (hI : #I ≤ ℵ_ 1) :
    ∃ bound : W2, ∀ a : W2, bound ≤ a →
      ∃ M : NiceCliqueName (Stage a) I V G,
        ∀ p i x, M.toClique.decides ((restriction a).restrict p) i x ↔
          N.toClique.decides p i x := by
  obtain ⟨bound, hb⟩ := exists_support_bound conditionSupport hsmall N.function hI
  refine ⟨bound, ?_⟩
  intro a hba
  have hs : Supported (restriction a) N.function := by
    intro i p v hp
    exact hlocal a p (fun b hbp => (hb i p v hp b hbp).trans_le hba)
  exact ⟨restrictClique (restriction a) N hs,
    Erdos1172Part3CompleteRestriction.restrictClique_decides_iff (restriction a) N hs⟩

theorem exists_club_supported_names
    (conditionSupport : P → Set W2) (hsmall : ∀ p, (conditionSupport p).Countable)
    (Stage : W2 → Type) [∀ a, Preorder (Stage a)]
    (restriction : ∀ a, CompleteRestriction P (Stage a))
    (hlocal : ∀ a p, (∀ b ∈ conditionSupport p, b < a) →
      p ∈ Set.range (restriction a).embed)
    (hI : #I ≤ ℵ_ 1) (rank : NiceCliqueName P I V G ↪ W2) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club,
      ∀ N : NiceCliqueName P I V G, rank N < a → Supported (restriction a) N.function := by
  classical
  choose bound hb using fun N : NiceCliqueName P I V G =>
    exists_support_bound conditionSupport hsmall N.function hI
  refine ⟨{a | ∀ N, rank N < a → bound N < a},
    ClubClosure.isClub_rankClosed rank bound
      Erdos1172Part3NeighborhoodCode.alephZero_lt_cof_W2, ?_⟩
  intro a ha N hN i p v hp
  exact hlocal a p (fun b hbp => (hb N i p v hp b hbp).trans (ha N hN))

end Erdos1172Part3NiceNameSupport
