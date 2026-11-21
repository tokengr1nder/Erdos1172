/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedCofinality

@[expose] public section

/-!
# Ground cofinal realizations of small ordered decision names

A descending omegaOne sequence schedules both the small decision domain
and all cuts of the small ambient order. At a cut's stage it stores one
cofinal decision. Its index need not equal the index scheduled at that
stage: uniqueness at a common later stage identifies the stored value
with the eventual chosen value of that index.

Thus the ground realization remains cofinal as well as strictly ordered.
Countable closure is used only at proper countable stages; there is no
condition below the completed omegaOne sequence.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedCofinalRealization

open ErdosRadoCHAsym (W1)
open Erdos1172Part3ClosedDecisionSystem
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3NamedCofinality (OrderedDecisions CofinalDecisions)

variable {P I V : Type} [Preorder P] [LinearOrder I] [LinearOrder V]

/-- Realize an ordered cofinal decision system by one ground cofinal
strictly increasing function when both its index and target are small. -/
theorem exists_ground_cofinal_embedding
    (E : FunctionDecisions P I V) (hclosed : CountablyClosed P) (p0 : P)
    (hI : #I ≤ ℵ_ 1) (hV : #V ≤ ℵ_ 1)
    (hordered : OrderedDecisions E) (hcofinal : CofinalDecisions E) :
    ∃ e : I → V, StrictMono e ∧ IsCofinal (Set.range e) := by
  classical
  obtain ⟨indexI⟩ : Nonempty (I ↪ W1) := (Cardinal.le_def _ _).mp (by
    simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using hI)
  obtain ⟨indexV⟩ : Nonempty (V ↪ W1) := (Cardinal.le_def _ _).mp (by
    simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using hV)
  let D (j : W1) : Set P := {p |
    (∀ i : I, indexI i = j → ∃ x : V, E.decides p i x) ∧
    (∀ cut : V, indexV cut = j → ∃ i : I, ∃ x : V, E.decides p i x ∧ cut ≤ x)}
  have hD : ∀ j : W1, DenseBelow (D j) := by
    intro j p
    obtain ⟨q, hqp, hvalues⟩ : ∃ q : P, q ≤ p ∧
        ∀ i : I, indexI i = j → ∃ x : V, E.decides q i x := by
      by_cases hrequest : ∃ i : I, indexI i = j
      · obtain ⟨q, hqp, x, hx⟩ := E.dense p hrequest.choose
        refine ⟨q, hqp, ?_⟩
        intro i hi
        have heq : i = hrequest.choose := indexI.injective (hi.trans hrequest.choose_spec.symm)
        subst i
        exact ⟨x, hx⟩
      · exact ⟨p, le_rfl, fun i hi => (hrequest ⟨i, hi⟩).elim⟩
    by_cases hcut : ∃ cut : V, indexV cut = j
    · obtain ⟨r, hrq, i, x, hx, hcutx⟩ := hcofinal q hcut.choose
      refine ⟨r, ⟨?_, ?_⟩, hrq.trans hqp⟩
      · intro k hk
        obtain ⟨y, hy⟩ := hvalues k hk
        exact ⟨y, E.persistent hrq hy⟩
      · intro cut hcutj
        have heq : cut = hcut.choose := indexV.injective (hcutj.trans hcut.choose_spec.symm)
        subst cut
        exact ⟨i, x, hx, hcutx⟩
    · exact ⟨q, ⟨hvalues, fun cut hcutj => (hcut ⟨cut, hcutj⟩).elim⟩, hqp⟩
  obtain ⟨conditions, hanti, -, hmeet⟩ := exists_antitone_dense_sequence hclosed p0 D hD
  have hvalues (i : I) : ∃ x : V, E.decides (conditions (indexI i)) i x :=
    (hmeet (indexI i)).1 i rfl
  let e (i : I) : V := (hvalues i).choose
  have he (i : I) : E.decides (conditions (indexI i)) i (e i) := (hvalues i).choose_spec
  refine ⟨e, ?_, ?_⟩
  · intro i j hij
    exact hordered hij
      (E.persistent (hanti (le_max_left (indexI i) (indexI j))) (he i))
      (E.persistent (hanti (le_max_right (indexI i) (indexI j))) (he j))
  · intro cut
    obtain ⟨i, x, hx, hcutx⟩ := (hmeet (indexV cut)).2 cut rfl
    have heq : x = e i := E.unique
      (E.persistent (hanti (le_max_left (indexV cut) (indexI i))) hx)
      (E.persistent (hanti (le_max_right (indexV cut) (indexI i))) (he i))
    exact ⟨e i, Set.mem_range_self i, hcutx.trans_eq heq⟩

/-- The realized cofinal range has exactly the original domain's order
type. In particular a cofinal named finite power supplies a ground seed. -/
theorem exists_ground_cofinal_set [WellFoundedLT I] [WellFoundedLT V]
    (E : FunctionDecisions P I V) (hclosed : CountablyClosed P) (p0 : P)
    (hI : #I ≤ ℵ_ 1) (hV : #V ≤ ℵ_ 1)
    (hordered : OrderedDecisions E) (hcofinal : CofinalDecisions E) :
    ∃ A : Set V, IsCofinal A ∧ typeLT A = typeLT I := by
  obtain ⟨e, hstrict, hcof⟩ := exists_ground_cofinal_embedding E hclosed p0 hI hV hordered hcofinal
  exact ⟨Set.range e, hcof, Ordinal.typeLT_range_of_strictMono e hstrict⟩

end Erdos1172Part3NamedCofinalRealization
