/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3IteratedHechlerOrder

@[expose] public section

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3IteratedHechlerClosure

open ErdosRadoCHAsym (W1)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed DenseBelow)
open Erdos1172Part3FunctionDecisions
open Erdos1172Part3NiceFunctionNames
open Erdos1172Part3IteratedHechlerOrder

variable {P : Type} [Preorder P]

/-- Forget the earlier stage and the named side conditions. This map is
used only to reuse the already checked countable stem-union construction. -/
def forget (p : Condition P) : Erdos1172Part3HechlerOrder.Condition where
  stem := p.stem
  stem_countable := p.stem_countable
  side := ∅
  side_countable := Set.countable_empty

theorem forget_mono : Monotone (forget (P := P)) := by
  intro p q hpq
  exact ⟨hpq.2.1, Set.Subset.rfl, fun _ _ _ _ _ h => h.elim⟩

/-- Countable closure is inherited from the earlier order. The earlier
condition bounds every old side-name decision, including at coordinates
introduced at any later point of the countable chain. -/
theorem countablyClosed (hclosed : CountablyClosed P) : CountablyClosed (Condition P) := by
  intro C hne hcount hchain
  let baseMap : Condition P →o P := ⟨Condition.base, fun _ _ h => base_le h⟩
  obtain ⟨lower, hlower⟩ := hclosed (Condition.base '' C) (hne.image Condition.base)
    (hcount.image Condition.base) (hchain.image baseMap)
  let stemMap : Condition P →o Erdos1172Part3HechlerOrder.Condition := ⟨forget, forget_mono⟩
  have hstemChain : IsChain (· ≤ ·) (forget '' C) := hchain.image stemMap
  let stems := Erdos1172Part3HechlerOrder.unionCondition (forget '' C) (hcount.image forget)
  let q : Condition P :=
    { base := lower
      stem := stems.stem
      stem_countable := stems.stem_countable
      side := ⋃ p ∈ C, p.side
      side_countable := hcount.biUnion (fun p _ => p.side_countable) }
  refine ⟨q, ?_⟩
  intro p hp
  have hlp : lower ≤ p.base := hlower p.base ⟨p, hp, rfl⟩
  have hstemp := Erdos1172Part3HechlerOrder.unionCondition_le
    (hcount.image forget) hstemChain (show forget p ∈ forget '' C from ⟨p, hp, rfl⟩)
  refine ⟨hlp, hstemp.1, ?_, ?_⟩
  · intro F hF
    exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hF⟩⟩
  · intro i hpi v hqv F hFp
    obtain ⟨g, ⟨r, hr, rfl⟩, hrv⟩ := Erdos1172Part3HechlerOrder.unionStem_some hqv
    change r.stem i = some v at hrv
    rcases hchain.total hr hp with hrp | hpr
    · exact boundedAt_mono (hrp.2.2.2 i hpi v hrv F hFp)
        (hlower r.base ⟨r, hr, rfl⟩)
    · have hpv := hpr.2.1 i v hrv
      rw [hpi] at hpv
      cases hpv

noncomputable def setValue (p : Condition P) (q : P) (i v : W1) : Condition P where
  base := q
  stem := Function.update p.stem i (some v)
  stem_countable := by
    classical
    apply (p.stem_countable.insert i).mono
    intro j hj
    by_cases hji : j = i
    · exact Or.inl hji
    · right
      change Function.update p.stem i (some v) j ≠ none at hj
      change p.stem j ≠ none
      simpa only [Function.update_of_ne hji] using hj
  side := p.side
  side_countable := p.side_countable

theorem setValue_le {p : Condition P} {q : P} {i v : W1} (hqp : q ≤ p.base)
    (hi : p.stem i = none) (hv : ∀ F ∈ p.side, BoundedAt F.toDecisions q i v) :
    setValue p q i v ≤ p := by
  classical
  refine ⟨hqp, ?_, Set.Subset.rfl, ?_⟩
  · intro j w hj
    by_cases hji : j = i
    · subst j
      rw [hi] at hj
      cases hj
    · exact (Function.update_of_ne hji _ _).trans hj
  · intro j hj w hnew F hF
    by_cases hji : j = i
    · subst j
      have heq : v = w := Option.some.inj (by
        simpa only [setValue, Function.update_self] using hnew)
      exact heq ▸ hv F hF
    · have hold : p.stem j = some w := by
        simpa only [setValue, Function.update_of_ne hji] using hnew
      rw [hj] at hold
      cases hold

/-- A new coordinate can be chosen by deciding countably many earlier
names, bounding their values, and strengthening the earlier condition. -/
theorem coordinate_dense (hclosed : CountablyClosed P) (i : W1) :
    DenseBelow {p : Condition P | ∃ v, p.stem i = some v} := by
  classical
  intro p
  cases hi : p.stem i with
  | none =>
    obtain ⟨q, hqp, v, hv⟩ := exists_bound_for_countable_family hclosed p.base
      (fun F : p.side => F.val.toDecisions)
      (Cardinal.le_aleph0_iff_set_countable.mpr p.side_countable) i
    exact ⟨setValue p q i v, ⟨v, Function.update_self _ _ _⟩,
      setValue_le hqp hi (fun F hF => hv ⟨F, hF⟩)⟩
  | some v => exact ⟨p, ⟨v, hi⟩, le_rfl⟩

/-- The new coordinate function is itself a total persistent decision
system over the extended order. -/
def coordinateFunction (hclosed : CountablyClosed P) :
    FunctionDecisions (Condition P) W1 W1 where
  decides p i v := p.stem i = some v
  dense := by
    intro p i
    obtain ⟨q, hq, hqp⟩ := coordinate_dense hclosed i p
    exact ⟨q, hqp, hq⟩
  persistent hqp hv := hqp.2.1 _ _ hv
  unique hv hw := Option.some.inj (hv.symm.trans hw)

end Erdos1172Part3IteratedHechlerClosure
