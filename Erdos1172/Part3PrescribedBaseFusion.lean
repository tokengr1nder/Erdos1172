/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3IteratedHechlerPreservation

@[expose] public section

/-!
# Countable fusion with a prescribed earlier condition

The chosen lower condition has exactly the supplied base. This extra
equality is what permits coherent lower bounds through a countable tower.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3PrescribedBaseFusion

open Erdos1172Part3FunctionDecisions (boundedAt_mono)
open Erdos1172Part3IteratedHechlerOrder
open Erdos1172Part3IteratedHechlerClosure (forget forget_mono)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode pairRank)
open Erdos1172Part3HechlerCentering (stemRank)

variable {P : Type} [Preorder P]

theorem exists_chain_lower_with_base (C : Set (Condition P)) (hC : C.Countable)
    (hchain : IsChain (· ≤ ·) C) (lower : P) (hlower : ∀ p ∈ C, lower ≤ p.base) :
    ∃ q : Condition P, q.base = lower ∧ ∀ p ∈ C, q ≤ p := by
  let stemMap : Condition P →o Erdos1172Part3HechlerOrder.Condition := ⟨forget, forget_mono⟩
  have hstemChain : IsChain (· ≤ ·) (forget '' C) := hchain.image stemMap
  let stems := Erdos1172Part3HechlerOrder.unionCondition (forget '' C) (hC.image forget)
  let q : Condition P :=
    { base := lower
      stem := stems.stem
      stem_countable := stems.stem_countable
      side := ⋃ p ∈ C, p.side
      side_countable := hC.biUnion (fun p _ => p.side_countable) }
  refine ⟨q, rfl, ?_⟩
  intro p hp
  have hstemp := Erdos1172Part3HechlerOrder.unionCondition_le
    (hC.image forget) hstemChain (show forget p ∈ forget '' C from ⟨p, hp, rfl⟩)
  refine ⟨hlower p hp, hstemp.1, ?_, ?_⟩
  · intro F hF
    exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hF⟩⟩
  · intro i hpi v hqv F hFp
    obtain ⟨g, ⟨r, hr, rfl⟩, hrv⟩ := Erdos1172Part3HechlerOrder.unionStem_some hqv
    change r.stem i = some v at hrv
    rcases hchain.total hr hp with hrp | hpr
    · exact boundedAt_mono (hrp.2.2.2 i hpi v hrv F hFp) (hlower r hr)
    · have hpv := hpr.2.1 i v hrv
      rw [hpi] at hpv
      cases hpv

theorem exists_same_stem_lower_with_base (p0 : Condition P) (C : Set (Condition P))
    (hC : C.Countable) (hstem : ∀ p ∈ C, p.stem = p0.stem)
    (lower : P) (hlower : ∀ p ∈ C, lower ≤ p.base) :
    ∃ q : Condition P, q.base = lower ∧ ∀ p ∈ C, q ≤ p := by
  let q : Condition P :=
    { base := lower
      stem := p0.stem
      stem_countable := p0.stem_countable
      side := ⋃ p ∈ C, p.side
      side_countable := hC.biUnion (fun p _ => p.side_countable) }
  refine ⟨q, rfl, ?_⟩
  intro p hp
  refine ⟨hlower p hp, ?_, ?_, ?_⟩
  · intro i v hv
    change p0.stem i = some v
    rwa [hstem p hp] at hv
  · intro F hF
    exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hF⟩⟩
  · intro i hi v hv _ _
    change p0.stem i = some v at hv
    rw [hstem p hp] at hi
    rw [hi] at hv
    cases hv

theorem same_stem_of_extend_code_eq (c : CountablyCenteredCode P) (hCH : CH)
    {p q : Condition P} (h : (c.extend hCH).code p = (c.extend hCH).code q) :
    p.stem = q.stem := by
  have hpairs := pairRank.injective h
  exact congrArg Subtype.val ((stemRank hCH).injective (congrArg Prod.snd hpairs))

end Erdos1172Part3PrescribedBaseFusion
