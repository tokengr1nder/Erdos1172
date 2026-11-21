/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3ClosedDenseRequirements
public import Erdos1172.Part3StationaryDecisions

@[expose] public section

/-!
# Extending a clique name from a condition cone

A countably closed cone supplies a ground fallback clique with exact
decision origins. The cone name extends to the whole order by using the
fallback only at conditions incompatible with the cone's starting point.
Below that point all decisions remain the original cone decisions.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3CliqueConeExtension

open ErdosRadoCHAsym (W1)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3StationaryDecisions (Compatible)

variable {P I V : Type} [Preorder P] [LinearOrder I] [LinearOrder V]
variable {G : SimpleGraph V}

theorem exists_clique_map_with_origins (core : CliqueDecisions P I V G)
    (hclosed : CountablyClosed P) (p0 : P) (hI : #I ≤ ℵ_ 1) :
    ∃ f : I → V, StrictMono f ∧ G.IsClique (Set.range f) ∧
      ∀ i : I, ∃ q : P, q ≤ p0 ∧ core.decides q i (f i) := by
  classical
  let D (i : I) : Set P := {p | ∃ v, core.decides p i v}
  obtain ⟨conditions, hanti, hstart, hmeet⟩ :=
    Erdos1172Part3ClosedDenseRequirements.exists_antitone_dense_sequence_of_card hclosed p0 D (by
        intro i p
        obtain ⟨q, hqp, v, hv⟩ := core.dense p i
        exact ⟨q, ⟨v, hv⟩, hqp⟩) hI
  let stage (i : I) : W1 := (hmeet i).choose
  have hdec (i : I) : ∃ v, core.decides (conditions (stage i)) i v := (hmeet i).choose_spec
  let value (i : I) : V := (hdec i).choose
  have hvalue (i : I) : core.decides (conditions (stage i)) i (value i) := (hdec i).choose_spec
  have common (i j : I) : ∃ p, core.decides p i (value i) ∧ core.decides p j (value j) :=
    ⟨conditions (max (stage i) (stage j)),
      core.persistent (hanti (le_max_left _ _)) (hvalue i),
      core.persistent (hanti (le_max_right _ _)) (hvalue j)⟩
  refine ⟨value, ?_, ?_, fun i => ⟨conditions (stage i), hstart _, hvalue i⟩⟩
  · intro i j hij
    obtain ⟨p, hi, hj⟩ := common i j
    exact core.ordered hij hi hj
  · rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ hne
    obtain ⟨p, hi, hj⟩ := common i j
    exact core.adjacent (fun heq => hne (congrArg value heq)) hi hj

def extendFromCone (p0 : P) (core : CliqueDecisions (Set.Iic p0) I V G)
    (fallback : I → V) (hstrict : StrictMono fallback)
    (hclique : G.IsClique (Set.range fallback)) : CliqueDecisions P I V G where
  decides p i v := (∃ hp : p ≤ p0, core.decides ⟨p, hp⟩ i v) ∨
    (¬Compatible p p0 ∧ fallback i = v)
  dense := by
    intro p i
    by_cases h : Compatible p p0
    · obtain ⟨q, hqp, hq0⟩ := h
      obtain ⟨s, hsq, v, hv⟩ := core.dense ⟨q, hq0⟩ i
      exact ⟨s.val, (show s.val ≤ q from hsq).trans hqp, v, Or.inl ⟨s.property, hv⟩⟩
    · exact ⟨p, le_rfl, fallback i, Or.inr ⟨h, rfl⟩⟩
  persistent := by
    rintro p q i v hqp (⟨hp, hv⟩ | ⟨hp, hv⟩)
    · exact Or.inl ⟨hqp.trans hp, core.persistent hqp hv⟩
    · exact Or.inr ⟨fun ⟨s, hsq, hs0⟩ => hp ⟨s, hsq.trans hqp, hs0⟩, hv⟩
  unique := by
    rintro p i v w (⟨hp, hv⟩ | ⟨hp, hv⟩) (⟨hq, hw⟩ | ⟨hq, hw⟩)
    · exact core.unique hv hw
    · exact (hq ⟨p, le_rfl, hp⟩).elim
    · exact (hp ⟨p, le_rfl, hq⟩).elim
    · exact hv.symm.trans hw
  ordered := by
    rintro p i j v w hij (⟨hp, hv⟩ | ⟨hp, hv⟩) (⟨hq, hw⟩ | ⟨hq, hw⟩)
    · exact core.ordered hij hv hw
    · exact (hq ⟨p, le_rfl, hp⟩).elim
    · exact (hp ⟨p, le_rfl, hq⟩).elim
    · rw [← hv, ← hw]
      exact hstrict hij
  adjacent := by
    rintro p i j v w hij (⟨hp, hv⟩ | ⟨hp, hv⟩) (⟨hq, hw⟩ | ⟨hq, hw⟩)
    · exact core.adjacent hij hv hw
    · exact (hq ⟨p, le_rfl, hp⟩).elim
    · exact (hp ⟨p, le_rfl, hq⟩).elim
    · rw [← hv, ← hw]
      exact hclique ⟨i, rfl⟩ ⟨j, rfl⟩ (fun h => hij (hstrict.injective h))

theorem extendFromCone_iff_below (p0 : P) (core : CliqueDecisions (Set.Iic p0) I V G)
    (f : I → V) (hf : StrictMono f) (hclique : G.IsClique (Set.range f))
    {p : P} (hp : p ≤ p0) (i : I) (v : V) :
    (extendFromCone p0 core f hf hclique).decides p i v ↔ core.decides ⟨p, hp⟩ i v := by
  constructor
  · rintro (⟨_, hv⟩ | ⟨h, _⟩)
    · exact hv
    · exact (h ⟨p, le_rfl, hp⟩).elim
  · exact fun h => Or.inl ⟨hp, h⟩

theorem exists_global_clique_from_cone (hclosed : CountablyClosed P) (p0 : P)
    (core : CliqueDecisions (Set.Iic p0) I V G) (hI : #I ≤ ℵ_ 1) :
    ∃ out : CliqueDecisions P I V G,
      (∀ p (hp : p ≤ p0) i v, out.decides p i v ↔ core.decides ⟨p, hp⟩ i v) ∧
      (∀ p i v, out.decides p i v → ∃ q : Set.Iic p0, core.decides q i v) := by
  obtain ⟨f, hf, hclique, horigin⟩ := exists_clique_map_with_origins core
    (Erdos1172Part3ClosedDenseRequirements.countablyClosed_Iic hclosed p0) ⟨p0, le_rfl⟩ hI
  refine ⟨extendFromCone p0 core f hf hclique,
    fun p hp i v => extendFromCone_iff_below p0 core f hf hclique hp i v, ?_⟩
  rintro p i v (⟨hp, hv⟩ | ⟨_, hv⟩)
  · exact ⟨⟨p, hp⟩, hv⟩
  · obtain ⟨q, _, hq⟩ := horigin i
    exact ⟨q, hv ▸ hq⟩

end Erdos1172Part3CliqueConeExtension
