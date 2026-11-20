/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CliqueConeExtension
public import Erdos1172.Part3RegularMembership

@[expose] public section

/-!
# Extending a clique from an entire regular truth region

Unlike a principal-cone extension, this extension agrees with the input
at every condition where the regular predicate is true. Its construction
depends on the predicate and the clique, not on a chosen starting condition.
The negative region uses a ground fallback with original decision values.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3RegularTruthExtension

open Erdos1172Part3RegularMembership
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3CliqueConeExtension (exists_clique_map_with_origins)

variable {P I V : Type} [Preorder P] [LinearOrder I] [LinearOrder V]
variable {G : SimpleGraph V}

abbrev TruthOrder (U : RegularName P Unit) := {p : P // U.holds p ()}

theorem countablyClosed_truth (hclosed : CountablyClosed P) (U : RegularName P Unit) :
    CountablyClosed (TruthOrder U) := by
  intro s hs hcount hchain
  obtain ⟨p0, hp0⟩ := hs
  have himage : IsChain (· ≤ ·) (Subtype.val '' s) := by
    rintro p ⟨q, hq, rfl⟩ r ⟨t, ht, rfl⟩ hne
    exact hchain hq ht (fun h => hne (congrArg Subtype.val h))
  obtain ⟨p, hp⟩ := hclosed (Subtype.val '' s) ⟨p0.val, p0, hp0, rfl⟩
    (hcount.image Subtype.val) himage
  exact ⟨⟨p, U.persistent (hp p0.val ⟨p0, hp0, rfl⟩) p0.property⟩,
    fun q hq => hp q.val ⟨q, hq, rfl⟩⟩

def extendFromTruth (U : RegularName P Unit) (core : CliqueDecisions (TruthOrder U) I V G)
    (fallback : I → V) (hstrict : StrictMono fallback)
    (hclique : G.IsClique (Set.range fallback)) : CliqueDecisions P I V G where
  decides p i v := (∃ hp : U.holds p (), core.decides ⟨p, hp⟩ i v) ∨
    ((neg U).holds p () ∧ fallback i = v)
  dense := by
    intro p i
    obtain ⟨q, hqp, hq | hq⟩ := exists_deciding_refinement U p ()
    · obtain ⟨s, hsq, v, hv⟩ := core.dense ⟨q, hq⟩ i
      exact ⟨s.val, (show s.val ≤ q from hsq).trans hqp, v, Or.inl ⟨s.property, hv⟩⟩
    · exact ⟨q, hqp, fallback i, Or.inr ⟨hq, rfl⟩⟩
  persistent := by
    rintro p q i v hqp (⟨hp, hv⟩ | ⟨hp, hv⟩)
    · exact Or.inl ⟨U.persistent hqp hp, core.persistent hqp hv⟩
    · exact Or.inr ⟨(neg U).persistent hqp hp, hv⟩
  unique := by
    rintro p i v w (⟨hp, hv⟩ | ⟨hp, hv⟩) (⟨hq, hw⟩ | ⟨hq, hw⟩)
    · exact core.unique hv hw
    · exact (hq p le_rfl hp).elim
    · exact (hp p le_rfl hq).elim
    · exact hv.symm.trans hw
  ordered := by
    rintro p i j v w hij (⟨hp, hv⟩ | ⟨hp, hv⟩) (⟨hq, hw⟩ | ⟨hq, hw⟩)
    · exact core.ordered hij hv hw
    · exact (hq p le_rfl hp).elim
    · exact (hp p le_rfl hq).elim
    · rw [← hv, ← hw]
      exact hstrict hij
  adjacent := by
    rintro p i j v w hij (⟨hp, hv⟩ | ⟨hp, hv⟩) (⟨hq, hw⟩ | ⟨hq, hw⟩)
    · exact core.adjacent hij hv hw
    · exact (hq p le_rfl hp).elim
    · exact (hp p le_rfl hq).elim
    · rw [← hv, ← hw]
      exact hclique ⟨i, rfl⟩ ⟨j, rfl⟩ (fun h => hij (hstrict.injective h))

theorem extendFromTruth_iff (U : RegularName P Unit) (core : CliqueDecisions (TruthOrder U) I V G)
    (f : I → V) (hf : StrictMono f) (hclique : G.IsClique (Set.range f))
    {p : P} (hp : U.holds p ()) (i : I) (v : V) :
    (extendFromTruth U core f hf hclique).decides p i v ↔ core.decides ⟨p, hp⟩ i v := by
  constructor
  · rintro (⟨_, hv⟩ | ⟨h, _⟩)
    · exact hv
    · exact (h p le_rfl hp).elim
  · exact fun h => Or.inl ⟨hp, h⟩

theorem exists_global_clique_from_truth (hclosed : CountablyClosed P) (U : RegularName P Unit)
    (core : CliqueDecisions (TruthOrder U) I V G) (hI : #I ≤ ℵ_ 1)
    (hne : ∃ p, U.holds p ()) :
    ∃ out : CliqueDecisions P I V G,
      (∀ p (hp : U.holds p ()) i v, out.decides p i v ↔ core.decides ⟨p, hp⟩ i v) ∧
      (∀ p i v, out.decides p i v → ∃ q : TruthOrder U, core.decides q i v) := by
  obtain ⟨p0, hp0⟩ := hne
  obtain ⟨f, hf, hclique, horigin⟩ := exists_clique_map_with_origins core
    (countablyClosed_truth hclosed U) ⟨p0, hp0⟩ hI
  refine ⟨extendFromTruth U core f hf hclique,
    fun p hp i v => extendFromTruth_iff U core f hf hclique hp i v, ?_⟩
  rintro p i v (⟨hp, hv⟩ | ⟨_, hv⟩)
  · exact ⟨⟨p, hp⟩, hv⟩
  · obtain ⟨q, _, hq⟩ := horigin i
    exact ⟨q, hv ▸ hq⟩

end Erdos1172Part3RegularTruthExtension
