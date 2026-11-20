/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3SupportedCoverRealization

@[expose] public section

/-!
# Joint realization of point decisions and a supported cover

Point values may vary with the condition. Actual cover membership of each
decided point supplies dense finite certificates. A single omegaOne chain
decides both the point values and every coordinate of the cover function.
The resulting ground points all lie in one ground cover, and any two have
a common decision stage. Order and graph coherence therefore survive.

The hypotheses are explicit decision systems and actual membership, not
a ground embedding or a common final condition. Constructing the required
decision systems for the original Part 3 argument remains separate.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3SupportedCoverEmbedding

open ErdosRadoCHAsym (W1)
open Erdos1172Part3ClosedDecisionSystem
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3SupportedCoverRealization

variable {P I X : Type} [Preorder P]

/-- Simultaneously realize point decisions and their cover certificates.
The common condition in the last clause may depend on the two indices. -/
theorem exists_ground_cover_and_values
    (F : FunctionDecisions P W1 W1) (E : FunctionDecisions P I X)
    (C : (W1 → W1) → Set X) (hclosed : CountablyClosed P)
    (p0 : P) (hI : #I ≤ ℵ_ 1)
    (hmem : ∀ p : P, p ≤ p0 → ∀ i x, E.decides p i x →
      (coverName F C).holds p x) :
    ∃ f : W1 → W1, ∃ e : I → X, Set.range e ⊆ C f ∧
      ∀ i j : I, ∃ p : P, p ≤ p0 ∧
        E.decides p i (e i) ∧ E.decides p j (e j) := by
  classical
  obtain ⟨index⟩ : Nonempty (I ↪ W1) := (Cardinal.le_def _ _).mp (by
    simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using hI)
  let D (j : W1) : Set P := {p |
    (∃ v, F.decides p j v) ∧
      (p ≤ p0 → ∀ i : I, index i = j →
        ∃ x : X, E.decides p i x ∧ Certificate F C p x)}
  have hD : ∀ j, DenseBelow (D j) := by
    intro j p
    obtain ⟨q, hqp, v, hv⟩ := F.dense p j
    by_cases hq0 : q ≤ p0
    · by_cases hrequest : ∃ i : I, index i = j
      · obtain ⟨r, hrq, x, hx⟩ := E.dense q hrequest.choose
        obtain ⟨t, htr, hcert⟩ :=
          hmem r (hrq.trans hq0) hrequest.choose x hx r le_rfl
        refine ⟨t, ⟨⟨v, F.persistent (htr.trans hrq) hv⟩, ?_⟩,
          (htr.trans hrq).trans hqp⟩
        intro _ i hi
        have heq : i = hrequest.choose :=
          index.injective (hi.trans hrequest.choose_spec.symm)
        subst i
        exact ⟨x, E.persistent htr hx, hcert⟩
      · exact ⟨q, ⟨⟨v, hv⟩, fun _ i hi => (hrequest ⟨i, hi⟩).elim⟩, hqp⟩
    · exact ⟨q, ⟨⟨v, hv⟩, fun h => (hq0 h).elim⟩, hqp⟩
  obtain ⟨conditions, hanti, hstart, hmeet⟩ :=
    exists_antitone_dense_sequence hclosed p0 D hD
  have hcoordinates (i : W1) : ∃ v, F.decides (conditions i) i v :=
    (hmeet i).1
  let f (i : W1) : W1 := (hcoordinates i).choose
  have hf (i : W1) : F.decides (conditions i) i (f i) :=
    (hcoordinates i).choose_spec
  have hpoints (i : I) : ∃ x : X,
      E.decides (conditions (index i)) i x ∧
        Certificate F C (conditions (index i)) x :=
    (hmeet (index i)).2 (hstart (index i)) i rfl
  let e (i : I) : X := (hpoints i).choose
  have he (i : I) : E.decides (conditions (index i)) i (e i) :=
    (hpoints i).choose_spec.1
  refine ⟨f, e, ?_, ?_⟩
  · rintro x ⟨i, rfl⟩
    obtain ⟨g, support, hdec, hcover⟩ := (hpoints i).choose_spec.2
    apply hcover f
    intro j hj
    have heq : g j = f j := F.unique
      (F.persistent (hanti (le_max_left (index i) j)) (hdec j hj))
      (F.persistent (hanti (le_max_right (index i) j)) (hf j))
    exact heq.le
  · intro i j
    refine ⟨conditions (max (index i) (index j)), hstart _, ?_, ?_⟩
    · exact E.persistent (hanti (le_max_left _ _)) (he i)
    · exact E.persistent (hanti (le_max_right _ _)) (he j)

variable [LinearOrder I] [LinearOrder X]

/-- Ordered point decisions contained in the cover yield one genuine
ground order embedding into a single ground cover. -/
theorem exists_ground_embedding
    (F : FunctionDecisions P W1 W1) (E : FunctionDecisions P I X)
    (C : (W1 → W1) → Set X) (hclosed : CountablyClosed P)
    (p0 : P) (hI : #I ≤ ℵ_ 1)
    (hmem : ∀ p : P, p ≤ p0 → ∀ i x, E.decides p i x →
      (coverName F C).holds p x)
    (hordered : ∀ p : P, p ≤ p0 → ∀ i j x y,
      i < j → E.decides p i x → E.decides p j y → x < y) :
    ∃ f : W1 → W1, ∃ e : I → X, StrictMono e ∧ Set.range e ⊆ C f := by
  obtain ⟨f, e, hsub, hcommon⟩ :=
    exists_ground_cover_and_values F E C hclosed p0 hI hmem
  refine ⟨f, e, ?_, hsub⟩
  intro i j hij
  obtain ⟨p, hp, hpi, hpj⟩ := hcommon i j
  exact hordered p hp i j (e i) (e j) hij hpi hpj

/-- The existing clique-decision API gives both a ground embedding and
a ground clique inside the same ground cover. -/
theorem exists_ground_clique_map
    (F : FunctionDecisions P W1 W1) {G : SimpleGraph X}
    (sys : CliqueDecisions P I X G) (C : (W1 → W1) → Set X)
    (hclosed : CountablyClosed P) (p0 : P) (hI : #I ≤ ℵ_ 1)
    (hmem : ∀ p : P, p ≤ p0 → ∀ i x, sys.decides p i x →
      (coverName F C).holds p x) :
    ∃ f : W1 → W1, ∃ e : I → X,
      StrictMono e ∧ G.IsClique (Set.range e) ∧ Set.range e ⊆ C f := by
  let E : FunctionDecisions P I X := {
    decides := sys.decides
    dense := sys.dense
    persistent := sys.persistent
    unique := sys.unique }
  obtain ⟨f, e, hsub, hcommon⟩ :=
    exists_ground_cover_and_values F E C hclosed p0 hI hmem
  refine ⟨f, e, ?_, ?_, hsub⟩
  · intro i j hij
    obtain ⟨p, _, hpi, hpj⟩ := hcommon i j
    exact sys.ordered hij hpi hpj
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    obtain ⟨p, _, hpi, hpj⟩ := hcommon i j
    exact sys.adjacent (fun heq => hne (congrArg e heq)) hpi hpj

variable [WellFoundedLT I] [WellFoundedLT X]

/-- A bound on every whole ground cover bounds any small ordered
decision domain whose decided points are actual cover members. -/
theorem typeLT_le_of_embedding_decisions
    (F : FunctionDecisions P W1 W1) (E : FunctionDecisions P I X)
    (C : (W1 → W1) → Set X) (hclosed : CountablyClosed P)
    (p0 : P) (hI : #I ≤ ℵ_ 1)
    (hmem : ∀ p : P, p ≤ p0 → ∀ i x, E.decides p i x →
      (coverName F C).holds p x)
    (hordered : ∀ p : P, p ≤ p0 → ∀ i j x y,
      i < j → E.decides p i x → E.decides p j y → x < y)
    (bound : Ordinal.{0}) (hbound : ∀ f, typeLT (C f) ≤ bound) :
    typeLT I ≤ bound := by
  obtain ⟨f, e, hstrict, hsub⟩ :=
    exists_ground_embedding F E C hclosed p0 hI hmem hordered
  calc
    typeLT I = typeLT (Set.range e) :=
      (Ordinal.typeLT_range_of_strictMono e hstrict).symm
    _ ≤ typeLT (C f) := Ordinal.type_mono hsub
    _ ≤ bound := hbound f

/-- The strict version rules out an ordered decision name at the loss
threshold. It does not rely on a bound only for fixed-condition members. -/
theorem typeLT_lt_of_embedding_decisions
    (F : FunctionDecisions P W1 W1) (E : FunctionDecisions P I X)
    (C : (W1 → W1) → Set X) (hclosed : CountablyClosed P)
    (p0 : P) (hI : #I ≤ ℵ_ 1)
    (hmem : ∀ p : P, p ≤ p0 → ∀ i x, E.decides p i x →
      (coverName F C).holds p x)
    (hordered : ∀ p : P, p ≤ p0 → ∀ i j x y,
      i < j → E.decides p i x → E.decides p j y → x < y)
    (bound : Ordinal.{0}) (hbound : ∀ f, typeLT (C f) < bound) :
    typeLT I < bound := by
  obtain ⟨f, e, hstrict, hsub⟩ :=
    exists_ground_embedding F E C hclosed p0 hI hmem hordered
  calc
    typeLT I = typeLT (Set.range e) :=
      (Ordinal.typeLT_range_of_strictMono e hstrict).symm
    _ ≤ typeLT (C f) := Ordinal.type_mono hsub
    _ < bound := hbound f

end Erdos1172Part3SupportedCoverEmbedding
