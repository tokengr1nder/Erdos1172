/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedShortCover
public import Erdos1172.Part3SupportedCoverUnion
public import Erdos1172.Part3OmegaSuccessorUnion

@[expose] public section

/-!
# Full ordered names in complements of uniformly short supported covers

If a complement had no full ordered embedding, the constructed short-name
cover theorem would cover it on a cone by a second uniformly short
family. Boolean decision density places every ambient point densely in
one of the two actual covers. Joint ground realization then covers the
whole ambient order by two short ground sets, which is impossible.

There is no named-short-cover premise or ground domination hypothesis.
Only the supplied first family's whole-set order-type bound is assumed.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3SupportedCoverComplement

open ErdosRadoCHAsym (W1)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3RegularMembership (neg exists_deciding_refinement)
open Erdos1172Part3RegularGreedyEnumeration (HasOrderedEmbeddingBelow)
open Erdos1172Part3NamedLocalRowCover (onConeDecisions)
open Erdos1172Part3NamedShortCofinalCover (coverName_onCone_iff)
open Erdos1172Part3SupportedCoverRealization (coverName)

variable {P V : Type} [Preorder P] [LinearOrder V] [WellFoundedLT V]

/-- Failure of a full complement embedding would let one ground member
of the original family cover the ambient order except for a short set. -/
theorem exists_ground_cover_union_of_no_complement_embedding
    (F : FunctionDecisions P W1 W1) (C : (W1 → W1) → Set V)
    (hclosed : CountablyClosed P) (p0 : P) (hcard : #V ≤ ℵ_ 1)
    (htype : typeLT V = (ω_ 1 : Ordinal.{0}) ^ (ω + 1))
    (hno : ¬HasOrderedEmbeddingBelow (I := V) (neg (coverName F C)) p0) :
    ∃ f : W1 → W1, ∃ A : Set V, typeLT A < (ω_ 1 : Ordinal.{0}) ^ (ω + 1) ∧ Set.univ ⊆ C f ∪ A := by
  obtain ⟨D, hD, hcoverage⟩ :=
    Erdos1172Part3NamedShortCover.exists_supported_named_short_covers hcard htype
  obtain ⟨q, _hqp0, e, H, hH⟩ := hcoverage P hclosed (neg (coverName F C)) p0 hno
  let restricted : FunctionDecisions (Set.Iic q) W1 W1 := onConeDecisions F q
  have hdense : ∀ p : Set.Iic q, p ≤ (⟨q, le_rfl⟩ : Set.Iic q) →
      ∀ x ∈ (Set.univ : Set V), ∃ r : Set.Iic q, r ≤ p ∧
        ((coverName restricted C).holds r x ∨ (coverName H (D e)).holds r x) := by
    intro p _ x _
    obtain ⟨r, hrp, hr⟩ := exists_deciding_refinement (coverName F C) p.val x
    let s : Set.Iic q := ⟨r, hrp.trans p.property⟩
    refine ⟨s, hrp, ?_⟩
    rcases hr with hx | hx
    · exact Or.inl ((coverName_onCone_iff q F C s x).mpr hx)
    · exact Or.inr (hH s x hx)
  have huniv : #(Set.univ : Set V) ≤ ℵ_ 1 := by
    simpa only [Cardinal.mk_univ] using hcard
  obtain ⟨f, g, hcover⟩ :=
    Erdos1172Part3SupportedCoverUnion.exists_ground_union_of_dense_members
      restricted H C (D e)
      (Erdos1172Part3ClosedDenseRequirements.countablyClosed_Iic hclosed q)
      ⟨q, le_rfl⟩ Set.univ huniv hdense
  exact ⟨f, D e g, (hD e).2.2 g, hcover⟩

/-- The actual complement of every uniformly short certified cover has
a full ordered decision embedding on every starting cone. -/
theorem hasOrderedEmbeddingBelow_neg_coverName
    (F : FunctionDecisions P W1 W1) (C : (W1 → W1) → Set V)
    (hclosed : CountablyClosed P) (p0 : P) (hcard : #V ≤ ℵ_ 1)
    (htype : typeLT V = (ω_ 1 : Ordinal.{0}) ^ (ω + 1))
    (hC : ∀ f, typeLT (C f) < (ω_ 1 : Ordinal.{0}) ^ (ω + 1)) :
    HasOrderedEmbeddingBelow (I := V) (neg (coverName F C)) p0 := by
  classical
  by_contra hno
  obtain ⟨f, A, hA, hcover⟩ :=
    exists_ground_cover_union_of_no_complement_embedding F C hclosed p0 hcard htype hno
  have hsmall : typeLT (C f ∪ A : Set V) < (ω_ 1 : Ordinal.{0}) ^ (ω + 1) :=
    Erdos1172Part3OmegaSuccessorUnion.union_type_lt htype (hC f) hA
  have hunivSmall : typeLT (Set.univ : Set V) < (ω_ 1 : Ordinal.{0}) ^ (ω + 1) :=
    (Ordinal.type_mono hcover).trans_lt hsmall
  have hVsmall : typeLT V < (ω_ 1 : Ordinal.{0}) ^ (ω + 1) :=
    OrderIso.Set.univ.ordinalType_congr.symm.trans_lt hunivSmall
  exact (lt_irrefl _) (htype.symm.trans_lt hVsmall)

end Erdos1172Part3SupportedCoverComplement
