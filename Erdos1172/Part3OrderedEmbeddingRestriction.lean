/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3OrderedEmbeddingSmallness
public import Erdos1172.Part3SupportedCoverRestriction

@[expose] public section

/-!
# Exact stage localization of hereditary ordered smallness

Complete restriction lifts earlier cone-local decisions exactly. Finite
cover certificates and actual cover membership are unchanged under this
lifting, including all dense refinements.

Earlier full embeddings therefore lift. Conversely, an earlier small
source has a short named cover on a strengthening. Lifting that cover
would bound any later full embedding, contradicting joint ground
realization. This proves equality of the hereditary smallness predicates
at the omega-successor threshold; no localization premise is assumed.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3OrderedEmbeddingRestriction

open ErdosRadoCHAsym (W1)
open Erdos1172Part3CompleteRestriction (CompleteRestriction)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3RegularMembership (RegularName)
open Erdos1172Part3RegularGreedyEnumeration (HasOrderedEmbeddingBelow)
open Erdos1172Part3SupportedCoverRealization (Certificate coverName)
open Erdos1172Part3NamedDiscreteCoverProfile (CoveredAt)
open Erdos1172Part3OrderedEmbeddingSmallness

variable {P Q I X : Type} [Preorder P] [Preorder Q]

/-- The restriction map between compatible starting cones. Exact
surjectivity onto the entire larger earlier cone is not needed. -/
def coneMap (r : CompleteRestriction P Q) (p0 : P) (q0 : Q)
    (h0 : r.restrict p0 ≤ q0) : Set.Iic p0 →o Set.Iic q0 :=
  ⟨fun p => ⟨r.restrict p.val, (r.restrict.monotone p.property).trans h0⟩,
    fun _ _ h => r.restrict.monotone h⟩

/-- Exact lifting of an earlier cone-local decision system. Each needed
earlier strengthening lifts below the current later condition. -/
def liftConeDecisions (r : CompleteRestriction P Q) (p0 : P) (q0 : Q)
    (h0 : r.restrict p0 ≤ q0) (F : FunctionDecisions (Set.Iic q0) I X) :
    FunctionDecisions (Set.Iic p0) I X where
  decides p i x := F.decides (coneMap r p0 q0 h0 p) i x
  dense := by
    intro p i
    obtain ⟨q, hqp, x, hx⟩ := F.dense (coneMap r p0 q0 h0 p) i
    obtain ⟨s, hsp, hs⟩ := r.lift p.val q.val hqp
    let t : Set.Iic p0 := ⟨s, hsp.trans p.property⟩
    have heq : coneMap r p0 q0 h0 t = q := Subtype.ext hs
    refine ⟨t, hsp, x, ?_⟩
    simpa only [heq] using hx
  persistent := fun hqp hx => F.persistent (r.restrict.monotone hqp) hx
  unique := fun hx hy => F.unique hx hy

theorem certificate_liftCone_iff (r : CompleteRestriction P Q) (p0 : P) (q0 : Q)
    (h0 : r.restrict p0 ≤ q0) (F : FunctionDecisions (Set.Iic q0) W1 W1)
    (C : (W1 → W1) → Set X) (p : Set.Iic p0) (x : X) :
    Certificate (liftConeDecisions r p0 q0 h0 F) C p x ↔
      Certificate F C (coneMap r p0 q0 h0 p) x := Iff.rfl

/-- Exact cone lifting preserves actual dense cover membership, not only
the possibility of a finite certificate. -/
theorem coverName_liftCone_iff (r : CompleteRestriction P Q) (p0 : P) (q0 : Q)
    (h0 : r.restrict p0 ≤ q0) (F : FunctionDecisions (Set.Iic q0) W1 W1)
    (C : (W1 → W1) → Set X) (p : Set.Iic p0) (x : X) :
    (coverName (liftConeDecisions r p0 q0 h0 F) C).holds p x ↔
      (coverName F C).holds (coneMap r p0 q0 h0 p) x := by
  constructor
  · intro hp q hqp
    obtain ⟨s, hsp, hs⟩ := r.lift p.val q.val hqp
    let t : Set.Iic p0 := ⟨s, hsp.trans p.property⟩
    obtain ⟨u, hut, hu⟩ := hp t hsp
    refine ⟨coneMap r p0 q0 h0 u, ?_, hu⟩
    change r.restrict u.val ≤ q.val
    have hle : r.restrict u.val ≤ r.restrict t.val := r.restrict.monotone hut
    simpa only [t, hs] using hle
  · intro hp q hqp
    obtain ⟨s, hsq, hs⟩ := hp (coneMap r p0 q0 h0 q)
      ((coneMap r p0 q0 h0).monotone hqp)
    obtain ⟨t, htq, ht⟩ := r.lift q.val s.val hsq
    let u : Set.Iic p0 := ⟨t, htq.trans q.property⟩
    have heq : coneMap r p0 q0 h0 u = s := Subtype.ext ht
    refine ⟨u, htq, ?_⟩
    change Certificate F C (coneMap r p0 q0 h0 u) x
    rwa [heq]

/-- A covering name on an earlier cone lifts to any compatible later
cone, retaining the same fixed ground covering family. -/
theorem coveredAt_liftCone (r : CompleteRestriction P Q) (p0 : P) (q0 : Q)
    (h0 : r.restrict p0 ≤ q0) (U : RegularName Q X) (C : (W1 → W1) → Set X)
    (hcover : CoveredAt U C q0) : CoveredAt (r.liftRegular U) C p0 := by
  obtain ⟨F, hF⟩ := hcover
  refine ⟨liftConeDecisions r p0 q0 h0 F, ?_⟩
  intro p x hx
  apply (coverName_liftCone_iff r p0 q0 h0 F C p x).mpr
  exact hF (coneMap r p0 q0 h0 p) x hx

variable [LinearOrder I] [LinearOrder X]

/-- Earlier full ordered embeddings lift without a closure assumption. -/
theorem hasOrderedEmbeddingBelow_lift (r : CompleteRestriction P Q)
    (U : RegularName Q X) (p0 : P) (q0 : Q) (h0 : r.restrict p0 ≤ q0)
    (hE : HasOrderedEmbeddingBelow (I := I) U q0) :
    HasOrderedEmbeddingBelow (I := I) (r.liftRegular U) p0 := by
  obtain ⟨E, hordered, hmem⟩ := hE
  refine ⟨liftConeDecisions r p0 q0 h0 E, ?_, ?_⟩
  · intro p i j x y hij hx hy
    exact hordered (coneMap r p0 q0 h0 p) i j x y hij hx hy
  · intro p i x hx
    exact hmem (coneMap r p0 q0 h0 p) i x hx

/-- Later hereditary smallness implies earlier hereditary smallness by
lifting any allegedly full earlier sub-cone. -/
theorem smallName_of_lift (r : CompleteRestriction P Q) (p : P)
    (U : RegularName Q X) (hsmall : (smallName (I := I)).holds p (r.liftRegular U)) :
    (smallName (I := I)).holds (r.restrict p) U := by
  intro q hqp hE
  obtain ⟨s, hsp, hs⟩ := r.lift p q hqp
  exact hsmall s hsp (hasOrderedEmbeddingBelow_lift r U s q hs.le hE)

variable {V : Type} [LinearOrder V] [WellFoundedLT V]

/-- Hereditary ordered smallness at the omega-successor threshold is
exactly invariant under complete stage restriction. Both orders are
countably closed, and all short covers are constructed by the proved
named-cover theorem. -/
theorem smallName_lift_iff (r : CompleteRestriction P Q)
    (hclosedP : CountablyClosed P) (hclosedQ : CountablyClosed Q)
    (hcard : #V ≤ ℵ_ 1) (htype : typeLT V = (ω_ 1 : Ordinal.{0}) ^ (ω + 1))
    (p : P) (U : RegularName Q V) :
    (smallName (I := V)).holds p (r.liftRegular U) ↔
      (smallName (I := V)).holds (r.restrict p) U := by
  constructor
  · exact smallName_of_lift r p U
  · intro hsmall s hsp hE
    have hno : ¬HasOrderedEmbeddingBelow (I := V) U (r.restrict s) :=
      hsmall (r.restrict s) (r.restrict.monotone hsp)
    obtain ⟨C, hC, hcoverage⟩ :=
      Erdos1172Part3NamedShortCover.exists_supported_named_short_covers hcard htype
    obtain ⟨q, hqs, e, F, hF⟩ := hcoverage Q hclosedQ U (r.restrict s) hno
    obtain ⟨t, hts, ht⟩ := r.lift s q hqs
    have hcover : CoveredAt (r.liftRegular U) (C e) t :=
      coveredAt_liftCone r t q ht.le U (C e) ⟨F, hF⟩
    have hshort : ∀ f, typeLT (C e f) < typeLT V := by
      intro f
      rw [htype]
      exact (hC e).2.2 f
    have hsmallLift : SmallAt (I := V) (r.liftRegular U) t :=
      smallAt_of_coveredAt (I := V) hclosedP hcard hcover hshort
    exact hsmallLift t le_rfl (hasOrderedEmbeddingBelow_persistent hts hE)

end Erdos1172Part3OrderedEmbeddingRestriction
