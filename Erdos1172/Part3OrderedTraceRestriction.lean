/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3OrderedCoreTrace
public import Erdos1172.Part3OrderedEmbeddingRestriction
public import Erdos1172.Part3TraceCompleteRestriction

@[expose] public section

/-!
# Exact localization and cone refinement of ordered traces

Complete restriction preserves actual inverse images whenever the two
decision systems agree exactly. Hereditary ordered smallness then gives
exact trace localization at the omega-successor threshold.

Cone restriction is stronger: its exact identification needs no closure
or type bound. A one-way refinement of total unique decisions already
gives equality of regular inverse images, so globalizing and normalizing
a cone-local core preserves its ordered trace on that cone.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3OrderedTraceRestriction

open ErdosRadoCHAsym (W2)
open Erdos1172Part3RegularMembership (RegularName)
open Erdos1172Part3RegularConeRestriction (onCone)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3ClosedDecisionSystem (CliqueDecisions CountablyClosed)
open Erdos1172Part3CompleteRestriction (CompleteRestriction)
open Erdos1172Part3RegularCliqueNeighborhoods (cliqueFunction)
open Erdos1172Part3NamedLocalRowCover (onConeDecisions)
open Erdos1172Part3NamedCofinalRowCovers (nestCone flattenCone flattenDecisions)
open Erdos1172Part3RegularGreedyEnumeration (HasOrderedEmbeddingBelow)
open Erdos1172Part3OrderedEmbeddingSmallness (smallName)
open Erdos1172Part3OrderedCoreTrace (pullback trace)
open Erdos1172Part3TraceCompleteRestriction (SameDecisions)

variable {P Q I X : Type} [Preorder P] [Preorder Q]

theorem pullback_lift_iff (r : CompleteRestriction P Q)
    (full : FunctionDecisions P I X) (earlier : FunctionDecisions Q I X)
    (hdec : ∀ p i x, full.decides p i x ↔ earlier.decides (r.restrict p) i x)
    (p : P) (U : RegularName Q X) (i : I) :
    (pullback full (r.liftRegular U)).holds p i ↔
      (pullback earlier U).holds (r.restrict p) i := by
  constructor
  · intro hp q hqp x hx
    obtain ⟨s, hsp, hs⟩ := r.lift p q hqp
    have hfull : full.decides s i x := (hdec s i x).mpr (by rwa [hs])
    have hU := hp s hsp x hfull
    change U.holds (r.restrict s) x at hU
    rwa [hs] at hU
  · intro hp q hqp x hx
    exact hp (r.restrict q) (r.restrict.monotone hqp) x ((hdec q i x).mp hx)

theorem pullback_lift (r : CompleteRestriction P Q)
    (full : FunctionDecisions P I X) (earlier : FunctionDecisions Q I X)
    (hdec : ∀ p i x, full.decides p i x ↔ earlier.decides (r.restrict p) i x)
    (U : RegularName Q X) :
    pullback full (r.liftRegular U) = r.liftRegular (pullback earlier U) :=
  RegularName.ext (fun p i => pullback_lift_iff r full earlier hdec p U i)

/-- Dense refinement cannot change an actual regular inverse image. -/
theorem pullback_eq_of_refines (F N : FunctionDecisions P I X)
    (href : ∀ p i x, N.decides p i x → F.decides p i x) (U : RegularName P X) :
    pullback N U = pullback F U := by
  apply RegularName.ext
  intro p i
  constructor
  · intro hp q hqp x hx
    apply U.of_dense q x
    intro r hrq
    obtain ⟨s, hsr, y, hy⟩ := N.dense r i
    have hxy : x = y :=
      F.unique (F.persistent (hsr.trans hrq) hx) (href s i y hy)
    subst y
    exact ⟨s, hsr, hp s ((hsr.trans hrq).trans hqp) x hy⟩
  · intro hp q hqp x hx
    exact hp q hqp x (href q i x hx)

theorem pullback_onCone (q : P) (F : FunctionDecisions P I X) (U : RegularName P X) :
    pullback (onConeDecisions F q) (onCone q U) = onCone q (pullback F U) := by
  apply RegularName.ext
  intro p i
  constructor
  · intro hp r hrp x hx
    exact hp ⟨r, hrp.trans p.property⟩ hrp x hx
  · intro hp r hrp x hx
    exact hp r.val hrp x hx

/-- Add back the redundant intermediate cone proof to a decision name. -/
def nestDecisions {q : P} (p : Set.Iic q)
    (F : FunctionDecisions (Set.Iic p.val) I X) : FunctionDecisions (Set.Iic p) I X where
  decides r i x := F.decides (flattenCone p r) i x
  dense := by
    intro r i
    obtain ⟨s, hsr, x, hx⟩ := F.dense (flattenCone p r) i
    exact ⟨nestCone p s, hsr, x, hx⟩
  persistent hsr hx := F.persistent hsr hx
  unique hx hy := F.unique hx hy

section ConeSmallness

variable [LinearOrder I] [LinearOrder X]

theorem hasOrderedEmbeddingBelow_onCone_iff (q : P) (U : RegularName P X)
    (p : Set.Iic q) :
    HasOrderedEmbeddingBelow (I := I) (onCone q U) p ↔
      HasOrderedEmbeddingBelow (I := I) U p.val := by
  constructor
  · rintro ⟨E, hordered, hmem⟩
    refine ⟨flattenDecisions p E, ?_, ?_⟩
    · intro s i j x y hij hx hy
      exact hordered (nestCone p s) i j x y hij hx hy
    · intro s i x hx
      exact hmem (nestCone p s) i x hx
  · rintro ⟨E, hordered, hmem⟩
    refine ⟨nestDecisions p E, ?_, ?_⟩
    · intro s i j x y hij hx hy
      exact hordered (flattenCone p s) i j x y hij hx hy
    · intro s i x hx
      exact hmem (flattenCone p s) i x hx

theorem smallName_onCone_iff (q : P) (U : RegularName P X) (p : Set.Iic q) :
    (smallName (I := I)).holds p (onCone q U) ↔
      (smallName (I := I)).holds p.val U := by
  constructor
  · intro hp r hrp hE
    let s : Set.Iic q := ⟨r, hrp.trans p.property⟩
    exact hp s hrp ((hasOrderedEmbeddingBelow_onCone_iff q U s).mpr hE)
  · intro hp r hrp hE
    exact hp r.val hrp ((hasOrderedEmbeddingBelow_onCone_iff q U r).mp hE)

end ConeSmallness

section Traces

variable [LinearOrder I] [LinearOrder X] {G : SimpleGraph X}

theorem trace_eq_of_refines (core refined : CliqueDecisions P I X G)
    (href : ∀ p i x, refined.decides p i x → core.decides p i x) :
    trace refined = trace core := by
  apply RegularName.ext
  intro p U
  change (smallName (I := I)).holds p (pullback (cliqueFunction refined) U) ↔
    (smallName (I := I)).holds p (pullback (cliqueFunction core) U)
  rw [pullback_eq_of_refines (cliqueFunction core) (cliqueFunction refined) href U]

theorem pullback_onCone_eq_of_refines (q : P)
    (sub : CliqueDecisions (Set.Iic q) I X G) (global : CliqueDecisions P I X G)
    (href : ∀ p : Set.Iic q, ∀ i x, global.decides p.val i x → sub.decides p i x)
    (U : RegularName P X) :
    pullback (cliqueFunction sub) (onCone q U) = onCone q (pullback (cliqueFunction global) U) := by
  calc
    pullback (cliqueFunction sub) (onCone q U) =
        pullback (onConeDecisions (cliqueFunction global) q) (onCone q U) :=
      (pullback_eq_of_refines (cliqueFunction sub)
        (onConeDecisions (cliqueFunction global) q) href (onCone q U)).symm
    _ = onCone q (pullback (cliqueFunction global) U) :=
      pullback_onCone q (cliqueFunction global) U

/-- Normalization or globalization with one-way refinement preserves
the entire ordered trace exactly on the selected cone. -/
theorem trace_onCone_iff_of_refines (q : P)
    (sub : CliqueDecisions (Set.Iic q) I X G) (global : CliqueDecisions P I X G)
    (href : ∀ p : Set.Iic q, ∀ i x, global.decides p.val i x → sub.decides p i x)
    (p : Set.Iic q) (U : RegularName P X) :
    (trace sub).holds p (onCone q U) ↔ (trace global).holds p.val U := by
  change (smallName (I := I)).holds p (pullback (cliqueFunction sub) (onCone q U)) ↔
    (smallName (I := I)).holds p.val (pullback (cliqueFunction global) U)
  rw [pullback_onCone_eq_of_refines q sub global href U]
  exact smallName_onCone_iff q (pullback (cliqueFunction global) U) p

theorem trace_of_onCone_refines (q : P)
    (sub : CliqueDecisions (Set.Iic q) I X G) (global : CliqueDecisions P I X G)
    (href : ∀ p : Set.Iic q, ∀ i x, global.decides p.val i x → sub.decides p i x)
    (p : Set.Iic q) (U : RegularName P X)
    (hsmall : (trace sub).holds p (onCone q U)) : (trace global).holds p.val U :=
  (trace_onCone_iff_of_refines q sub global href p U).mp hsmall

end Traces

variable [LinearOrder I] [WellFoundedLT I] {G : SimpleGraph W2}

theorem trace_lift_iff (r : CompleteRestriction P Q)
    (full : CliqueDecisions P I W2 G) (earlier : CliqueDecisions Q I W2 G)
    (hdec : SameDecisions r full earlier)
    (hclosedP : CountablyClosed P) (hclosedQ : CountablyClosed Q)
    (hcard : #I ≤ ℵ_ 1) (htype : typeLT I = (ω_ 1 : Ordinal.{0}) ^ (ω + 1))
    (p : P) (U : RegularName Q W2) :
    (trace full).holds p (r.liftRegular U) ↔
      (trace earlier).holds (r.restrict p) U := by
  change (smallName (I := I)).holds p (pullback (cliqueFunction full) (r.liftRegular U)) ↔
    (smallName (I := I)).holds (r.restrict p) (pullback (cliqueFunction earlier) U)
  rw [pullback_lift r (cliqueFunction full) (cliqueFunction earlier) hdec U]
  exact Erdos1172Part3OrderedEmbeddingRestriction.smallName_lift_iff r
    hclosedP hclosedQ hcard htype p (pullback (cliqueFunction earlier) U)

end Erdos1172Part3OrderedTraceRestriction
