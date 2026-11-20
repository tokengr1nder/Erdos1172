/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3OrderedCoreTrace
public import Erdos1172.Part3CliqueDecisionComposition

@[expose] public section

/-!
# Full ordered extraction with hereditary loss transfer

An actual ordered selector retains its original index, not just a point
origin. Composing any hypothetical full loss embedding with that selector
would give a full loss embedding in the original core. Thus the extracted
core retains hereditary order-smallness of every original loss name.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3OrderedCoreExtraction

open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3ClosedDecisionSystem (CliqueDecisions)
open Erdos1172Part3NamedCofinality (OrderedDecisions)
open Erdos1172Part3RegularMembership (RegularName neg)
open Erdos1172Part3RegularGreedyEnumeration (HasOrderedEmbeddingBelow)
open Erdos1172Part3RegularCliqueNeighborhoods (cliqueFunction)
open Erdos1172Part3OrderedCoreTrace (pullback trace)
open Erdos1172Part3NamedLocalRowCover (onConeDecisions)
open Erdos1172Part3NamedCofinalRowCovers (nestCone flattenDecisions)
open Erdos1172Part3CliqueDecisionComposition (compose onCone)

variable {P I J K X : Type} [Preorder P]

def composeFunctions (A : FunctionDecisions P I J) (E : FunctionDecisions P J K) :
    FunctionDecisions P I K where
  decides p i k := ∃ j, A.decides p i j ∧ E.decides p j k
  dense := by
    intro p i
    obtain ⟨q, hqp, j, hj⟩ := A.dense p i
    obtain ⟨r, hrq, k, hk⟩ := E.dense q j
    exact ⟨r, hrq.trans hqp, k, j, A.persistent hrq hj, hk⟩
  persistent := by
    rintro p q i k hqp ⟨j, hj, hk⟩
    exact ⟨j, A.persistent hqp hj, E.persistent hqp hk⟩
  unique := by
    rintro p i k l ⟨j, hj, hk⟩ ⟨j', hj', hl⟩
    have h : j = j' := A.unique hj hj'
    subst j'
    exact E.unique hk hl

variable [LinearOrder I] [LinearOrder X]
  {G : SimpleGraph X}

def selectedCore (core : CliqueDecisions P I X G) (q : P)
    (E : FunctionDecisions (Iic q) I I) (hE : OrderedDecisions E) :
    CliqueDecisions (Iic q) I X G := compose E (onCone q core) hE

theorem selectedCore_actual (core : CliqueDecisions P I X G) (q : P)
    (E : FunctionDecisions (Iic q) I I) (hE : OrderedDecisions E)
    (U : RegularName P X)
    (hmem : ∀ p i j, E.decides p i j → (pullback (cliqueFunction core) U).holds p.val j)
    (p : Iic q) (i : I) (x : X) (hx : (selectedCore core q E hE).decides p i x) :
    U.holds p.val x ∧ ∃ j, core.decides p.val j x := by
  obtain ⟨j, hj, hx⟩ := hx
  exact ⟨hmem p i j hj p.val le_rfl x hx, j, hx⟩

/-- Hereditary loss smallness survives this selected subcore on the
actual cone. The proof composes named index decisions, not ground maps. -/
theorem selectedCore_trace (core : CliqueDecisions P I X G) (q : P)
    (E : FunctionDecisions (Iic q) I I) (hE : OrderedDecisions E)
    (U : RegularName P X) (p : Iic q) (hsmall : (trace core).holds p.val U) :
    (trace (selectedCore core q E hE)).holds p
      (Erdos1172Part3RegularConeRestriction.onCone q U) := by
  intro s hsp hfull
  obtain ⟨A, hAord, hAmem⟩ := hfull
  let F := composeFunctions A (onConeDecisions E s)
  let B := flattenDecisions s F
  apply hsmall s.val hsp
  refine ⟨B, ?_, ?_⟩
  · intro t i j x y hij hx hy
    obtain ⟨k, hik, hkx⟩ := hx
    obtain ⟨l, hjl, hly⟩ := hy
    exact hE (hAord (nestCone s t) i j k l hij hik hjl) hkx hly
  · intro t i k hk v hvt x hx
    obtain ⟨j, hij, hjk⟩ := hk
    have hsub := hAmem (nestCone s t) i j hij
    let w : Iic q := ⟨v, (hvt.trans t.property).trans s.property⟩
    have he : E.decides w j k := E.persistent hvt hjk
    exact hsub w hvt x ⟨k, he, hx⟩

/-- Positivity for the actual order-small ideal yields a full subcore
and transfers every original small loss, with no finite-trace premise. -/
theorem exists_full_subcore (core : CliqueDecisions P I X G)
    (p0 : P) (U : RegularName P X) (hpos : (neg (trace core)).holds p0 U) :
    ∃ q : P, q ≤ p0 ∧ ∃ sub : CliqueDecisions (Iic q) I X G,
      (∀ p i x, sub.decides p i x → U.holds p.val x ∧ ∃ j, core.decides p.val j x) ∧
      ∀ p : Iic q, ∀ W : RegularName P X, (trace core).holds p.val W →
        (trace sub).holds p (Erdos1172Part3RegularConeRestriction.onCone q W) := by
  classical
  have hex : ∃ q : P, q ≤ p0 ∧
      HasOrderedEmbeddingBelow (I := I) (pullback (cliqueFunction core) U) q := by
    by_contra h
    apply hpos p0 le_rfl
    intro q hqp hq
    exact h ⟨q, hqp, hq⟩
  obtain ⟨q, hqp0, E, hordered, hmem⟩ := hex
  have hE : OrderedDecisions E := fun {p i j x y} hij hx hy => hordered p i j x y hij hx hy
  exact ⟨q, hqp0, selectedCore core q E hE,
    selectedCore_actual core q E hE U hmem,
    fun p W hW => selectedCore_trace core q E hE W p hW⟩

end Erdos1172Part3OrderedCoreExtraction
