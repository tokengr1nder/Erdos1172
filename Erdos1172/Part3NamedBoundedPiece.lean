/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedCofinalCovers
public import Erdos1172.Part3NamedCofinalEndpoint

@[expose] public section

/-!
# Moving a bounded pure named piece into its endpoint order

An exact pure-power enumeration below a fixed endpoint can be reindexed
by the canonical pure-power domain and restricted to the endpoint's open
initial segment. Dense cofinality below that endpoint becomes the usual
cofinal decision property there. The lower-rank named-cover input then
gives actual membership in the image of its same ground cover family.

The named-cover structure is an explicit induction input. This adapter
does not assume or conclude its existence at any unproved rank. Neither
the order adapters nor the image-certificate transfer use closure; closure
is passed only to the supplied named-cover theorem.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedBoundedPiece

open ErdosRadoCHAsym (W1)
open Erdos1172Part3FiniteTraceSchemes (Index typeLT_index)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName)
open Erdos1172Part3NamedCofinality (OrderedDecisions CofinalDecisions)
open Erdos1172Part3NamedFinalTail (DenseCoverage)
open Erdos1172Part3NamedCofinalEndpoint (CofinalBelow)
open Erdos1172Part3NamedCofinalCovers (NamedCofinalCovers)
open Erdos1172Part3SupportedCoverRealization (coverName)

variable {P I J V : Type} [Preorder P] [LinearOrder I] [LinearOrder J] [LinearOrder V]

/-- Reindex by an actual ground order isomorphism. -/
def domainIso (E : FunctionDecisions P I V) (e : J ≃o I) : FunctionDecisions P J V :=
  Erdos1172Part3DecisionSelection.reindex E e

theorem domainIso_ordered (E : FunctionDecisions P I V) (e : J ≃o I)
    (hordered : OrderedDecisions E) : OrderedDecisions (domainIso E e) := by
  intro p j k x y hjk hx hy
  exact hordered (e.strictMono hjk) hx hy

theorem domainIso_cofinal (E : FunctionDecisions P I V) (e : J ≃o I)
    (hcofinal : CofinalDecisions E) : CofinalDecisions (domainIso E e) := by
  intro p cut
  obtain ⟨q, hqp, i, x, hx, hcut⟩ := hcofinal p cut
  obtain ⟨j, rfl⟩ := e.surjective i
  exact ⟨q, hqp, j, x, hx, hcut⟩

theorem domainIso_denseCoverage (E : FunctionDecisions P I V) (e : J ≃o I)
    (U : RegularName P V) (hcoverage : DenseCoverage E U) :
    DenseCoverage (domainIso E e) U := by
  intro p x hx
  obtain ⟨q, hqp, i, hi⟩ := hcoverage p x hx
  obtain ⟨j, rfl⟩ := e.surjective i
  exact ⟨q, hqp, j, hi⟩

theorem domainIso_actual (E : FunctionDecisions P I V) (e : J ≃o I)
    (U : RegularName P V)
    (hmem : ∀ p i x, E.decides p i x → U.holds p x) :
    ∀ p j x, (domainIso E e).decides p j x → U.holds p x :=
  fun p j x hx => hmem p (e j) x hx

/-- Actual membership restricted to the fixed ground initial segment. -/
def belowName (U : RegularName P V) (y : V) : RegularName P (Set.Iio y) :=
  Erdos1172Part3RegularMembership.reindex U Subtype.val

/-- Restrict the target of every decision using its actual strict bound. -/
def belowE (E : FunctionDecisions P I V) (y : V)
    (hbound : ∀ p i x, E.decides p i x → x < y) :
    FunctionDecisions P I (Set.Iio y) where
  decides p i x := E.decides p i x.val
  dense p i := by
    obtain ⟨q, hqp, x, hx⟩ := E.dense p i
    exact ⟨q, hqp, ⟨x, hbound q i x hx⟩, hx⟩
  persistent hqp h := E.persistent hqp h
  unique hx hy := Subtype.ext (E.unique hx hy)

theorem belowE_ordered (E : FunctionDecisions P I V) (y : V)
    (hbound : ∀ p i x, E.decides p i x → x < y)
    (hordered : OrderedDecisions E) : OrderedDecisions (belowE E y hbound) := by
  intro p i j x z hij hx hz
  exact hordered hij hx hz

theorem belowE_denseCoverage (E : FunctionDecisions P I V) (y : V)
    (hbound : ∀ p i x, E.decides p i x → x < y)
    (U : RegularName P V) (hcoverage : DenseCoverage E U) :
    DenseCoverage (belowE E y hbound) (belowName U y) := by
  intro p x hx
  obtain ⟨q, hqp, i, hi⟩ := hcoverage p x.val hx
  exact ⟨q, hqp, i, hi⟩

theorem belowE_actual (E : FunctionDecisions P I V) (y : V)
    (hbound : ∀ p i x, E.decides p i x → x < y)
    (U : RegularName P V) (hmem : ∀ p i x, E.decides p i x → U.holds p x) :
    ∀ p i x, (belowE E y hbound).decides p i x → (belowName U y).holds p x :=
  fun p i x hx => hmem p i x.val hx

/-- Dense cofinal actual members below y give cofinal decisions in Iio y.
The equality case at the test point is retained. -/
theorem belowE_cofinal (E : FunctionDecisions P I V) (y : V)
    (hbound : ∀ p i x, E.decides p i x → x < y)
    (U : RegularName P V) (hcoverage : DenseCoverage E U)
    (hcofinal : ∀ p : P, CofinalBelow U p y) :
    CofinalDecisions (belowE E y hbound) := by
  intro p cut
  obtain ⟨q, hqp, x, hx, hcutx, hxy⟩ := hcofinal p p le_rfl cut.val cut.property
  obtain ⟨r, hrq, i, hi⟩ := hcoverage q x hx
  exact ⟨r, hrq.trans hqp, i, ⟨x, hxy⟩, hi, hcutx⟩

variable [WellFoundedLT I] [WellFoundedLT V]

/-- A bounded pure piece has a canonical-domain ordered cofinal exact
enumeration in the fixed endpoint order. No named covering premise is used. -/
theorem exists_below_pure_enumeration (k : ℕ) (U : RegularName P V)
    (E : FunctionDecisions P I V)
    (htype : typeLT I = (ω_ 1 : Ordinal.{0}) ^ ((k + 1 : ℕ) : Ordinal))
    (hordered : OrderedDecisions E) (hcoverage : DenseCoverage E U)
    (hmem : ∀ p i x, E.decides p i x → U.holds p x)
    (y : V) (hbound : ∀ p x, U.holds p x → x < y)
    (hcofinal : ∀ p : P, CofinalBelow U p y) :
    ∃ G : FunctionDecisions P (Index k) (Set.Iio y),
      OrderedDecisions G ∧ CofinalDecisions G ∧ DenseCoverage G (belowName U y) ∧
        ∀ p j x, G.decides p j x → (belowName U y).holds p x := by
  have hEbound : ∀ p i x, E.decides p i x → x < y :=
    fun p i x hx => hbound p x (hmem p i x hx)
  let EB : FunctionDecisions P I (Set.Iio y) := belowE E y hEbound
  have htypes : typeLT (Index k) = typeLT I := (typeLT_index k).trans htype.symm
  obtain ⟨e⟩ := Ordinal.type_eq.mp htypes
  let iso : Index k ≃o I := OrderIso.ofRelIsoLT e
  exact ⟨domainIso EB iso,
    domainIso_ordered EB iso (belowE_ordered E y hEbound hordered),
    domainIso_cofinal EB iso (belowE_cofinal E y hEbound U hcoverage hcofinal),
    domainIso_denseCoverage EB iso (belowName U y)
      (belowE_denseCoverage E y hEbound U hcoverage),
    domainIso_actual EB iso (belowName U y) (belowE_actual E y hEbound U hmem)⟩

/-- An actual finite-supported cover certificate maps to its set image
without deciding any additional coordinates. -/
theorem coverName_image_holds {X Y : Type} (F : FunctionDecisions P W1 W1)
    (C : (W1 → W1) → Set X) (f : X → Y) (p : P) (x : X)
    (hx : (coverName F C).holds p x) :
    (coverName F (fun g => f '' C g)).holds p (f x) := by
  intro q hqp
  obtain ⟨r, hrq, g, support, hdec, hcover⟩ := hx q hqp
  exact ⟨r, hrq, g, support, hdec, fun h hh => ⟨x, hcover h hh, rfl⟩⟩

/-- Apply the explicitly supplied lower-rank named-cover structure and
map its actual membership certificates back into the ambient order. -/
theorem exists_named_cover_of_bounded_pure_piece
    (k : ℕ) (y : V) (C : NamedCofinalCovers k (Set.Iio y))
    (hclosed : CountablyClosed P) (U : RegularName P V) (E : FunctionDecisions P I V)
    (htype : typeLT I = (ω_ 1 : Ordinal.{0}) ^ ((k + 1 : ℕ) : Ordinal))
    (hordered : OrderedDecisions E) (hcoverage : DenseCoverage E U)
    (hmem : ∀ p i x, E.decides p i x → U.holds p x)
    (hbound : ∀ p x, U.holds p x → x < y)
    (hcofinal : ∀ p : P, CofinalBelow U p y) :
    ∃ F : FunctionDecisions P W1 W1,
      ∀ p x, U.holds p x →
        (coverName F (fun f => (Subtype.val : Set.Iio y → V) '' C.family f)).holds p x := by
  obtain ⟨G, hGorder, hGcofinal, hGcoverage, hGmem⟩ :=
    exists_below_pure_enumeration k U E htype hordered hcoverage hmem y hbound hcofinal
  obtain ⟨F, hF⟩ := C.named_covers P hclosed (belowName U y) G
    hGorder hGcofinal hGcoverage hGmem
  refine ⟨F, ?_⟩
  intro p x hx
  exact coverName_image_holds F C.family (Subtype.val : Set.Iio y → V)
    p ⟨x, hbound p x hx⟩ (hF p ⟨x, hbound p x hx⟩ hx)

end Erdos1172Part3NamedBoundedPiece
