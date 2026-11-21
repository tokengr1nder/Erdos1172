/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedCoverProfile
public import Erdos1172.Part3SupportedCoverComplement
public import Erdos1172.Part3SupportedCoverRestriction
public import Erdos1172.Part3CliqueDecisionComposition

@[expose] public section

/-!
# Stationary thinning by actual uniformly short loss covers

A stationary uniform profile gives a single new upper function name for
the loss-cover names of the retained future points. The complement of its
short cover contains a full ordered selector. Composing that selector with
the lifted earlier clique gives a full subclique joined to every actual
retained future point.

The output is a decision system on the selected condition's cone. Its
decisions retain actual origins in the earlier core; no extension to
incompatible conditions or ground total domination is asserted.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3StationarySupportedThinning

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3StationaryDecisions (Persistent possible StationaryAt)
open Erdos1172Part3IteratedHechlerOrder (Condition liftFunction)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3IteratedHechlerPreservation (liftClique)
open Erdos1172Part3NamedCofinality (OrderedDecisions)
open Erdos1172Part3NamedCliqueThinning (StationaryCliqueDecisions)
open Erdos1172Part3NamedCoverProfile
open Erdos1172Part3SupportedCoverRealization (coverName)
open Erdos1172Part3SupportedCoverRestriction (coverName_liftFunction_iff)
open Erdos1172Part3CliqueDecisionComposition (compose onCone compose_decides_iff)

variable {P V : Type} [Preorder P] [LinearOrder V] [WellFoundedLT V]

/-- Uniform actual covers of the bad-adjacency index losses suffice for
stationary thinning at the full omega-successor index type. The resulting
clique and future live on the selected cone and preserve actual origins. -/
theorem exists_stationary_clique_from_supported_losses
    (center : CountablyCenteredCode P) (hclosed : CountablyClosed P) (hCH : CH)
    (p0 : Condition P) (G : SimpleGraph W2) (core : CliqueDecisions P V W2 G)
    (hcard : #V ≤ ℵ_ 1) (htype : typeLT V = (ω_ 1 : Ordinal.{0}) ^ (ω + 1))
    (U : P → W2 → Prop) (hU : Persistent U)
    (hs : IsStationary (possible U p0.base))
    (hafter : ∀ p a, U p a → ∀ i x, core.decides p i x → x < a)
    (F : W2 → FunctionDecisions P W1 W1) (C : (W1 → W1) → Set V)
    (hC : ∀ f, typeLT (C f) < (ω_ 1 : Ordinal.{0}) ^ (ω + 1))
    (hloss : ∀ p a, U p a → ∀ i x, core.decides p i x → ¬G.Adj x a →
      (coverName (F a) C).holds p i) :
    ∃ p : Condition P, p ≤ p0 ∧
      ∃ sys : StationaryCliqueDecisions (Set.Iic p) V G,
        sys.start = (⟨p, Erdos1172Part3IteratedHechlerOrder.stronger_refl (P := P) p⟩ : Set.Iic p) ∧
        (∀ q a, sys.future q a → U q.val.base a) ∧
        ∀ q i x, sys.clique.decides q i x → ∃ z : V, core.decides q.val.base z x := by
  obtain ⟨bound, profile, p, hpp0, hp⟩ :=
    exists_stationary_uniform_profile hclosed center hCH p0 U hU hs F
  let H : FunctionDecisions (Condition P) W1 W1 := upperFunction hclosed bound profile
  obtain ⟨selector, hselectorOrder, hselectorActual⟩ :=
    Erdos1172Part3SupportedCoverComplement.hasOrderedEmbeddingBelow_neg_coverName
      H C (Erdos1172Part3IteratedHechlerClosure.countablyClosed hclosed) p hcard htype hC
  have hordered : OrderedDecisions selector :=
    fun {q i j x y} hij hx hy => hselectorOrder q i j x y hij hx hy
  let previous : CliqueDecisions (Set.Iic p) V W2 G := onCone p (liftClique core)
  let clique : CliqueDecisions (Set.Iic p) V W2 G := compose selector previous hordered
  let future (q : Set.Iic p) (a : W2) : Prop := ProfileMembers U F bound profile q.val a
  have hfuture : Persistent future :=
    fun {_ _ _} hqp ha => profileMembers_persistent U hU F bound profile hqp ha
  have hstationary : StationaryAt future
      (⟨p, Erdos1172Part3IteratedHechlerOrder.stronger_refl (P := P) p⟩ : Set.Iic p) := by
    intro q _
    apply (hp q.val q.property).mono
    rintro a ⟨r, hrq, ha⟩
    exact ⟨⟨r, hrq.trans q.property⟩, hrq, ha⟩
  have hcross : ∀ q a, future q a → ∀ j x, clique.decides q j x → x < a ∧ G.Adj x a := by
    intro q a ha j x hx
    obtain ⟨i, hi, hxi⟩ := (compose_decides_iff selector previous hordered q j x).mp hx
    change core.decides q.val.base i x at hxi
    have haU : U q.val.base a := ha.1.1
    refine ⟨hafter q.val.base a haU i x hxi, ?_⟩
    by_contra hbad
    have hbaseCover : (coverName (F a) C).holds q.val.base i := hloss q.val.base a haU i x hxi hbad
    have hliftCover : (coverName (liftFunction (F a)) C).holds q.val i :=
      (coverName_liftFunction_iff (F a) C q.val i).mpr hbaseCover
    have hupperCover : (coverName H C).holds q.val i :=
      upper_cover_holds_of_profileMember hclosed U F bound profile C ha hliftCover
    exact hselectorActual q j i hi q.val le_rfl hupperCover
  refine ⟨p, hpp0, {
    start := ⟨p, Erdos1172Part3IteratedHechlerOrder.stronger_refl (P := P) p⟩
    clique := clique
    future := future
    persistent := hfuture
    stationary := hstationary
    cross := hcross }, rfl, ?_, ?_⟩
  · exact fun _ _ ha => ha.1.1
  · intro q j x hx
    obtain ⟨i, _, hxi⟩ := (compose_decides_iff selector previous hordered q j x).mp hx
    exact ⟨i, hxi⟩

end Erdos1172Part3StationarySupportedThinning
