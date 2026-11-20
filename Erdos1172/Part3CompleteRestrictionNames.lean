/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CompleteRestriction

@[expose] public section

/-!
# Source pullback and nice-name inclusion along complete restrictions

Pulling a regular source back along the empty-tail inclusion remains
regular. Lifting that pullback implies the original source; the reverse
implication for an arbitrary source is not asserted. Conversely, an
earlier nice clique has a canonical full-order nice name with exactly
the same decisions after restriction, including all common-red endpoints.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3CompleteRestrictionNames

open ErdosRadoCHAsym (W2)
open Erdos1172Part3CompleteRestriction (CompleteRestriction Supported)
open Erdos1172Part3RegularMembership (RegularName)
open Erdos1172Part3NiceFunctionNames (NiceFunctionName)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3RegularCliqueNeighborhoods (afterClique)
open Erdos1172Part3StationaryDecisions (StationaryAt)

variable {P Q X I V : Type} [Preorder P] [Preorder Q]

def pullRegular (r : CompleteRestriction P Q) (U : RegularName P X) : RegularName Q X where
  holds q x := U.holds (r.embed q) x
  persistent hqp hx := U.persistent (r.embed.monotone hqp) hx
  of_dense := by
    intro q x h
    apply U.of_dense
    intro p hpq
    obtain ⟨t, htp, ht⟩ := h (r.restrict p) ((r.le_embed_iff p q).mp hpq)
    obtain ⟨s, hsp, hs⟩ := r.lift p t htp
    refine ⟨s, hsp, U.persistent ((r.le_embed_iff s t).mpr ?_) ht⟩
    exact hs.le

theorem pull_lift (r : CompleteRestriction P Q) (U : RegularName Q X) :
    pullRegular r (r.liftRegular U) = U := by
  apply RegularName.ext
  intro q x
  change U.holds (r.restrict (r.embed q)) x ↔ U.holds q x
  rw [r.restrict_embed]

/-- Only this direction holds for an arbitrary full-order source. -/
theorem lift_pull_implies (r : CompleteRestriction P Q) (U : RegularName P X)
    (p : P) (x : X) (h : (r.liftRegular (pullRegular r U)).holds p x) : U.holds p x :=
  U.persistent (r.below_embed p) h

theorem stationary_pull_implies (r : CompleteRestriction P Q) (U : RegularName P W2)
    (p : P) (h : StationaryAt (pullRegular r U).holds (r.restrict p)) :
    StationaryAt U.holds p := by
  have hlift := (r.stationary_lift_iff (pullRegular r U).holds p).mpr h
  intro q hqp
  apply (hlift q hqp).mono
  rintro a ⟨s, hsq, hs⟩
  exact ⟨s, hsq, lift_pull_implies r U s a hs⟩

def pushFunction (r : CompleteRestriction P Q) (N : NiceFunctionName Q I V) :
    NiceFunctionName P I V where
  graph i := (fun qv : Q × V => (r.embed qv.1, qv.2)) '' N.graph i
  small i := Cardinal.mk_image_le.trans (N.small i)
  consistent := by
    rintro i p v q w ⟨⟨s, x⟩, hs, hsx⟩ ⟨⟨t, y⟩, ht, hty⟩ hcompat
    have hsp : r.embed s = p := congrArg Prod.fst hsx
    have hxv : x = v := congrArg Prod.snd hsx
    have htq : r.embed t = q := congrArg Prod.fst hty
    have hyw : y = w := congrArg Prod.snd hty
    subst p q v w
    apply N.consistent i s x t y hs ht
    have h := (r.compatible_embed_iff (r.embed s) t).mp hcompat
    simpa only [r.restrict_embed] using h
  predense := by
    intro p i
    obtain ⟨q, v, hq, hcompat⟩ := N.predense (r.restrict p) i
    exact ⟨r.embed q, v, ⟨(q, v), hq, rfl⟩, (r.compatible_embed_iff p q).mpr hcompat⟩

theorem pushFunction_supported (r : CompleteRestriction P Q) (N : NiceFunctionName Q I V) :
    Supported r (pushFunction r N) := by
  rintro i p v ⟨⟨q, w⟩, hq, heq⟩
  exact ⟨q, congrArg Prod.fst heq⟩

theorem pushFunction_decides_iff (r : CompleteRestriction P Q) (N : NiceFunctionName Q I V)
    (p : P) (i : I) (v : V) :
    (pushFunction r N).toDecisions.decides p i v ↔ N.toDecisions.decides (r.restrict p) i v := by
  constructor
  · rintro ⟨q, ⟨⟨s, w⟩, hs, heq⟩, hpq⟩
    have hsq : r.embed s = q := congrArg Prod.fst heq
    have hwv : w = v := congrArg Prod.snd heq
    subst q v
    exact ⟨s, hs, (r.le_embed_iff p s).mp hpq⟩
  · rintro ⟨q, hq, hpq⟩
    exact ⟨r.embed q, ⟨(q, v), hq, rfl⟩, (r.le_embed_iff p q).mpr hpq⟩

variable [LinearOrder I] [LinearOrder V] {G : SimpleGraph V}

def pushClique (r : CompleteRestriction P Q) (N : NiceCliqueName Q I V G) :
    NiceCliqueName P I V G where
  function := pushFunction r N.function
  ordered := by
    intro p i j x y hij hx hy
    exact N.ordered hij ((pushFunction_decides_iff r N.function p i x).mp hx)
      ((pushFunction_decides_iff r N.function p j y).mp hy)
  adjacent := by
    intro p i j x y hij hx hy
    exact N.adjacent hij ((pushFunction_decides_iff r N.function p i x).mp hx)
      ((pushFunction_decides_iff r N.function p j y).mp hy)

theorem pushClique_decides_iff (r : CompleteRestriction P Q) (N : NiceCliqueName Q I V G)
    (p : P) (i : I) (v : V) :
    (pushClique r N).toClique.decides p i v ↔ N.toClique.decides (r.restrict p) i v :=
  pushFunction_decides_iff r N.function p i v

theorem pushClique_after_iff (r : CompleteRestriction P Q) (N : NiceCliqueName Q I V G)
    (p : P) (a : V) :
    (afterClique (pushClique r N).toClique).holds p a ↔
      (afterClique N.toClique).holds (r.restrict p) a := by
  constructor
  · intro h q hqp i x hx
    obtain ⟨s, hsp, hs⟩ := r.lift p q hqp
    apply h s hsp i x
    apply (pushClique_decides_iff r N s i x).mpr
    rwa [hs]
  · intro h q hqp i x hx
    exact h (r.restrict q) (r.restrict.monotone hqp) i x ((pushClique_decides_iff r N q i x).mp hx)

theorem pushClique_stationary_future_iff (r : CompleteRestriction P Q)
    {G : SimpleGraph W2} (N : NiceCliqueName Q I W2 G)
    (source : RegularName Q W2) (p : P) :
    StationaryAt (fun q a => source.holds (r.restrict q) a ∧
      (afterClique (pushClique r N).toClique).holds q a) p ↔
    StationaryAt (fun q a => source.holds q a ∧ (afterClique N.toClique).holds q a) (r.restrict p) := by
  have heq : (fun q a => source.holds (r.restrict q) a ∧
      (afterClique (pushClique r N).toClique).holds q a) =
      (fun q a => source.holds (r.restrict q) a ∧ (afterClique N.toClique).holds (r.restrict q) a) := by
    funext q a
    exact propext (and_congr_right (fun _ => pushClique_after_iff r N q a))
  rw [heq]
  exact r.stationary_lift_iff (fun q a => source.holds q a ∧ (afterClique N.toClique).holds q a) p

end Erdos1172Part3CompleteRestrictionNames
