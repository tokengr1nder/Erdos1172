/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3RegularCliqueNeighborhoods

@[expose] public section

/-!
# Complete restriction to an earlier decision order

The extension map is a genuine empty-tail inclusion: every condition
lies below the extension of its restriction. Together with exact
lifting this reflects compatibility with an embedd condition.
Names supported on the inclusion range then restrict with equality
of decisions, not merely a choice of compatible point origins.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3CompleteRestriction

open Erdos1172Part3StationaryDecisions (Compatible StationaryAt possible)
open Erdos1172Part3NiceFunctionNames (NiceFunctionName)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3RegularMembership (RegularName)
open Erdos1172Part3RegularCliqueNeighborhoods (afterClique)

variable (P Q : Type) [Preorder P] [Preorder Q]

structure CompleteRestriction where
  restrict : P →o Q
  embed : Q →o P
  restrict_embed : ∀ q, restrict (embed q) = q
  below_embed : ∀ p, p ≤ embed (restrict p)
  lift : ∀ p q, q ≤ restrict p → ∃ s, s ≤ p ∧ restrict s = q

variable {P Q}

theorem CompleteRestriction.embed_injective (r : CompleteRestriction P Q) :
    Injective r.embed := by
  intro q t h
  have h' := congrArg r.restrict h
  simpa only [r.restrict_embed] using h'

theorem CompleteRestriction.le_embed_iff (r : CompleteRestriction P Q) (p : P) (q : Q) :
    p ≤ r.embed q ↔ r.restrict p ≤ q := by
  constructor
  · intro h
    simpa only [r.restrict_embed] using r.restrict.monotone h
  · intro h
    exact (r.below_embed p).trans (r.embed.monotone h)

theorem CompleteRestriction.compatible_embed_iff (r : CompleteRestriction P Q)
    (p : P) (q : Q) : Compatible p (r.embed q) ↔ Compatible (r.restrict p) q := by
  constructor
  · rintro ⟨s, hsp, hsq⟩
    exact ⟨r.restrict s, r.restrict.monotone hsp, (r.le_embed_iff s q).mp hsq⟩
  · rintro ⟨s, hsp, hsq⟩
    obtain ⟨t, htp, ht⟩ := r.lift p s hsp
    refine ⟨t, htp, (r.le_embed_iff t q).mpr ?_⟩
    rwa [ht]

def CompleteRestriction.liftRegular (r : CompleteRestriction P Q) {X : Type}
    (U : RegularName Q X) : RegularName P X where
  holds p x := U.holds (r.restrict p) x
  persistent hqp hx := U.persistent (r.restrict.monotone hqp) hx
  of_dense := by
    intro p x h
    apply U.of_dense
    intro q hqp
    obtain ⟨s, hsp, hs⟩ := r.lift p q hqp
    obtain ⟨t, hts, ht⟩ := h s hsp
    refine ⟨r.restrict t, ?_, ht⟩
    have hle := r.restrict.monotone hts
    rwa [hs] at hle

theorem CompleteRestriction.possible_lift (r : CompleteRestriction P Q)
    (U : Q → ErdosRadoCHAsym.W2 → Prop) (p : P) :
    possible (fun q x => U (r.restrict q) x) p = possible U (r.restrict p) := by
  ext x
  constructor
  · rintro ⟨q, hqp, hq⟩
    exact ⟨r.restrict q, r.restrict.monotone hqp, hq⟩
  · rintro ⟨q, hqp, hq⟩
    obtain ⟨s, hsp, hs⟩ := r.lift p q hqp
    refine ⟨s, hsp, ?_⟩
    change U (r.restrict s) x
    rwa [hs]

theorem CompleteRestriction.stationary_lift_iff (r : CompleteRestriction P Q)
    (U : Q → ErdosRadoCHAsym.W2 → Prop) (p : P) :
    StationaryAt (fun q a => U (r.restrict q) a) p ↔ StationaryAt U (r.restrict p) := by
  constructor
  · intro h q hqp
    obtain ⟨s, hsp, hs⟩ := r.lift p q hqp
    have hstat := h s hsp
    rwa [r.possible_lift, hs] at hstat
  · intro h q hqp
    rw [r.possible_lift]
    exact h (r.restrict q) (r.restrict.monotone hqp)

variable {I V : Type}

def Supported (r : CompleteRestriction P Q) (N : NiceFunctionName P I V) : Prop :=
  ∀ i p v, (p, v) ∈ N.graph i → p ∈ Set.range r.embed

def restrictFunction (r : CompleteRestriction P Q) (N : NiceFunctionName P I V)
    (hs : Supported r N) : NiceFunctionName Q I V where
  graph i := {qv | (r.embed qv.1, qv.2) ∈ N.graph i}
  small := by
    intro i
    let encode (qv : {qv : Q × V | (r.embed qv.1, qv.2) ∈ N.graph i}) : N.graph i :=
      ⟨(r.embed qv.val.1, qv.val.2), qv.property⟩
    have hinj : Injective encode := by
      intro qv tw h
      have hp := congrArg (fun z : N.graph i => z.val) h
      apply Subtype.ext
      exact Prod.ext (r.embed_injective (congrArg (fun z : P × V => z.1) hp))
        (congrArg (fun z : P × V => z.2) hp)
    exact (Cardinal.mk_le_of_injective hinj).trans (N.small i)
  consistent := by
    rintro i p v q w hp hq ⟨s, hsp, hsq⟩
    exact N.consistent i (r.embed p) v (r.embed q) w hp hq
      ⟨r.embed s, r.embed.monotone hsp, r.embed.monotone hsq⟩
  predense := by
    intro p i
    obtain ⟨q, v, hq, hcompat⟩ := N.predense (r.embed p) i
    obtain ⟨s, rfl⟩ := hs i q v hq
    refine ⟨s, v, hq, ?_⟩
    have h := (r.compatible_embed_iff (r.embed p) s).mp hcompat
    simpa only [r.restrict_embed] using h

theorem restrictFunction_decides_iff (r : CompleteRestriction P Q)
    (N : NiceFunctionName P I V) (hs : Supported r N) (p : P) (i : I) (v : V) :
    (restrictFunction r N hs).toDecisions.decides (r.restrict p) i v ↔
      N.toDecisions.decides p i v := by
  constructor
  · rintro ⟨q, hq, hpq⟩
    exact ⟨r.embed q, hq, (r.le_embed_iff p q).mpr hpq⟩
  · rintro ⟨q, hq, hpq⟩
    obtain ⟨s, rfl⟩ := hs i q v hq
    exact ⟨s, hq, (r.le_embed_iff p s).mp hpq⟩

variable [LinearOrder I] [LinearOrder V] {G : SimpleGraph V}

def restrictClique (r : CompleteRestriction P Q) (N : NiceCliqueName P I V G)
    (hs : Supported r N.function) : NiceCliqueName Q I V G where
  function := restrictFunction r N.function hs
  ordered := by
    intro p i j x y hij hx hy
    have hx' : (restrictFunction r N.function hs).toDecisions.decides
        (r.restrict (r.embed p)) i x := by simpa only [r.restrict_embed] using hx
    have hy' : (restrictFunction r N.function hs).toDecisions.decides
        (r.restrict (r.embed p)) j y := by simpa only [r.restrict_embed] using hy
    exact N.ordered hij ((restrictFunction_decides_iff r N.function hs _ _ _).mp hx')
      ((restrictFunction_decides_iff r N.function hs _ _ _).mp hy')
  adjacent := by
    intro p i j x y hij hx hy
    have hx' : (restrictFunction r N.function hs).toDecisions.decides
        (r.restrict (r.embed p)) i x := by simpa only [r.restrict_embed] using hx
    have hy' : (restrictFunction r N.function hs).toDecisions.decides
        (r.restrict (r.embed p)) j y := by simpa only [r.restrict_embed] using hy
    exact N.adjacent hij ((restrictFunction_decides_iff r N.function hs _ _ _).mp hx')
      ((restrictFunction_decides_iff r N.function hs _ _ _).mp hy')

theorem restrictClique_decides_iff (r : CompleteRestriction P Q)
    (N : NiceCliqueName P I V G) (hs : Supported r N.function) (p : P) (i : I) (v : V) :
    (restrictClique r N hs).toClique.decides (r.restrict p) i v ↔ N.toClique.decides p i v :=
  restrictFunction_decides_iff r N.function hs p i v

/-- All common-red endpoint truth is reflected, not just one endpoint
chosen before descent. The support premise is essential. -/
theorem restrictClique_after_iff (r : CompleteRestriction P Q)
    (N : NiceCliqueName P I V G) (hs : Supported r N.function) (p : P) (a : V) :
    (afterClique (restrictClique r N hs).toClique).holds (r.restrict p) a ↔
      (afterClique N.toClique).holds p a := by
  constructor
  · intro h q hqp i x hx
    exact h (r.restrict q) (r.restrict.monotone hqp) i x
      ((restrictClique_decides_iff r N hs q i x).mpr hx)
  · intro h q hqp i x hx
    obtain ⟨s, hsp, hsbase⟩ := r.lift p q hqp
    have hx' : (restrictClique r N hs).toClique.decides (r.restrict s) i x :=
      hsbase.symm ▸ hx
    exact h s hsp i x ((restrictClique_decides_iff r N hs s i x).mp hx')

end Erdos1172Part3CompleteRestriction
