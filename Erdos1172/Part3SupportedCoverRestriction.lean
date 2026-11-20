/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3SupportedCoverRealization
public import Erdos1172.Part3CanonicalBaseRestriction

@[expose] public section

/-! Exact restriction laws for actual supported-cover membership. -/

open Set

namespace Erdos1172Part3SupportedCoverRestriction

open ErdosRadoCHAsym (W1)
open Erdos1172Part3CompleteRestriction (CompleteRestriction)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3SupportedCoverRealization (Certificate coverName)
open Erdos1172Part3IteratedHechlerOrder (Condition liftFunction)

variable {P Q I X : Type} [Preorder P] [Preorder Q]

def liftDecisions (r : CompleteRestriction P Q) (F : FunctionDecisions Q I X) :
    FunctionDecisions P I X where
  decides p i x := F.decides (r.restrict p) i x
  dense := by
    intro p i
    obtain ⟨q, hqp, x, hx⟩ := F.dense (r.restrict p) i
    obtain ⟨s, hsp, hs⟩ := r.lift p q hqp
    exact ⟨s, hsp, x, hs.symm ▸ hx⟩
  persistent hqp hx := F.persistent (r.restrict.monotone hqp) hx
  unique hx hy := F.unique hx hy

theorem certificate_lift_iff (r : CompleteRestriction P Q)
    (F : FunctionDecisions Q W1 W1) (C : (W1 → W1) → Set X) (p : P) (x : X) :
    Certificate (liftDecisions r F) C p x ↔ Certificate F C (r.restrict p) x := Iff.rfl

theorem coverName_lift_iff (r : CompleteRestriction P Q)
    (F : FunctionDecisions Q W1 W1) (C : (W1 → W1) → Set X) (p : P) (x : X) :
    (coverName (liftDecisions r F) C).holds p x ↔ (coverName F C).holds (r.restrict p) x := by
  constructor
  · intro h q hqp
    obtain ⟨s, hsp, hs⟩ := r.lift p q hqp
    obtain ⟨t, hts, ht⟩ := h s hsp
    refine ⟨r.restrict t, ?_, ht⟩
    simpa only [hs] using r.restrict.monotone hts
  · intro h q hqp
    obtain ⟨s, hsq, hs⟩ := h (r.restrict q) (r.restrict.monotone hqp)
    obtain ⟨t, htq, ht⟩ := r.lift q s hsq
    refine ⟨t, htq, ?_⟩
    change Certificate F C (r.restrict t) x
    rwa [ht]

theorem coverName_liftFunction_iff
    (F : FunctionDecisions P W1 W1) (C : (W1 → W1) → Set X)
    (p : Condition P) (x : X) :
    (coverName (liftFunction F) C).holds p x ↔ (coverName F C).holds p.base x :=
  coverName_lift_iff Erdos1172Part3CanonicalBaseRestriction.oneStage F C p x

end Erdos1172Part3SupportedCoverRestriction
