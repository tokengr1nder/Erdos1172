/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3RegularMembership

@[expose] public section

open Set

namespace Erdos1172Part3RegularConeRestriction

open ErdosRadoCHAsym (W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3StationaryDecisions (possible StationaryAt)

variable {P X : Type} [Preorder P]

/-- Restriction to an actual starting cone preserves dense stability. -/
def onCone (p0 : P) (U : RegularName P X) : RegularName (Set.Iic p0) X where
  holds p x := U.holds p.val x
  persistent := fun hqp h => U.persistent hqp h
  of_dense p x h := by
    apply U.of_dense p.val x
    intro q hqp
    obtain ⟨s, hsq, hs⟩ := h ⟨q, hqp.trans p.property⟩ hqp
    exact ⟨s.val, hsq, hs⟩

theorem onCone_meet (p0 : P) (U V : RegularName P X) :
    onCone p0 (meet U V) = meet (onCone p0 U) (onCone p0 V) := by
  apply RegularName.ext
  intro p x
  rfl

theorem onCone_ground (p0 : P) (s : Set X) :
    onCone p0 (ground s) = ground s := by
  apply RegularName.ext
  intro p x
  rfl

theorem possible_onCone (p0 : P) (U : RegularName P W2) (p : Set.Iic p0) :
    possible (onCone p0 U).holds p = possible U.holds p.val := by
  ext a
  constructor
  · rintro ⟨q, hqp, hq⟩
    exact ⟨q.val, hqp, hq⟩
  · rintro ⟨q, hqp, hq⟩
    exact ⟨⟨q, hqp.trans p.property⟩, hqp, hq⟩

theorem stationaryAt_onCone_iff (p0 : P) (U : RegularName P W2) (p : Set.Iic p0) :
    StationaryAt (onCone p0 U).holds p ↔ StationaryAt U.holds p.val := by
  constructor
  · intro h q hqp
    have hq := h ⟨q, hqp.trans p.property⟩ hqp
    rwa [possible_onCone] at hq
  · intro h q hqp
    rw [possible_onCone]
    exact h q.val hqp

end Erdos1172Part3RegularConeRestriction
