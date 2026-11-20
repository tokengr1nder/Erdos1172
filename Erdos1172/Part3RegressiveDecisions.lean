/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3StationaryDecisions

@[expose] public section

/-!
# Pressing down persistent regressive decisions

Stationary many possible regressive decisions have one value which
remains stationarily possible below a fixed strengthening. The argument
uses the ordinary ground-type pressing-down theorem and the small
antichain preservation argument, with all decision premises explicit.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3RegressiveDecisions

open Erdos1172Part3NeighborhoodCode (W2)
open Erdos1172Part3StationaryDecisions
open Erdos1172Part3RedPredecessorReflection (stationaryPressingDown)

variable {P : Type} [Preorder P]

/-- Freeze one value and retain stationary possibilities below a single
condition. The deciding conditions themselves need not be constant. -/
theorem exists_stationary_decision_fiber_below (hcc : OmegaTwoCC P) (p0 : P)
    (S : Set W2) (hS : IsStationary S) (decides : P → W2 → W2 → Prop)
    (hpersistent : ∀ b, Persistent (fun p a => decides p a b))
    (hdecides : ∀ a ∈ S, ∃ p : P, p ≤ p0 ∧ ∃ b : W2, decides p a b)
    (hregressive : ∀ p a b, decides p a b → b < a) :
    ∃ b : W2, ∃ p : P, p ≤ p0 ∧ StationaryAt (fun q a => decides q a b) p := by
  classical
  have witness (a : W2) (ha : a ∈ S) :
      ∃ b : W2, ∃ p : P, p ≤ p0 ∧ decides p a b := by
    obtain ⟨p, hpp0, b, hab⟩ := hdecides a ha
    exact ⟨b, p, hpp0, hab⟩
  let chosen (a : W2) : W2 := if ha : a ∈ S then (witness a ha).choose else a
  have hchosen (a : W2) (ha : a ∈ S) :
      ∃ p : P, p ≤ p0 ∧ decides p a (chosen a) := by
    simpa only [chosen, dif_pos ha] using (witness a ha).choose_spec
  have hreg (a : W2) (ha : a ∈ S) : chosen a < a := by
    obtain ⟨p, _, hp⟩ := hchosen a ha
    exact hregressive p a (chosen a) hp
  obtain ⟨b, hfiber⟩ := stationaryPressingDown S chosen hS hreg
  have hpossible : IsStationary (possible (fun p a => decides p a b) p0) := by
    apply hfiber.mono
    intro a ha
    obtain ⟨p, hpp0, hp⟩ := hchosen a ha.1
    rw [ha.2] at hp
    exact ⟨p, hpp0, hp⟩
  obtain ⟨p, hpp0, hp⟩ := exists_stationary_refinement hcc
    (fun p a => decides p a b) (hpersistent b) p0 hpossible
  exact ⟨b, p, hpp0, hp⟩

/-- The source may itself be a persistent system of possible members.
Only its ground set of possibilities at the starting condition is used
for pressing down. -/
theorem exists_stationary_regressive_fiber (hcc : OmegaTwoCC P) (p0 : P)
    (U : P → W2 → Prop) (hstationary : StationaryAt U p0)
    (decides : P → W2 → W2 → Prop)
    (hpersistent : ∀ b, Persistent (fun p a => decides p a b))
    (hdense : ∀ p a, U p a → ∃ q : P, q ≤ p ∧ ∃ b : W2, decides q a b)
    (hregressive : ∀ p a b, decides p a b → b < a) :
    ∃ b : W2, ∃ p : P, p ≤ p0 ∧ StationaryAt (fun q a => decides q a b) p := by
  apply exists_stationary_decision_fiber_below hcc p0 (possible U p0)
    (hstationary p0 le_rfl) decides hpersistent _ hregressive
  rintro a ⟨p, hpp0, hpa⟩
  obtain ⟨q, hqp, b, hqab⟩ := hdense p a hpa
  exact ⟨q, hqp.trans hpp0, b, hqab⟩

end Erdos1172Part3RegressiveDecisions
