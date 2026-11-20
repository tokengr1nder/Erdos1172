/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3HechlerFinitePrefixes

@[expose] public section

open Cardinal Ordinal Set Order

namespace Erdos1172Part3CountableHechlerProjections

open ErdosRadoCHAsym (W2)
open Erdos1172Part3CountableHechlerLimit
open Erdos1172Part3HechlerFinitePrefixes
open Erdos1172Part3IteratedHechlerOrder (liftBase liftBase_le)
open Erdos1172Part3StationaryDecisions
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3ClosedDecisionSystem (CliqueDecisions)

variable {hGCH : GCH}

theorem exists_limit_extending_prefix (p : Limit hGCH) {n : ℕ} (segment : Prefix hGCH n)
    (hprefix : ∀ k hk, segment.point k hk ≤ p.point k) :
    ∃ q : Limit hGCH, q ≤ p ∧ ∀ k hk, q.point k = segment.point k hk := by
  classical
  let next (k : ℕ) (previous : At hGCH k) : At hGCH (k + 1) :=
    if hk : k + 1 ≤ n then segment.point (k + 1) hk
    else liftBase (p.point (k + 1)) previous
  let branch : ∀ k : ℕ, At hGCH k :=
    fun k => Nat.rec (segment.point 0 (Nat.zero_le n)) next k
  have hmatch : ∀ k (hk : k ≤ n), branch k = segment.point k hk := by
    intro k hk
    cases k with
    | zero => rfl
    | succ k =>
      change next k (branch k) = segment.point (k + 1) hk
      dsimp only [next]
      erw [dif_pos hk]
  have hcoherent : ∀ k, (branch (k + 1)).base = branch k := by
    intro k
    change (next k (branch k)).base = branch k
    by_cases hk : k + 1 ≤ n
    · rw [show next k (branch k) = segment.point (k + 1) hk by
        dsimp only [next]
        erw [dif_pos hk]]
      exact (segment.coherent k (Nat.lt_of_succ_le hk)).trans
        (hmatch k (Nat.le_of_succ_le hk)).symm
    · dsimp only [next]
      erw [dif_neg hk]
      rfl
  have hbelow : ∀ k, branch k ≤ p.point k := by
    intro k
    induction k with
    | zero => exact hprefix 0 (Nat.zero_le n)
    | succ k ih =>
      by_cases hk : k + 1 ≤ n
      · rw [hmatch (k + 1) hk]
        exact hprefix (k + 1) hk
      · change next k (branch k) ≤ p.point (k + 1)
        rw [show next k (branch k) = liftBase (p.point (k + 1)) (branch k) by
          dsimp only [next]
          erw [dif_neg hk]]
        apply liftBase_le
        rw [p.coherent k]
        exact ih
  exact ⟨⟨branch, hcoherent⟩, hbelow, hmatch⟩

/-- Every earlier-stage strengthening lifts exactly, not just to a
compatible or still stronger earlier projection. -/
theorem exists_lift_at (p : Limit hGCH) (n : ℕ) (q : At hGCH n) (hqp : q ≤ p.point n) :
    ∃ r : Limit hGCH, r ≤ p ∧ r.point n = q := by
  obtain ⟨segment, hlast, hprefix⟩ := exists_prefix_below p n q hqp
  obtain ⟨r, hrp, hr⟩ := exists_limit_extending_prefix p segment hprefix
  exact ⟨r, hrp, (hr n le_rfl).trans hlast⟩

def liftPredicate (n : ℕ) (U : At hGCH n → W2 → Prop) : Limit hGCH → W2 → Prop :=
  fun p a => U (p.point n) a

theorem liftPredicate_persistent (n : ℕ) {U : At hGCH n → W2 → Prop}
    (hU : Persistent U) : Persistent (liftPredicate n U) := fun hqp ha => hU (hqp n) ha

theorem possible_liftPredicate (n : ℕ) (U : At hGCH n → W2 → Prop) (p : Limit hGCH) :
    possible (liftPredicate n U) p = possible U (p.point n) := by
  ext a
  constructor
  · rintro ⟨q, hqp, hqa⟩
    exact ⟨q.point n, hqp n, hqa⟩
  · rintro ⟨q, hqp, hqa⟩
    obtain ⟨r, hrp, hr⟩ := exists_lift_at p n q hqp
    refine ⟨r, hrp, ?_⟩
    change U (r.point n) a
    rwa [hr]

/-- Exact projection lifting preserves and reflects stationary possible
membership from any finite stage, not just from the initial stage. -/
theorem stationaryAt_liftPredicate_iff (n : ℕ) (U : At hGCH n → W2 → Prop)
    (p : Limit hGCH) : StationaryAt (liftPredicate n U) p ↔ StationaryAt U (p.point n) := by
  constructor
  · intro h q hqp
    obtain ⟨r, hrp, hr⟩ := exists_lift_at p n q hqp
    have hstat := h r hrp
    rwa [possible_liftPredicate, hr] at hstat
  · intro h q hqp
    rw [possible_liftPredicate]
    exact h (q.point n) (hqp n)

def liftFunction (n : ℕ) {I V : Type} (F : FunctionDecisions (At hGCH n) I V) :
    FunctionDecisions (Limit hGCH) I V where
  decides p i v := F.decides (p.point n) i v
  dense := by
    intro p i
    obtain ⟨q, hqp, v, hv⟩ := F.dense (p.point n) i
    obtain ⟨r, hrp, hr⟩ := exists_lift_at p n q hqp
    refine ⟨r, hrp, v, ?_⟩
    rwa [hr]
  persistent hqp hv := F.persistent (hqp n) hv
  unique hv hw := F.unique hv hw

def liftClique (n : ℕ) {I V : Type} [LinearOrder I] [LinearOrder V] {G : SimpleGraph V}
    (sys : CliqueDecisions (At hGCH n) I V G) : CliqueDecisions (Limit hGCH) I V G where
  decides p i v := sys.decides (p.point n) i v
  dense := by
    intro p i
    obtain ⟨q, hqp, v, hv⟩ := sys.dense (p.point n) i
    obtain ⟨r, hrp, hr⟩ := exists_lift_at p n q hqp
    refine ⟨r, hrp, v, ?_⟩
    rwa [hr]
  persistent hqp hv := sys.persistent (hqp n) hv
  unique hv hw := sys.unique hv hw
  ordered hij hv hw := sys.ordered hij hv hw
  adjacent hij hv hw := sys.adjacent hij hv hw

theorem lift_cross (n : ℕ) {I : Type} [LinearOrder I] {G : SimpleGraph W2}
    (sys : CliqueDecisions (At hGCH n) I W2 G) (U : At hGCH n → W2 → Prop)
    (hcross : ∀ p a, U p a → ∀ i x, sys.decides p i x → x < a ∧ G.Adj x a) :
    ∀ p a, liftPredicate n U p a → ∀ i x, (liftClique n sys).decides p i x →
      x < a ∧ G.Adj x a := by
  intro p a ha i x hx
  exact hcross (p.point n) a ha i x hx

end Erdos1172Part3CountableHechlerProjections
