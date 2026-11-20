/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3OmegaPowerIndex

@[expose] public section

/-!
# A coherent tower of growing finite cores

Each new block belongs to the preceding stationary common-red future.
Those sources remain eventually local, so the proved finite factory can
be applied repeatedly in the same full order. Countable closure retains
all containment conditions. No stationarity of the limit intersection
is asserted or used.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3GrowingFiniteTower

open ErdosRadoCHAsym (W1 W2 IsOmegaOneSup)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularStageLocality (EventuallyLocal eventuallyLocal_ground)
open Erdos1172Part3RegularCliqueNeighborhoods (afterClique)
open Erdos1172Part3RegularNeighborhoodCode (blockName eval_blockName)
open Erdos1172Part3TransfiniteStageLocality (Full Earlier restriction eventually_local_code)
open Erdos1172Part3TransfiniteRankedFailures (eventuallyLocal_meet)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3FiniteTraceSchemes (Index mk_index_le)
open Erdos1172Part3FullRankedCoreReflection (coreFuture)
open Erdos1172Part3FullStationaryFiniteCores (finite_factory)
open Erdos1172Part3StationaryDecisions (StationaryAt)
open OrdinalRamsey (HasCliqueOfType)

theorem eventuallyLocal_coreFuture (hGCH : GCH) {I : Type} [LinearOrder I] (hI : #I ≤ ℵ_ 1)
    {G : SimpleGraph W2} (source : RegularName (Full hGCH) W2)
    (hsource : EventuallyLocal (Earlier hGCH) (restriction hGCH) source)
    (N : NiceCliqueName (Full hGCH) I W2 G) (a : W2) :
    EventuallyLocal (Earlier hGCH) (restriction hGCH) (coreFuture source N a) := by
  have hN : EventuallyLocal (Earlier hGCH) (restriction hGCH) (afterClique N.toClique) := by
    simpa only [eval_blockName] using eventually_local_code hGCH G G hI (blockName N)
  exact eventuallyLocal_meet hGCH hsource (eventuallyLocal_meet hGCH
    (eventuallyLocal_ground (Earlier hGCH) (restriction hGCH) _) hN)

structure SourceState (hGCH : GCH) where
  start : Full hGCH
  source : RegularName (Full hGCH) W2
  sup : ∀ p a, source.holds p a → IsOmegaOneSup a
  locality : EventuallyLocal (Earlier hGCH) (restriction hGCH) source
  stationary : StationaryAt source.holds start

structure NextCore (hGCH : GCH) (G : SimpleGraph W2) (n : ℕ) (old : SourceState hGCH) where
  next : SourceState hGCH
  name : NiceCliqueName (Full hGCH) (Index n) W2 G
  below : next.start ≤ old.start
  follows : ∀ p a, next.source.holds p a → old.source.holds p a
  future : ∀ p a, next.source.holds p a → ∀ z x,
    name.toClique.decides p z x → x < a ∧ G.Adj x a
  points : ∀ p : Full hGCH, p ≤ next.start → ∀ z x,
    name.toClique.decides p z x → old.source.holds p x

theorem exists_next_core (hGCH : GCH) (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (n : ℕ) (old : SourceState hGCH) : Nonempty (NextCore hGCH G n old) := by
  obtain ⟨a, q, hq, _, N, _, hpoints, hfuture⟩ := finite_factory hGCH G H hcompl hred hblue n
    old.source old.sup old.locality old.start old.stationary
  let next : SourceState hGCH := {
    start := q
    source := coreFuture old.source N a
    sup := fun p b hb => old.sup p b hb.1
    locality := eventuallyLocal_coreFuture hGCH (mk_index_le n) old.source old.locality N a
    stationary := hfuture }
  exact ⟨⟨next, N, hq, fun _ _ h => h.1, fun p _ h z x hx => h.2.2 p le_rfl z x hx, hpoints⟩⟩

structure GrowingTower (hGCH : GCH) (G : SimpleGraph W2) where
  start : Full hGCH
  sources : ℕ → RegularName (Full hGCH) W2
  names : ∀ n : ℕ, NiceCliqueName (Full hGCH) (Index n) W2 G
  follows : ∀ n p a, (sources (n + 1)).holds p a → (sources n).holds p a
  future : ∀ n p a, (sources (n + 1)).holds p a → ∀ z x,
    (names n).toClique.decides p z x → x < a ∧ G.Adj x a
  points : ∀ n p, p ≤ start → ∀ z x, (names n).toClique.decides p z x → (sources n).holds p x

theorem exists_growing_tower_from_source (hGCH : GCH) (G H : SimpleGraph W2)
    (hcompl : IsCompl G H) (hred : ¬HasCliqueOfType G (ω_ 2))
    (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) (initial : SourceState hGCH) :
    ∃ tower : GrowingTower hGCH G, tower.start ≤ initial.start ∧ tower.sources 0 = initial.source := by
  classical
  let next (n : ℕ) (old : SourceState hGCH) : NextCore hGCH G n old :=
    Classical.choice (exists_next_core hGCH G H hcompl hred hblue n old)
  let chain : ℕ → SourceState hGCH := fun n => Nat.rec initial (fun n old => (next n old).next) n
  have hstep (n : ℕ) : (chain (n + 1)).start ≤ (chain n).start := (next n (chain n)).below
  have hanti : Antitone (fun n => (chain n).start) := antitone_nat_of_succ_le hstep
  let C : Set (Full hGCH) := Set.range (fun n => (chain n).start)
  have hC : IsChain (· ≤ ·) C := by
    rintro p ⟨i, rfl⟩ q ⟨j, rfl⟩ _
    rcases le_total i j with hij | hji
    · exact Or.inr (hanti hij)
    · exact Or.inl (hanti hji)
  obtain ⟨p, hp⟩ := Erdos1172Part3TransfiniteHechlerClosure.full_countablyClosed hGCH
    C ⟨(chain 0).start, 0, rfl⟩ (Set.countable_range _) hC
  refine ⟨{
    start := p
    sources := fun n => (chain n).source
    names := fun n => (next n (chain n)).name
    follows := fun n => (next n (chain n)).follows
    future := fun n => (next n (chain n)).future
    points := ?_ }, hp (chain 0).start ⟨0, rfl⟩, rfl⟩
  intro n q hqp z x hx
  exact (next n (chain n)).points q
    (hqp.trans (hp (chain (n + 1)).start ⟨n + 1, rfl⟩)) z x hx

theorem exists_growing_tower (hGCH : GCH) (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (p0 : Full hGCH) : ∃ tower : GrowingTower hGCH G, tower.start ≤ p0 := by
  let initial : SourceState hGCH := {
    start := p0
    source := ground {a | IsOmegaOneSup a}
    sup := fun _ _ h => h
    locality := eventuallyLocal_ground (Earlier hGCH) (restriction hGCH) _
    stationary := by
      intro p _
      exact ErdosRadoCHAsym.isStationary_isOmegaOneSup_omegaTwo.mono (fun a ha => ⟨p, le_rfl, ha⟩) }
  obtain ⟨tower, htower, _⟩ := exists_growing_tower_from_source hGCH G H hcompl hred hblue initial
  exact ⟨tower, htower⟩

end Erdos1172Part3GrowingFiniteTower
