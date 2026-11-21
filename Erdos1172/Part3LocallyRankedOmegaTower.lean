/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3FiniteHistorySources

@[expose] public section

/-!
# A coherent locally ranked tower at one fixed cut

Each finite history has actual membership at the cut. The reflected
finite factories therefore supply another ranked witness below any
current condition. A countable lower bound preserves all containment
and common-future assertions. No stationary limit future is used.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3LocallyRankedOmegaTower

open ErdosRadoCHAsym (W2)
open Erdos1172Part3TransfiniteStageLocality (Full)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularCliqueNeighborhoods (afterClique containedIn cliqueFunction)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3FiniteTraceSchemes (Index)
open Erdos1172Part3FiniteHistorySources
open Erdos1172Part3CanonicalOmegaGluing (Blocks allJoined)

variable {hGCH : GCH} {G : SimpleGraph W2}

structure HistoryState (source : RegularName (Full hGCH) W2) (a : W2) where
  start : Full hGCH
  history : History hGCH G
  rank_lt : historyRank hGCH G history < a
  actual : (historySource source history).holds start a

structure HistoryStep (source : RegularName (Full hGCH) W2) (a : W2) (n : ℕ)
    (old : HistoryState (G := G) source a) where
  next : HistoryState (G := G) source a
  name : NiceCliqueName (Full hGCH) (Index n) W2 G
  below : next.start ≤ old.start
  history_eq : next.history = ⟨n, name⟩ :: old.history
  rank_lt : rankAt hGCH G n name < a
  geometry : ∀ p i x, name.toClique.decides p i x → x < a
  points : (containedIn (cliqueFunction name.toClique) (historySource source old.history)).holds next.start ()
  future : (afterClique name.toClique).holds next.start a

theorem exists_historyStep {source : RegularName (Full hGCH) W2} {a : W2}
    (hc : HistoryCut hGCH G source a) (n : ℕ) (old : HistoryState (G := G) source a) :
    Nonempty (HistoryStep source a n old) := by
  obtain ⟨q, hqp, N, hrank, hbelow, hpoints, hafter⟩ :=
    (hc.available n old.history old.rank_lt old.start old.actual) old.start le_rfl
  let next : HistoryState (G := G) source a := {
    start := q
    history := ⟨n, N⟩ :: old.history
    rank_lt := hc.cons_lt old.history ⟨n, N⟩ old.rank_lt hrank
    actual := ⟨(historySource source old.history).persistent hqp old.actual, hafter⟩ }
  exact ⟨⟨next, N, hqp, rfl, hrank, hbelow, hpoints, hafter⟩⟩

theorem HistoryStep.follows {source : RegularName (Full hGCH) W2} {a : W2} {n : ℕ}
    {old : HistoryState (G := G) source a} (step : HistoryStep source a n old)
    (p : Full hGCH) (x : W2) (hx : (historySource source step.next.history).holds p x) :
    (historySource source old.history).holds p x := by
  rw [step.history_eq] at hx
  exact hx.1

theorem HistoryStep.after_of_source {source : RegularName (Full hGCH) W2} {a : W2} {n : ℕ}
    {old : HistoryState (G := G) source a} (step : HistoryStep source a n old)
    (p : Full hGCH) (x : W2) (hx : (historySource source step.next.history).holds p x) :
    (afterClique step.name.toClique).holds p x := by
  rw [step.history_eq] at hx
  exact hx.2

structure RankedTower (source : RegularName (Full hGCH) W2) (a : W2) where
  start : Full hGCH
  names : Blocks (Full hGCH) G
  rank_lt : ∀ n, rankAt hGCH G n (names n) < a
  geometry : ∀ n p i x, (names n).toClique.decides p i x → x < a
  joined : (allJoined names).holds start ()
  points : ∀ n, (containedIn (cliqueFunction (names n).toClique) source).holds start ()
  future : ∀ n, (afterClique (names n).toClique).holds start a

theorem exists_ranked_tower {source : RegularName (Full hGCH) W2} {a : W2}
    (hc : HistoryCut hGCH G source a) (p0 : Full hGCH) (hp0 : source.holds p0 a) :
    ∃ tower : RankedTower (G := G) source a, tower.start ≤ p0 := by
  classical
  let initial : HistoryState (G := G) source a := ⟨p0, [], hc.empty_lt, hp0⟩
  let next (n : ℕ) (old : HistoryState (G := G) source a) : HistoryStep source a n old :=
    Classical.choice (exists_historyStep hc n old)
  let states : ℕ → HistoryState (G := G) source a :=
    fun n => Nat.rec initial (fun n old => (next n old).next) n
  let sources (n : ℕ) := historySource source (states n).history
  let names : Blocks (Full hGCH) G := fun n => (next n (states n)).name
  have hstep (n : ℕ) : (states (n + 1)).start ≤ (states n).start := (next n (states n)).below
  have hanti : Antitone (fun n => (states n).start) := antitone_nat_of_succ_le hstep
  have hsource_mono {m n : ℕ} (hmn : m ≤ n) :
      ∀ q x, (sources n).holds q x → (sources m).holds q x := by
    induction n, hmn using Nat.le_induction with
    | base => exact fun _ _ h => h
    | succ n hmn ih => exact fun q x h => ih q x ((next n (states n)).follows q x h)
  let C : Set (Full hGCH) := Set.range (fun n => (states n).start)
  have hC : IsChain (· ≤ ·) C := by
    rintro q ⟨i, rfl⟩ r ⟨j, rfl⟩ _
    rcases le_total i j with hij | hji
    · exact Or.inr (hanti hij)
    · exact Or.inl (hanti hji)
  obtain ⟨p, hp⟩ := Erdos1172Part3TransfiniteHechlerClosure.full_countablyClosed hGCH
    C ⟨(states 0).start, 0, rfl⟩ (Set.countable_range _) hC
  have hbelow (n : ℕ) : p ≤ (next n (states n)).next.start := hp (states (n + 1)).start ⟨n + 1, rfl⟩
  refine ⟨{
    start := p
    names := names
    rank_lt := fun n => (next n (states n)).rank_lt
    geometry := fun n => (next n (states n)).geometry
    joined := ?_
    points := ?_
    future := ?_ }, hp (states 0).start ⟨0, rfl⟩⟩
  · rintro ⟨⟨m, n⟩, hmn⟩ q hqp j y hy s hsq i x hx
    have hyn : (sources n).holds q y := (next n (states n)).points q (hqp.trans (hbelow n)) j y hy
    have hym : (sources (m + 1)).holds q y := hsource_mono (Nat.succ_le_of_lt hmn) q y hyn
    exact (next m (states m)).after_of_source q y hym s hsq i x hx
  · intro n q hqp i x hx
    exact historySource_base source (states n).history q x
      ((next n (states n)).points q (hqp.trans (hbelow n)) i x hx)
  · intro n
    exact (afterClique (names n).toClique).persistent (hbelow n) (next n (states n)).future

end Erdos1172Part3LocallyRankedOmegaTower
