/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedStationaryRedLoss

@[expose] public section

/-!
# Stationary small losses give a completely red-joined tail

A stationary small-valued choice freezes one dense trace bound. The
remaining core has the same omegaOne index type. Its actual common-red
future is a regular name and remains stationary below one strengthening.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedRedTail

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularCliqueNeighborhoods (afterClique)
open Erdos1172Part3NamedTraceIdeal
open Erdos1172Part3ClosedDecisionSystem (CliqueDecisions)
open Erdos1172Part3StationaryDecisions (possible StationaryAt OmegaTwoCC exists_stationary_refinement)
open Erdos1172Part3StationarySquareDecisions (tail tail_strict lt_tail)

variable {P : Type} [Preorder P] {G : SimpleGraph W2}

/-- Centering is inherited by a condition cone, including the empty
countable subset case. -/
def centerOnCone (center : Erdos1172Part3IteratedHechlerCentering.CountablyCenteredCode P)
    (p0 : P) : Erdos1172Part3IteratedHechlerCentering.CountablyCenteredCode (Set.Iic p0) where
  code p := center.code p.val
  lower := by
    intro C hC value hvalue
    by_cases hne : C.Nonempty
    · obtain ⟨s, hs⟩ := hne
      obtain ⟨q, hq⟩ := center.lower (Subtype.val '' C) (hC.image Subtype.val) value (by
        rintro p ⟨t, ht, rfl⟩
        exact hvalue t ht)
      have hq0 : q ≤ p0 := (hq s.val ⟨s, hs, rfl⟩).trans s.property
      exact ⟨⟨q, hq0⟩, fun t ht => hq t.val ⟨t, ht, rfl⟩⟩
    · exact ⟨⟨p0, (show p0 ≤ p0 from le_rfl)⟩, fun t ht => (hne ⟨t, ht⟩).elim⟩

noncomputable def tailCore (core : CliqueDecisions P W1 W2 G) (bound : W1) :
    CliqueDecisions P W1 W2 G where
  decides p i x := core.decides p (tail bound i) x
  dense p i := core.dense p (tail bound i)
  persistent := core.persistent
  unique := core.unique
  ordered hij hi hj := core.ordered (tail_strict bound hij) hi hj
  adjacent hij hi hj := core.adjacent (fun h => hij ((tail_strict bound).injective h)) hi hj

theorem exists_stationary_red_tail (hcc : OmegaTwoCC P)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H) (core : CliqueDecisions P W1 W2 G)
    (future : RegularName P W2) (p0 : P)
    (hstat : IsStationary (possible future.holds p0))
    (hafter : ∀ p b, future.holds p b → ∀ i x, core.decides p i x → x < b)
    (hloss : ∀ p b, future.holds p b → (traceName core).holds p (ground {x | H.Adj x b})) :
    ∃ bound : W1, ∃ p : P, p ≤ p0 ∧
      StationaryAt (meet future (afterClique (tailCore core bound))).holds p := by
  classical
  let S := possible future.holds p0
  have witness (b : S) : ∃ bound : W1, ∃ p : P, p ≤ p0 ∧
      (meet future (afterClique (tailCore core bound))).holds p b.val := by
    obtain ⟨q, hqp0, hqb⟩ := b.property
    obtain ⟨p, hpq, bound, hp⟩ := hloss q b.val hqb q le_rfl
    have hpb := future.persistent hpq hqb
    refine ⟨bound, p, hpq.trans hqp0, hpb, ?_⟩
    intro s hsp i x hx
    have hxb := hafter s b.val (future.persistent hsp hpb) (tail bound i) x hx
    refine ⟨hxb, ?_⟩
    rw [← hcompl.symm.compl_eq, SimpleGraph.compl_adj]
    exact ⟨hxb.ne, hp s hsp (tail bound i) (lt_tail bound i) x hx⟩
  let chosen (b : S) : W1 := (witness b).choose
  have hsmall : #W1 < ℵ_ 2 := by
    simp only [W1, Cardinal.mk_toType, Ordinal.card_omega]
    exact Cardinal.aleph_lt_aleph.mpr (by norm_num)
  obtain ⟨bound, hbound⟩ := Erdos1172Part3CenteredStationaryLoss.exists_stationary_fiber_of_small
    hsmall hstat chosen
  let out := meet future (afterClique (tailCore core bound))
  have hout : IsStationary (possible out.holds p0) := by
    apply hbound.mono
    rintro b ⟨hb, heq⟩
    obtain ⟨p, hpp0, hp⟩ := (witness ⟨b, hb⟩).choose_spec
    have hval : (witness ⟨b, hb⟩).choose = bound := heq
    rw [hval] at hp
    exact ⟨p, hpp0, hp⟩
  obtain ⟨p, hpp0, hp⟩ := exists_stationary_refinement hcc out.holds
    (fun hqp h => out.persistent hqp h) p0 hout
  exact ⟨bound, p, hpp0, hp⟩

end Erdos1172Part3NamedRedTail
