/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedColorCore
public import Erdos1172.Part3IteratedHechlerCentering

@[expose] public section

/-!
# Red predecessor reflection for locally named sources

Two pressing-down steps freeze the source code and the smallness witness.
An omegaOne-valued center then makes the witnessing conditions compatible.
Their common strengthenings turn the stationary bad fiber into an actual
ground blue omegaTwo clique. No generic universe is used.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedRedReflection

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularNamedIdeal
open Erdos1172Part3NamedColorCore (colorFiber)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3RedPredecessorReflection (stationaryPressingDown)
open OrdinalRamsey (HasCliqueOfType)

variable {P I J : Type} [Preorder P] [LinearOrder I]

theorem exists_club_red_positive_family (center : CountablyCenteredCode P)
    {G : SimpleGraph W2} (r : Code P I G ↪ W2) (H : SimpleGraph W2)
    (hcompl : IsCompl G H) (hblue : ¬HasCliqueOfType H (ω_ 2))
    (t : J ↪ W2) (U : J → RegularName P W2) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, ∀ j : J, t j < a →
      ∀ p : P, (U j).holds p a →
        (neg (smallName r H a)).holds p (colorFiber G H (U j) a true) := by
  classical
  let bad : Set W2 := {a | ∃ j : J, t j < a ∧ ∃ p : P,
    (U j).holds p a ∧ (smallName r H a).holds p (colorFiber G H (U j) a true)}
  have witness (a : bad) : ∃ j : J, t j < a.val ∧ ∃ p : P,
      (U j).holds p a.val ∧ WitnessSmall r H a.val p (colorFiber G H (U j) a.val true) := by
    obtain ⟨j, hj, p, hp, hsmall⟩ := a.property
    obtain ⟨q, hqp, hq⟩ := hsmall p le_rfl
    exact ⟨j, hj, q, (U j).persistent hqp hp, hq⟩
  choose index hindex assigned hsource cover hcover hneg hsub using witness
  let indexRank (a : W2) : W2 := if ha : a ∈ bad then t (index ⟨a, ha⟩) else a
  let coverRank (a : W2) : W2 := if ha : a ∈ bad then r (cover ⟨a, ha⟩) else a
  have hnonstat : ¬IsStationary bad := by
    intro hbad
    obtain ⟨jvalue, hjstat⟩ := stationaryPressingDown bad indexRank hbad (by
      intro a ha
      simpa only [indexRank, dif_pos ha] using hindex ⟨a, ha⟩)
    let first : Set W2 := {a | a ∈ bad ∧ indexRank a = jvalue}
    obtain ⟨cvalue, hcstat⟩ := stationaryPressingDown first coverRank hjstat (by
      intro a ha
      simpa only [coverRank, dif_pos ha.1] using hcover ⟨a, ha.1⟩)
    let second : Set W2 := {a | a ∈ first ∧ coverRank a = cvalue}
    let centers (a : second) : W1 := center.code (assigned ⟨a.val, a.property.1.1⟩)
    have hsmall : #W1 < ℵ_ 2 := by
      simp only [W1, Cardinal.mk_toType, Ordinal.card_omega]
      exact Cardinal.aleph_lt_aleph.mpr (by norm_num)
    obtain ⟨zvalue, hzstat⟩ :=
      Erdos1172Part3CenteredStationaryLoss.exists_stationary_fiber_of_small hsmall hcstat centers
    let fiber : Set W2 := {a | ∃ ha : a ∈ second, centers ⟨a, ha⟩ = zvalue}
    have hclique : H.IsClique fiber := by
      rintro x ⟨hx, hxc⟩ y ⟨hy, hyc⟩ hxy
      let xb : bad := ⟨x, hx.1.1⟩
      let yb : bad := ⟨y, hy.1.1⟩
      have hi : index xb = index yb := by
        apply t.injective
        have hxj : t (index xb) = jvalue := by
          simpa only [indexRank, dif_pos hx.1.1] using hx.1.2
        have hyj : t (index yb) = jvalue := by
          simpa only [indexRank, dif_pos hy.1.1] using hy.1.2
        exact hxj.trans hyj.symm
      have hc : cover xb = cover yb := by
        apply r.injective
        have hxc' : r (cover xb) = cvalue := by
          simpa only [coverRank, dif_pos hx.1.1] using hx.2
        have hyc' : r (cover yb) = cvalue := by
          simpa only [coverRank, dif_pos hy.1.1] using hy.2
        exact hxc'.trans hyc'.symm
      have hcenter : center.code (assigned xb) = center.code (assigned yb) :=
        hxc.trans hyc.symm
      obtain ⟨q, hqx, hqy⟩ := center.common_lower hcenter
      rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
      refine ⟨hxy, ?_⟩
      intro hred
      rcases lt_or_gt_of_ne hxy with hlt | hgt
      · have hUx : (U (index yb)).holds q x := by
          rw [← hi]
          exact (U (index xb)).persistent hqx (hsource xb)
        have hmem := hsub yb x hlt q hqy ⟨hUx, hlt, hred⟩
        rw [← hc] at hmem
        exact hneg xb q hqx hmem
      · have hUy : (U (index xb)).holds q y := by
          rw [hi]
          exact (U (index yb)).persistent hqy (hsource yb)
        have hmem := hsub xb y hgt q hqx ⟨hUy, hgt, hred.symm⟩
        rw [hc] at hmem
        exact hneg yb q hqy hmem
    exact hblue ⟨fiber, hclique, Erdos1172Part3Failure.typeLT_eq_omegaTwo_of_mk_eq
      (Erdos1172Part3RedCoreIdeal.mk_eq_alephTwo_of_isCofinal
        (Erdos1172Part3TwoSuccessorBootstrap.isCofinal_of_stationary hzstat))⟩
  obtain ⟨club, hclub, hdisjoint⟩ := not_isStationary_iff.mp hnonstat
  refine ⟨club, hclub, ?_⟩
  intro a hac j hj p hp q hqp hq
  exact Set.disjoint_left.mp hdisjoint
    ⟨j, hj, q, (U j).persistent hqp hp, hq⟩ hac

theorem exists_club_red_positive_family_of_no_blue_target (center : CountablyCenteredCode P)
    {G : SimpleGraph W2} (r : Code P I G ↪ W2) (H : SimpleGraph W2)
    (hcompl : IsCompl G H) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (t : J ↪ W2) (U : J → RegularName P W2) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, ∀ j : J, t j < a →
      ∀ p : P, (U j).holds p a →
        (neg (smallName r H a)).holds p (colorFiber G H (U j) a true) := by
  apply exists_club_red_positive_family center r H hcompl _ t U
  rintro ⟨s, hs, ht⟩
  obtain ⟨v, hvs, hvt⟩ := Ordinal.exists_subset_typeLT_eq s
    (show (ω_ 1 : Ordinal.{0}) + 2 ≤ typeLT s by
      rw [ht]
      exact Erdos1172Part3RedCoreDerivedIdeal.blue_target_le_omegaTwo)
  exact hblue ⟨v, hs.subset hvs, hvt⟩

end Erdos1172Part3NamedRedReflection
