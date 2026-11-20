/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Variants
public import Erdos1172.Part3FullStationaryOmegaSuccessor
public import Erdos1172.Part3TwoSuccessorBootstrap

@[expose] public section

/-!
# The exact Part 3 partition relation under GCH

The constructed stationary omega-successor local-core factory reflects
to a club of ranked core cuts. A further whole-block product has exact
order type omegaOne^(omega+2), and countable-closure realization yields
the ground red core. The established two-successor bootstrap then gives
the two final red points in the original Part 3 statement.

The final theorem states the unchanged `Erdos1172.Part3` abbreviation
and has only GCH as a hypothesis.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3Solution

open ErdosRadoCHAsym (W1 W2 IsOmegaOneSup)
open Erdos1172Part3RegularMembership (RegularName ground)
open Erdos1172Part3TransfiniteStageLocality (Full Earlier restriction)
open Erdos1172Part3RegularStageLocality (eventuallyLocal_ground)
open Erdos1172Part3OmegaSuccessorCore (OmegaSuccessor mk_omegaSuccessor_le)
open Erdos1172Part3ExactOmegaIndex (typeLT_omegaSuccessor)
open Erdos1172Part3RankedCoreBlockAssembly (mk_product_le)
open Erdos1172Part3ControlledCoreProducts (exists_guarded_source_product)
open Erdos1172Part3FullRankedCoreReflection (exists_club_goodCoreCut)
open Erdos1172Part3FullStationaryOmegaSuccessor (omega_successor_factory)
open Erdos1172Part3TwoSuccessorBootstrap (part3_iff_core)
open OrdinalRamsey (HasCliqueOfType)

abbrev RedCoreIndex := W1 ×ₗ OmegaSuccessor

theorem mk_redCoreIndex_le : #RedCoreIndex ≤ ℵ_ 1 :=
  mk_product_le mk_omegaSuccessor_le

theorem typeLT_redCoreIndex : typeLT RedCoreIndex = (ω_ 1 : Ordinal.{0}) ^ (ω + 2) := by
  change Ordinal.type (Prod.Lex ((· < ·) : W1 → W1 → Prop)
    ((· < ·) : OmegaSuccessor → OmegaSuccessor → Prop)) = _
  rw [Ordinal.type_prod_lex]
  change (typeLT OmegaSuccessor) * (typeLT W1) = _
  rw [typeLT_omegaSuccessor, Ordinal.type_toType]
  simpa only [add_assoc, one_add_one_eq_two] using
    (Ordinal.opow_add_one (ω_ 1 : Ordinal.{0}) (ω + 1)).symm

theorem redCoreTarget_lt_omegaTwo : (ω_ 1 : Ordinal.{0}) ^ (ω + 2) < ω_ 2 :=
  lt_of_le_of_lt le_self_add Erdos1172.omega_one_opow_omega_add_two_add_two_lt_omega_two

/-- The new reflected factory supplies the original full red-core
exponent, not merely the omega-successor exponent. -/
theorem exists_ground_redCore (hGCH : GCH)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) :
    HasCliqueOfType G ((ω_ 1 : Ordinal.{0}) ^ (ω + 2)) := by
  let source : RegularName (Full hGCH) W2 := ground {a : W2 | IsOmegaOneSup a}
  obtain ⟨club, hclub, hgood⟩ := exists_club_goodCoreCut hGCH mk_omegaSuccessor_le G H
    (omega_successor_factory hGCH G H hcompl hred hblue) source
    (fun _ _ hp => hp) (eventuallyLocal_ground (Earlier hGCH) (restriction hGCH) _)
  obtain ⟨a, ha, hac⟩ := ErdosRadoCHAsym.isStationary_isOmegaOneSup_omegaTwo hclub
  let p0 : Full hGCH := default
  let hclosed := Erdos1172Part3TransfiniteHechlerClosure.full_countablyClosed hGCH
  obtain ⟨data⟩ := exists_guarded_source_product hclosed
    (Erdos1172Part3TransfiniteHechlerCentering.omegaTwoCC hGCH ⊤)
    mk_omegaSuccessor_le (hgood a hac ha) ⟨p0, ha⟩
  obtain ⟨C, hC, htype⟩ := data.name.toClique.exists_clique_type hclosed p0 mk_redCoreIndex_le
  exact ⟨C, hC, htype.trans typeLT_redCoreIndex⟩

theorem ordinalRamsey_redCoreTarget (hGCH : GCH) :
    OrdinalRamsey (ω_ 2 : Ordinal.{0}) ((ω_ 1) ^ (ω + 2)) (ω_ 1 + 2) := by
  classical
  intro G H hcompl
  by_cases hblue : HasCliqueOfType H (ω_ 1 + 2)
  · exact Or.inr hblue
  by_cases hred : HasCliqueOfType G (ω_ 2)
  · obtain ⟨C, hC, htype⟩ := hred
    obtain ⟨D, hDC, hDtype⟩ := Ordinal.exists_subset_typeLT_eq C
      (show (ω_ 1 : Ordinal.{0}) ^ (ω + 2) ≤ typeLT C by
        rw [htype]
        exact redCoreTarget_lt_omegaTwo.le)
    exact Or.inl ⟨D, hC.subset hDC, hDtype⟩
  · exact Or.inl (exists_ground_redCore hGCH G H hcompl hred hblue)

/-- The original exact Part 3 of Erdős Problem 1172, under GCH. -/
theorem part3_of_gch (hGCH : GCH) : Erdos1172.Part3.{0} :=
  (part3_iff_core hGCH).mpr (ordinalRamsey_redCoreTarget hGCH)

end Erdos1172Part3Solution
