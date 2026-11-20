/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3LocalOmegaReflection

@[expose] public section

/-!
# The omega+1 power core from local omega-core reflection

The proved local availability supports omegaOne many mutually joined
omega-power blocks. The lexicographic product has order type at least
omegaOne^(omega+1), so exact subset extraction gives the desired core.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3OmegaSuccessorCore

open ErdosRadoCHAsym (W1 W2 IsOmegaOneSup)
open Erdos1172Part3TransfiniteStageLocality (Full Earlier restriction)
open Erdos1172Part3TransfiniteHechlerOrder (mk_stage_le)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularStageLocality (EventuallyLocal eventuallyLocal_ground)
open Erdos1172Part3RegularNeighborhoodCode (rank blockRank)
open Erdos1172Part3RankedCoreBlockAssembly (GoodCoreCut mk_product_le)
open Erdos1172Part3ControlledCoreProducts (ProductData exists_guarded_source_product)
open Erdos1172Part3OmegaPowerIndex (OmegaIndex mk_omegaIndex_le omega_power_le_type)
open Erdos1172Part3LocalOmegaReflection (exists_club_goodOmegaCut)
open OrdinalRamsey (HasCliqueOfType)

abbrev OmegaSuccessor := W1 ×ₗ OmegaIndex

theorem mk_omegaSuccessor_le : #OmegaSuccessor ≤ ℵ_ 1 := mk_product_le mk_omegaIndex_le

theorem omega_successor_power_le_type : (ω_ 1 : Ordinal.{0}) ^ (ω + 1) ≤ typeLT OmegaSuccessor := by
  change (ω_ 1 : Ordinal.{0}) ^ (ω + 1) ≤ Ordinal.type
    (Prod.Lex ((· < ·) : W1 → W1 → Prop) ((· < ·) : OmegaIndex → OmegaIndex → Prop))
  rw [Ordinal.type_prod_lex, Ordinal.opow_add_one]
  change (ω_ 1 : Ordinal.{0}) ^ ω * (ω_ 1) ≤ (typeLT OmegaIndex) * (typeLT (ω_ 1).ToType)
  rw [Ordinal.type_toType]
  exact mul_le_mul' omega_power_le_type le_rfl

theorem exists_club_guarded_omega_successor (hGCH : GCH) (G H : SimpleGraph W2)
    (hcompl : IsCompl G H) (hred : ¬HasCliqueOfType G (ω_ 2))
    (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) (source : RegularName (Full hGCH) W2)
    (hsup : ∀ p a, source.holds p a → IsOmegaOneSup a)
    (hlocal : EventuallyLocal (Earlier hGCH) (restriction hGCH) source) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, IsOmegaOneSup a →
      GoodCoreCut (rank hGCH (mk_stage_le hGCH ⊤) mk_omegaIndex_le G)
        (blockRank hGCH (mk_stage_le hGCH ⊤) mk_omegaIndex_le G) H source a ∧
      ((∃ p : Full hGCH, source.holds p a) →
        Nonempty (ProductData (rank hGCH (mk_stage_le hGCH ⊤) mk_omegaIndex_le G) H source a)) := by
  obtain ⟨club, hclub, hc⟩ := exists_club_goodOmegaCut hGCH G H hcompl hred hblue source hsup hlocal
  exact ⟨club, hclub, fun a ha hsa => ⟨hc a ha hsa,
    exists_guarded_source_product (Erdos1172Part3TransfiniteHechlerClosure.full_countablyClosed hGCH)
      (Erdos1172Part3TransfiniteHechlerCentering.omegaTwoCC hGCH ⊤) mk_omegaIndex_le (hc a ha hsa)⟩⟩

theorem exists_ground_omega_successor (hGCH : GCH) (G H : SimpleGraph W2)
    (hcompl : IsCompl G H) (hred : ¬HasCliqueOfType G (ω_ 2))
    (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) :
    HasCliqueOfType G ((ω_ 1 : Ordinal.{0}) ^ (ω + 1)) := by
  let source : RegularName (Full hGCH) W2 := ground {a : W2 | IsOmegaOneSup a}
  obtain ⟨club, hclub, hc⟩ := exists_club_guarded_omega_successor hGCH G H hcompl hred hblue source
    (fun _ _ hp => hp) (eventuallyLocal_ground (Earlier hGCH) (restriction hGCH) _)
  obtain ⟨a, ha, hac⟩ := ErdosRadoCHAsym.isStationary_isOmegaOneSup_omegaTwo hclub
  let p0 : Full hGCH := default
  obtain ⟨data⟩ := (hc a hac ha).2 ⟨p0, ha⟩
  obtain ⟨C, hC, ht⟩ := data.name.toClique.exists_clique_type
    (Erdos1172Part3TransfiniteHechlerClosure.full_countablyClosed hGCH) p0 mk_omegaSuccessor_le
  obtain ⟨D, hDC, hDt⟩ := Ordinal.exists_subset_typeLT_eq C (omega_successor_power_le_type.trans_eq ht.symm)
  exact ⟨D, hC.subset hDC, hDt⟩

end Erdos1172Part3OmegaSuccessorCore
