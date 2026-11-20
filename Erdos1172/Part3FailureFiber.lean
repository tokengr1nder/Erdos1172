/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part2Reduction
public import Erdos1172.ForMathlib.SetTheory.Ordinal.CliqueExtension
public import Erdos1172.ForMathlib.SetTheory.Ordinal.DushnikMillerCountable
public import Erdos1172.ForMathlib.SetTheory.Ordinal.PartitionRelationSubset

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3Failure

abbrev W2 : Type := (ω_ 2 : Ordinal.{0}).ToType

/-- Every tail above a point of the initial ordinal `ω₂` still has
cardinality `ℵ₂`. -/
theorem mk_Ioi_omegaTwo_eq (m : W2) : #(Set.Ioi m) = ℵ_ 2 := by
  letI : Infinite W2 := by
    rw [← Cardinal.aleph0_le_mk_iff]
    simp only [W2, Cardinal.mk_toType, Ordinal.card_omega]
    exact Cardinal.aleph0_le_aleph 2
  have hIic : #(Set.Iic m) < #W2 :=
    Cardinal.mk_Iic_lt m (by simp [W2]) (by
      simp only [W2, Cardinal.mk_toType, Ordinal.card_omega]
      exact Cardinal.aleph0_le_aleph 2)
  have hcompl := Cardinal.mk_compl_of_infinite (Set.Iic m) hIic
  simpa only [compl_Iic, W2, Cardinal.mk_toType, Ordinal.card_omega] using hcompl

/-- A subset of the initial ordinal `ω₂` with cardinality `ℵ₂` has
order type exactly `ω₂`. -/
theorem typeLT_eq_omegaTwo_of_mk_eq {s : Set W2} (hcard : #s = ℵ_ 2) :
    typeLT s = ω_ 2 := by
  apply le_antisymm
  · simpa only [W2, Ordinal.type_toType] using Ordinal.type_set_le s
  · simpa only [hcard, Cardinal.ord_aleph] using
      (Cardinal.ord_le_type ((· < ·) : s → s → Prop))

/-- The red target from Part 3 lies below the initial ordinal `ω₂`. -/
theorem part3_red_target_lt_omegaTwo :
    (ω_ 1 : Ordinal.{0}) ^ (ω + 2) + 2 < ω_ 2 := by
  have htwo : (2 : Ordinal.{0}) < ω_ 2 :=
    (Ordinal.natCast_lt_omega0 2).trans_le (Ordinal.omega0_le_omega 2)
  have homega : (ω : Ordinal.{0}) < ω_ 2 := by
    simpa only [Ordinal.omega_zero] using
      (Ordinal.omega_lt_omega.mpr (show (0 : Ordinal.{0}) < 2 by simp))
  have hexponent : (ω : Ordinal.{0}) + 2 < ω_ 2 :=
    Ordinal.isPrincipal_add_omega 2 homega htwo
  have hpower : (ω_ 1 : Ordinal.{0}) ^ (ω + 2) < ω_ 2 :=
    Ordinal.isPrincipal_opow_omega 2
      (Ordinal.omega_lt_omega.mpr one_lt_two) hexponent
  exact Ordinal.isPrincipal_add_omega 2 hpower htwo

end Erdos1172Part3Failure
