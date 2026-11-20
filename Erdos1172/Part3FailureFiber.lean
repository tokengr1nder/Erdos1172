/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.SetTheory.Cardinal.Pigeonhole
public import Erdos1172.Part3Reduction
public import Erdos1172.ForMathlib.SetTheory.Ordinal.CliqueExtension
public import Erdos1172.ForMathlib.SetTheory.Ordinal.DushnikMillerCountable
public import Erdos1172.ForMathlib.SetTheory.Ordinal.PartitionRelationSubset

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3Failure

abbrev W2 : Type := (ω_ 2 : Ordinal.{0}).ToType

/-- A subset of `ω₂` of order type `ω₁ + 1` has a maximum. -/
theorem exists_max_of_type_omegaOne_add_one {s : Set W2}
    (hstype : typeLT s = ω_ 1 + 1) : ∃ m : s, IsMax m := by
  apply Ordinal.type_lt_mem_range_succ_iff.mp
  rw [hstype]
  exact ⟨(ω_ 1 : Ordinal.{0}), rfl⟩

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

/-- If a blue clique of type `ω₁ + 1` cannot be extended to type
`ω₁ + 2`, then above its maximum there is an `ℵ₂`-sized set of
vertices which all have a red edge to one fixed point of the blue clique. -/
theorem exists_large_red_failure_fiber
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {base : Set W2} (hbase : blue.IsClique base)
    (hbaseType : typeLT base = ω_ 1 + 1)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) :
    ∃ (m y : W2) (fiber : Set W2),
      m ∈ base ∧ y ∈ base ∧
      #fiber = ℵ_ 2 ∧ fiber ⊆ Set.Ioi m ∧
      ∀ x ∈ fiber, red.Adj y x := by
  classical
  obtain ⟨m, hm⟩ := exists_max_of_type_omegaOne_add_one hbaseType
  have hlater (x : Set.Ioi (m : W2)) : ∀ y ∈ base, y < (x : W2) := by
    intro y hy
    have hym : (⟨y, hy⟩ : base) ≤ m :=
      le_of_not_gt ((isMax_iff_forall_not_lt.mp hm) ⟨y, hy⟩)
    change y ≤ (m : W2) at hym
    have hmx : (m : W2) < x := x.property
    exact hym.trans_lt hmx
  have hwitness (x : Set.Ioi (m : W2)) : ∃ y : base, red.Adj y x := by
    by_contra hnone
    have hblueAdj : ∀ y ∈ base, blue.Adj y x := by
      intro y hy
      have hyx : y ≠ (x : W2) := (hlater x y hy).ne
      rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
      refine ⟨hyx, ?_⟩
      intro hred
      exact hnone ⟨⟨y, hy⟩, hred⟩
    have hext := blue.exists_clique_type_add_one_of_common_later
      hbase hbaseType (hlater x) hblueAdj
    apply hnoBlue
    obtain ⟨t, ht, httype⟩ := hext
    refine ⟨t, ht, ?_⟩
    calc
      typeLT t = (ω_ 1 + 1) + 1 := httype
      _ = ω_ 1 + 2 := by norm_num [add_assoc]
  let failure : Set.Ioi (m : W2) → base := fun x ↦ Classical.choose (hwitness x)
  have hfailure (x : Set.Ioi (m : W2)) : red.Adj (failure x) x :=
    Classical.choose_spec (hwitness x)
  have htailCard : #(Set.Ioi (m : W2)) = ℵ_ 2 := mk_Ioi_omegaTwo_eq m
  have hbaseCard : #base = ℵ_ 1 := by
    have hc := congrArg Ordinal.card hbaseType
    simpa only [Ordinal.card_type, Cardinal.card_omega_one_add_one] using hc
  obtain ⟨y, hyfiber⟩ := Cardinal.infinite_pigeonhole failure
    (by rw [htailCard]; exact Cardinal.aleph0_le_aleph 2)
    (by
      rw [hbaseCard, htailCard]
      rw [show (ℵ_ 2 : Cardinal.{0}) = ℵ_ ((1 : Ordinal.{0}) + 1) by norm_num,
        (Cardinal.isRegular_aleph_add_one 1).cof_ord]
      exact Cardinal.aleph_lt_aleph.mpr (by norm_num))
  let fiber : Set W2 := Subtype.val '' (failure ⁻¹' {y})
  refine ⟨m, y, fiber, m.property, y.property, ?_, ?_, ?_⟩
  · calc
      #fiber = #(failure ⁻¹' {y}) := Cardinal.mk_image_eq Subtype.val_injective
      _ = #(Set.Ioi (m : W2)) := hyfiber
      _ = ℵ_ 2 := htailCard
  · rintro x ⟨z, hz, rfl⟩
    exact z.property
  · rintro x ⟨z, hz, rfl⟩
    have hzy : failure z = y := by simpa only [mem_preimage, mem_singleton_iff] using hz
    simpa only [hzy] using hfailure z

/-- Strengthen the large failure fiber using the regular-cardinal
Erdős--Dushnik--Miller theorem. Either the fiber already contains the exact
red target from Part 3, or it contains a blue clique of type `ω + 1` all of
whose points are red-adjacent to one fixed point of the original blue clique. -/
theorem red_target_or_blue_omega_add_one_star
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {base : Set W2} (hbase : blue.IsClique base)
    (hbaseType : typeLT base = ω_ 1 + 1)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) :
    OrdinalRamsey.HasCliqueOfType red (ω_ 1 ^ (ω + 2) + 2) ∨
      ∃ (y : W2) (t : Set W2), y ∈ base ∧
        blue.IsClique t ∧ typeLT t = ω + 1 ∧
        ∀ x ∈ t, red.Adj y x := by
  obtain ⟨m, y, fiber, hm, hy, hcard, hfiberTail, hstar⟩ :=
    exists_large_red_failure_fiber red blue hcompl hbase hbaseType hnoBlue
  have hfiberType : typeLT fiber = ω_ 2 := typeLT_eq_omegaTwo_of_mk_eq hcard
  obtain ⟨t, htSub, htRed, htType⟩ | ⟨t, htSub, htBlue, htType⟩ :=
    OrdinalRamsey.on_set_of_type
      Ordinal.ordinalRamsey_omega_two_omega_two_omega_add_one
      red blue hcompl fiber hfiberType
  · left
    obtain ⟨z, hzSub, hzType⟩ := Ordinal.exists_subset_typeLT_eq t
      (part3_red_target_lt_omegaTwo.le.trans_eq htType.symm)
    exact ⟨z, htRed.subset hzSub, hzType⟩
  · right
    exact ⟨y, t, hy, htBlue, htType, fun x hx ↦ hstar x (htSub hx)⟩

end Erdos1172Part3Failure
