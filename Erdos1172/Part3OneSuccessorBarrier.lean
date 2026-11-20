/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3OmegaOneNeighborDeepBlue

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3OneSuccessorBarrier

open Erdos1172Part3Failure Erdos1172Part3FiniteStars
  Erdos1172Part3CHAsymmetric
  Erdos1172Part3OmegaOneRectangleRefinement
  Erdos1172Part3OmegaOneNeighborProfiles
  Erdos1172Part3OmegaOneNeighborUltrametric
  Erdos1172Part3OmegaOneNeighborDeepBlue

/-- The limit part of the red target in Part 3. -/
noncomputable abbrev RedCoreTarget : Ordinal :=
  (ω_ 1 : Ordinal.{0}) ^ (ω + 2)

/-- The BHT-style red target, exactly one successor short of Part 3. -/
noncomputable abbrev RedNearTarget : Ordinal :=
  RedCoreTarget + 1

/-- The one-successor-short red target still has cardinality `alephOne`. -/
theorem card_redNearTarget : RedNearTarget.card = ℵ_ 1 := by
  have hExp : (ω + 2 : Ordinal.{0}).card = ℵ₀ := by
    rw [Ordinal.card_add, Ordinal.card_omega0, Ordinal.card_ofNat,
      Cardinal.add_eq_left]
    · exact le_rfl
    · exact Cardinal.natCast_le_aleph0
  have hPow : ((ω_ 1 : Ordinal.{0}) ^ (ω + 2)).card = ℵ_ 1 := by
    rw [Ordinal.card_opow_eq_of_omega0_le_left, Ordinal.card_omega, hExp,
      max_eq_left (Cardinal.aleph0_le_aleph 1)]
    · exact Ordinal.omega0_le_omega 1
    · exact Ordinal.omega0_pos.trans_le (by simp)
  rw [RedNearTarget, RedCoreTarget, Ordinal.card_add, hPow,
    Ordinal.card_one, Cardinal.add_eq_left]
  · exact Cardinal.aleph0_le_aleph 1
  · exact Cardinal.one_le_aleph0.trans (Cardinal.aleph0_le_aleph 1)

/-- A clique of type `RedNearTarget` has a terminal point. -/
theorem exists_max_of_type_redNearTarget {s : Set W2}
    (hstype : typeLT s = RedNearTarget) :
    ∃ m : s, IsMax m := by
  apply Ordinal.type_lt_mem_range_succ_iff.mp
  rw [hstype]
  exact ⟨RedCoreTarget, rfl⟩

/-- A fixed point lying *before* a blue `omegaOne + 1` clique does not
produce the missing second successor: finite initial prefixes are absorbed
by `omegaOne`.  This is the ordinal-arithmetic reason that the failure fan
below is a genuine obstruction rather than an immediate blue solution. -/
theorem one_add_omegaOne_add_one_eq :
    (1 : Ordinal.{0}) + (ω_ 1 + 1) = ω_ 1 + 1 := by
  rw [← add_assoc, Ordinal.one_add_of_omega0_le
    (Ordinal.omega0_le_omega 1)]

/-- The canonical obstruction to adding the final red successor.

The red near-target has a maximum.  Every point above that maximum has a
blue edge back into the near-target, and one such failure coordinate is
constant on an `alephTwo`-sized tail fiber.  Under CH that fiber contains a
blue `omegaOne + 1` arm.  Its fixed blue centre lies before the arm, so the
preceding absorption identity explains why this is still one point short
of the exact blue target. -/
def NearRedOneSuccessorFailureFan
    (red blue : SimpleGraph W2) : Prop :=
  ∃ (base : Set W2) (maximum center : W2)
      (failureFiber arm : Set W2),
    red.IsClique base ∧ typeLT base = RedNearTarget ∧
    maximum ∈ base ∧ (∀ x ∈ base, x ≤ maximum) ∧
    center ∈ base ∧
    (∀ y : W2, maximum < y → ∃ x ∈ base, blue.Adj x y) ∧
    #failureFiber = ℵ_ 2 ∧ failureFiber ⊆ Set.Ioi maximum ∧
    (∀ y ∈ failureFiber, blue.Adj center y) ∧
    arm ⊆ failureFiber ∧ blue.IsClique arm ∧
    typeLT arm = ω_ 1 + 1

/-- Failure to extend a given red BHT-style near-target to the exact red
target produces the canonical large fixed-coordinate failure fan.  No
hypothesis excluding the exact blue target is needed for this extraction. -/
theorem NearRedOneSuccessorFailureFan.of_nearClique_of_no_red_target
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {base : Set W2} (hbaseRed : red.IsClique base)
    (hbaseType : typeLT base = RedNearTarget)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget) :
    NearRedOneSuccessorFailureFan red blue := by
  classical
  obtain ⟨maximum, hmaximum⟩ := exists_max_of_type_redNearTarget hbaseType
  have hmaximumMem : (maximum : W2) ∈ base := maximum.property
  have hbaseBefore (y : Set.Ioi (maximum : W2)) :
      ∀ x ∈ base, x < (y : W2) := by
    intro x hx
    have hxmax : (⟨x, hx⟩ : base) ≤ maximum :=
      le_of_not_gt ((isMax_iff_forall_not_lt.mp hmaximum) ⟨x, hx⟩)
    change x ≤ (maximum : W2) at hxmax
    exact hxmax.trans_lt y.property
  have hwitness (y : Set.Ioi (maximum : W2)) :
      ∃ x : base, blue.Adj x y := by
    by_contra hnone
    have hredAdj : ∀ x ∈ base, red.Adj x y := by
      intro x hx
      rw [← hcompl.symm.compl_eq, SimpleGraph.compl_adj]
      refine ⟨(hbaseBefore y x hx).ne, ?_⟩
      intro hblue
      exact hnone ⟨⟨x, hx⟩, hblue⟩
    obtain ⟨target, htargetRed, htargetType⟩ :=
      red.exists_clique_type_add_one_of_common_later
        hbaseRed hbaseType (hbaseBefore y) hredAdj
    apply hnoRed
    refine ⟨target, htargetRed, ?_⟩
    calc
      typeLT target = RedNearTarget + 1 := htargetType
      _ = RedTarget := by
        norm_num [RedNearTarget, RedCoreTarget, RedTarget, add_assoc]
  let failure : Set.Ioi (maximum : W2) → base :=
    fun y ↦ Classical.choose (hwitness y)
  have hfailure (y : Set.Ioi (maximum : W2)) :
      blue.Adj (failure y) y :=
    Classical.choose_spec (hwitness y)
  have htailCard : #(Set.Ioi (maximum : W2)) = ℵ_ 2 :=
    mk_Ioi_omegaTwo_eq maximum
  have hbaseCard : #base = ℵ_ 1 := by
    have hc := congrArg Ordinal.card hbaseType
    simpa only [Ordinal.card_type, card_redNearTarget] using hc
  obtain ⟨center, hlargeFiber⟩ := Cardinal.infinite_pigeonhole failure
    (by rw [htailCard]; exact Cardinal.aleph0_le_aleph 2)
    (by
      rw [hbaseCard, htailCard]
      rw [show (ℵ_ 2 : Cardinal.{0}) =
          ℵ_ ((1 : Ordinal.{0}) + 1) by norm_num,
        (Cardinal.isRegular_aleph_add_one 1).cof_ord]
      exact Cardinal.aleph_lt_aleph.mpr (by norm_num))
  let failureFiber : Set W2 :=
    Subtype.val '' (failure ⁻¹' {center})
  have hfailureFiberCard : #failureFiber = ℵ_ 2 := by
    calc
      #failureFiber = #(failure ⁻¹' {center}) :=
        Cardinal.mk_image_eq Subtype.val_injective
      _ = #(Set.Ioi (maximum : W2)) := hlargeFiber
      _ = ℵ_ 2 := htailCard
  have hfailureFiberTail : failureFiber ⊆ Set.Ioi maximum := by
    rintro y ⟨z, _hz, rfl⟩
    exact z.property
  have hcenterBlue : ∀ y ∈ failureFiber, blue.Adj center y := by
    rintro y ⟨z, hz, rfl⟩
    have hzc : failure z = center := by
      simpa only [mem_preimage, mem_singleton_iff] using hz
    simpa only [hzc] using hfailure z
  obtain ⟨arm, harmSub, harmBlue, harmType⟩ :=
    exists_blue_omegaOne_add_one_in_every_alephTwo_set
      hCH red blue hcompl hnoRed hfailureFiberCard
  refine ⟨base, maximum, center, failureFiber, arm,
    hbaseRed, hbaseType, hmaximumMem, ?_, center.property, ?_,
    hfailureFiberCard, hfailureFiberTail, hcenterBlue,
    harmSub, harmBlue, harmType⟩
  · intro x hx
    exact show (⟨x, hx⟩ : base) ≤ maximum from
      le_of_not_gt ((isMax_iff_forall_not_lt.mp hmaximum) ⟨x, hx⟩)
  · intro y hy
    let z : Set.Ioi (maximum : W2) := ⟨y, hy⟩
    exact ⟨failure z, (failure z).property, hfailure z⟩

/-- The BHT-style relation needed here: the blue target is already exact,
while the red target is short by one final successor. -/
def BHTNearPart3Relation : Prop :=
  OrdinalRamsey (ω_ 2 : Ordinal.{0}) RedNearTarget (ω_ 1 + 2)

/-- The full one-step obstruction obtained by reapplying the BHT near
relation inside the fixed failure fiber.  The same ordered `alephTwo`
fiber contains both a blue `omegaOne + 1` arm and a red near-target arm;
one point of the first red near-target is blue-adjacent to every point of
both arms. -/
def NearRedOneSuccessorDoubleFan
    (red blue : SimpleGraph W2) : Prop :=
  ∃ (base : Set W2) (maximum center : W2)
      (failureFiber blueArm redArm : Set W2),
    red.IsClique base ∧ typeLT base = RedNearTarget ∧
    maximum ∈ base ∧ (∀ x ∈ base, x ≤ maximum) ∧
    center ∈ base ∧
    (∀ y : W2, maximum < y → ∃ x ∈ base, blue.Adj x y) ∧
    #failureFiber = ℵ_ 2 ∧ failureFiber ⊆ Set.Ioi maximum ∧
    (∀ y ∈ failureFiber, blue.Adj center y) ∧
    blueArm ⊆ failureFiber ∧ blue.IsClique blueArm ∧
    typeLT blueArm = ω_ 1 + 1 ∧
    redArm ⊆ failureFiber ∧ red.IsClique redArm ∧
    typeLT redArm = RedNearTarget

/-- In a counterexample to both exact targets, reapplying the BHT near
relation to the large fixed-coordinate fiber necessarily takes its red
branch.  Thus the one-successor failure fan simultaneously contains a
second, strictly later red near-target. -/
theorem NearRedOneSuccessorDoubleFan.of_nearClique_of_no_targets
    (hCH : CH) (hBHT : BHTNearPart3Relation)
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {base : Set W2} (hbaseRed : red.IsClique base)
    (hbaseType : typeLT base = RedNearTarget)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) :
    NearRedOneSuccessorDoubleFan red blue := by
  obtain ⟨base, maximum, center, failureFiber, blueArm,
      hbaseRed, hbaseType, hmaximumMem, hmaximum,
      hcenterMem, hallTailFailure, hfailureFiberCard,
      hfailureFiberTail, hcenterBlue, hblueArmSub,
      hblueArm, hblueArmType⟩ :=
    NearRedOneSuccessorFailureFan.of_nearClique_of_no_red_target
      hCH red blue hcompl hbaseRed hbaseType hnoRed
  have hfailureFiberType : typeLT failureFiber = ω_ 2 :=
    typeLT_eq_omegaTwo_of_mk_eq hfailureFiberCard
  obtain ⟨redArm, hredArmSub, hredArm, hredArmType⟩ |
      ⟨blueTarget, _hblueTargetSub, hblueTarget, hblueTargetType⟩ :=
    OrdinalRamsey.on_set_of_type hBHT red blue hcompl
      failureFiber hfailureFiberType
  · exact ⟨base, maximum, center, failureFiber, blueArm, redArm,
      hbaseRed, hbaseType, hmaximumMem, hmaximum,
      hcenterMem, hallTailFailure, hfailureFiberCard,
      hfailureFiberTail, hcenterBlue, hblueArmSub,
      hblueArm, hblueArmType, hredArmSub, hredArm, hredArmType⟩
  · exact (hnoBlue ⟨blueTarget, hblueTarget, hblueTargetType⟩).elim

/-- Once the BHT-style near relation is available, Part 3 is equivalent
to one precise obligation: every red near-target clique must extend to one
of the two exact targets.  The blue outcome of the near relation is already
the exact blue target. -/
theorem part3_iff_extend_every_redNearTarget (hBHT : BHTNearPart3Relation) :
    OrdinalRamsey (ω_ 2 : Ordinal.{0}) RedTarget (ω_ 1 + 2) ↔
      ∀ red blue : SimpleGraph W2, IsCompl red blue →
        OrdinalRamsey.HasCliqueOfType red RedNearTarget →
          OrdinalRamsey.HasCliqueOfType red RedTarget ∨
            OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2) := by
  constructor
  · intro hexact red blue hcompl _hnear
    exact hexact red blue hcompl
  · intro hext red blue hcompl
    obtain hnear | hblue := hBHT red blue hcompl
    · exact hext red blue hcompl hnear
    · exact Or.inr hblue

/-- Assuming the known BHT-style near relation, the exact Part 3 statement
reduces to the explicit one-successor failure fan above. -/
theorem part3_exact_or_nearRedOneSuccessorFailureFan
    (hCH : CH) (hBHT : BHTNearPart3Relation)
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      NearRedOneSuccessorFailureFan red blue := by
  classical
  by_cases htarget :
      OrdinalRamsey.HasCliqueOfType red RedTarget ∨
        OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)
  · exact Or.inl htarget
  · right
    have hnone := not_or.mp htarget
    obtain ⟨base, hbaseRed, hbaseType⟩ |
        ⟨base, hbaseBlue, hbaseType⟩ := hBHT red blue hcompl
    · exact NearRedOneSuccessorFailureFan.of_nearClique_of_no_red_target
        hCH red blue hcompl hbaseRed hbaseType hnone.1
    · exact (hnone.2 ⟨base, hbaseBlue, hbaseType⟩).elim

/-- BHT-strengthened exact normal form: outside the exact targets, the
one-successor obstruction contains both the CH blue arm and a second
strictly later BHT red near-target in the same fixed failure fiber. -/
theorem part3_exact_or_nearRedOneSuccessorDoubleFan
    (hCH : CH) (hBHT : BHTNearPart3Relation)
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      NearRedOneSuccessorDoubleFan red blue := by
  classical
  by_cases htarget :
      OrdinalRamsey.HasCliqueOfType red RedTarget ∨
        OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)
  · exact Or.inl htarget
  · right
    have hnone := not_or.mp htarget
    obtain ⟨base, hbaseRed, hbaseType⟩ |
        ⟨base, hbaseBlue, hbaseType⟩ := hBHT red blue hcompl
    · exact NearRedOneSuccessorDoubleFan.of_nearClique_of_no_targets
        hCH hBHT red blue hcompl hbaseRed hbaseType hnone.1 hnone.2
    · exact (hnone.2 ⟨base, hbaseBlue, hbaseType⟩).elim

/-- Combined sharp normal form.  Outside the exact targets, the same
coloring simultaneously carries the one-successor BHT failure fan and
either the ordered blue rectangle or the graph-synchronised deep-blue
neighbourhood ultrametric obstruction. -/
theorem part3_exact_or_oneSuccessorAndDeepBlueObstruction
    (hCH : CH) (hBHT : BHTNearPart3Relation)
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      (NearRedOneSuccessorFailureFan red blue ∧
        (OrderedBlueOmegaOneByOmegaOneAddOneRedRectangle red blue ∨
          (LocallyCompactUltrametricOmegaOneBaseNeighborhoodResidualWithFan
              red blue ∧
            DeepBlueOmegaOneAddOneNeighborhoodUltrametricObstruction
              red blue))) := by
  classical
  obtain hexact | hfailure :=
    part3_exact_or_nearRedOneSuccessorFailureFan
      hCH hBHT red blue hcompl
  · exact Or.inl hexact
  · obtain hexact | hrectangle | hdeep :=
      part3_exact_or_orderedBlueRectangle_or_deepBlueNeighborhoodUltrametric
        hCH red blue hcompl
    · exact Or.inl hexact
    · exact Or.inr ⟨hfailure, Or.inl hrectangle⟩
    · exact Or.inr ⟨hfailure, Or.inr hdeep⟩

/-- Strongest combined normal form in this module.  The near-target
one-successor obstruction is closed under one further BHT step, and the
independent stationary/deep-blue obstruction is retained for the very same
coloring. -/
theorem part3_exact_or_doubleFanAndDeepBlueObstruction
    (hCH : CH) (hBHT : BHTNearPart3Relation)
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      (NearRedOneSuccessorDoubleFan red blue ∧
        (OrderedBlueOmegaOneByOmegaOneAddOneRedRectangle red blue ∨
          (LocallyCompactUltrametricOmegaOneBaseNeighborhoodResidualWithFan
              red blue ∧
            DeepBlueOmegaOneAddOneNeighborhoodUltrametricObstruction
              red blue))) := by
  classical
  obtain hexact | hdouble :=
    part3_exact_or_nearRedOneSuccessorDoubleFan
      hCH hBHT red blue hcompl
  · exact Or.inl hexact
  · obtain hexact | hrectangle | hdeep :=
      part3_exact_or_orderedBlueRectangle_or_deepBlueNeighborhoodUltrametric
        hCH red blue hcompl
    · exact Or.inl hexact
    · exact Or.inr ⟨hdouble, Or.inl hrectangle⟩
    · exact Or.inr ⟨hdouble, Or.inr hdeep⟩

end Erdos1172Part3OneSuccessorBarrier
