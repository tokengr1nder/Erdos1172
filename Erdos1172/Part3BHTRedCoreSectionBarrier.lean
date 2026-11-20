/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3BHTSecondMaximumGap

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3BHTRedCoreSectionBarrier

open Erdos1172Part3Failure
  Erdos1172Part3FiniteStars
  Erdos1172Part3OneSuccessorBarrier
  Erdos1172Part3OneSuccessorDeepMatrix
  Erdos1172Part3BHTSecondMaximumGap

/-- The part of a BHT fusion core which is red-compatible with a
prospective second maximum.  Requiring the whole fusion core here is
unnecessarily strong: retaining its exact order type already suffices. -/
def redCompatibleCoreSection
    (red : SimpleGraph W2)
    (fusion : BHTFinalFusionCore red) (secondMaximum : W2) : Set W2 :=
  {x | x ∈ fusion.core ∧ red.Adj x secondMaximum}

theorem redCompatibleCoreSection_sub_core
    {red : SimpleGraph W2}
    (fusion : BHTFinalFusionCore red) (secondMaximum : W2) :
    redCompatibleCoreSection red fusion secondMaximum ⊆ fusion.core := by
  intro x hx
  exact hx.1

theorem redCompatibleCoreSection_red
    {red : SimpleGraph W2}
    (fusion : BHTFinalFusionCore red) (secondMaximum : W2) :
    red.IsClique (redCompatibleCoreSection red fusion secondMaximum) :=
  fusion.core_red.subset
    (redCompatibleCoreSection_sub_core fusion secondMaximum)

theorem redCompatibleCoreSection_before_first
    {red : SimpleGraph W2}
    (fusion : BHTFinalFusionCore red) (secondMaximum : W2) :
    ∀ x ∈ redCompatibleCoreSection red fusion secondMaximum,
      x < fusion.firstMaximum := by
  intro x hx
  exact fusion.core_before_first x hx.1

theorem redCompatibleCoreSection_red_first
    {red : SimpleGraph W2}
    (fusion : BHTFinalFusionCore red) (secondMaximum : W2) :
    ∀ x ∈ redCompatibleCoreSection red fusion secondMaximum,
      red.Adj x fusion.firstMaximum := by
  intro x hx
  exact fusion.core_red_first x hx.1

theorem redCompatibleCoreSection_red_second
    {red : SimpleGraph W2}
    (fusion : BHTFinalFusionCore red) (secondMaximum : W2) :
    ∀ x ∈ redCompatibleCoreSection red fusion secondMaximum,
      red.Adj x secondMaximum := by
  intro x hx
  exact hx.2

/-- The ambient vertices represented by the complement of a candidate's
blue column inside the fusion core. -/
def blueCoreRedComplementVertices
    {red : SimpleGraph W2} (blue : SimpleGraph W2)
    (fusion : BHTFinalFusionCore red) (secondMaximum : W2) : Set W2 :=
  Subtype.val '' (blueColumn blue fusion.core secondMaximum)ᶜ

/-- Under global complementarity and the required ordering, the literal
complement of the blue defect column is exactly the red-compatible core
section.  This is the bridge from the existing cofinal-blue-column APIs
to the target-closing theorem below. -/
theorem blueCoreRedComplementVertices_eq_redCompatibleCoreSection
    {red blue : SimpleGraph W2} (hcompl : IsCompl red blue)
    (fusion : BHTFinalFusionCore red) (secondMaximum : W2)
    (hfirstBefore : fusion.firstMaximum < secondMaximum) :
    blueCoreRedComplementVertices blue fusion secondMaximum =
      redCompatibleCoreSection red fusion secondMaximum := by
  ext x
  constructor
  · rintro ⟨xCore, hxCore, rfl⟩
    have hnotBlue : ¬ blue.Adj (xCore : W2) secondMaximum := by
      simpa only [Set.mem_compl_iff, blueColumn,
        Set.mem_ofPred_eq] using hxCore
    have hxLt : (xCore : W2) < secondMaximum :=
      (fusion.core_before_first xCore xCore.property).trans hfirstBefore
    refine ⟨xCore.property, ?_⟩
    have hblueComplAdj : blueᶜ.Adj (xCore : W2) secondMaximum := by
      rw [SimpleGraph.compl_adj]
      exact ⟨hxLt.ne, hnotBlue⟩
    rw [hcompl.symm.compl_eq] at hblueComplAdj
    exact hblueComplAdj
  · intro hx
    let xCore : fusion.core := ⟨x, hx.1⟩
    refine ⟨xCore, ?_, rfl⟩
    have hnotBlue : ¬ blue.Adj (xCore : W2) secondMaximum := by
      intro hblue
      have hredComplAdj : redᶜ.Adj (xCore : W2) secondMaximum := by
        rw [hcompl.compl_eq]
        exact hblue
      rw [SimpleGraph.compl_adj] at hredComplAdj
      exact hredComplAdj.2 hx.2
    simpa only [Set.mem_compl_iff, blueColumn,
      Set.mem_ofPred_eq] using hnotBlue

/-- A full-type red-compatible *section* of the fusion core is enough
for the exact red target.  The first BHT maximum remains between the
selected core and the new point, so the construction has literal type
`RedCoreTarget + 2`; no absorption or cardinal-to-order shortcut occurs. -/
theorem BHTFinalFusionCore.hasCliqueOfType_redTarget_of_section
    {red : SimpleGraph W2}
    (fusion : BHTFinalFusionCore red) (secondMaximum : W2)
    (hfirstBefore : fusion.firstMaximum < secondMaximum)
    (hfirstRed : red.Adj fusion.firstMaximum secondMaximum)
    (hsection : RedCoreTarget ≤
      typeLT (redCompatibleCoreSection red fusion secondMaximum)) :
    OrdinalRamsey.HasCliqueOfType red RedTarget := by
  classical
  obtain ⟨exactCore, hexactCoreSub, hexactCoreType⟩ :=
    Ordinal.exists_subset_typeLT_eq
      (redCompatibleCoreSection red fusion secondMaximum) hsection
  have hexactCoreRed : red.IsClique exactCore :=
    (redCompatibleCoreSection_red fusion secondMaximum).subset
      hexactCoreSub
  have hexactCoreBeforeFirst :
      ∀ x ∈ exactCore, x < fusion.firstMaximum := by
    intro x hx
    exact redCompatibleCoreSection_before_first fusion secondMaximum
      x (hexactCoreSub hx)
  have hexactCoreRedFirst :
      ∀ x ∈ exactCore, red.Adj x fusion.firstMaximum := by
    intro x hx
    exact redCompatibleCoreSection_red_first fusion secondMaximum
      x (hexactCoreSub hx)
  let withFirst : Set W2 := Set.insert fusion.firstMaximum exactCore
  have hwithFirstRed : red.IsClique withFirst := by
    apply hexactCoreRed.insert
    intro x hx _
    rw [red.adj_comm]
    exact hexactCoreRedFirst x hx
  have hwithFirstType : typeLT withFirst = RedCoreTarget + 1 := by
    calc
      typeLT withFirst = typeLT exactCore + 1 :=
        Ordinal.typeLT_insert_of_forall_lt hexactCoreBeforeFirst
      _ = RedCoreTarget + 1 := by rw [hexactCoreType]
  have hwithFirstBeforeSecond :
      ∀ x ∈ withFirst, x < secondMaximum := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hfirstBefore
    · exact (hexactCoreBeforeFirst x hx).trans hfirstBefore
  have hwithFirstRedSecond :
      ∀ x ∈ withFirst, red.Adj x secondMaximum := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hfirstRed
    · exact redCompatibleCoreSection_red_second fusion secondMaximum
        x (hexactCoreSub hx)
  obtain ⟨target, htargetRed, htargetType⟩ :=
    red.exists_clique_type_add_one_of_common_later
      hwithFirstRed hwithFirstType hwithFirstBeforeSecond
        hwithFirstRedSecond
  refine ⟨target, htargetRed, ?_⟩
  calc
    typeLT target = (RedCoreTarget + 1) + 1 := htargetType
    _ = RedTarget := by
      norm_num [RedCoreTarget, RedTarget, add_assoc]

/-- Consequently, the actual BHT second-maximum gap is sharper than
failure of complete adjacency.  Outside the exact red target, every one
of its `alephTwo` candidates has a red-compatible core section strictly
shorter than `RedCoreTarget`, even though the complementary blue defect
is itself strictly cofinal and has cardinality `alephOne`. -/
theorem BHTSecondMaximumGap.redCompatibleCoreSection_type_lt
    {red blue : SimpleGraph W2}
    (gap : BHTSecondMaximumGap red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    {secondMaximum : W2} (hsecond : secondMaximum ∈ gap.candidates) :
    typeLT
        (redCompatibleCoreSection red gap.fusion secondMaximum) <
      RedCoreTarget := by
  by_contra hnot
  apply hnoRed
  exact BHTFinalFusionCore.hasCliqueOfType_redTarget_of_section
    gap.fusion secondMaximum
    (gap.first_before_candidates secondMaximum hsecond)
    (gap.first_red_candidates secondMaximum hsecond)
    (le_of_not_gt hnot)

/-- Equivalent blue-column form of the same sharp barrier.  Although
the blue defect is cofinal and has cardinality `alephOne`, its literal
complement inside the fused core cannot retain the full red-core order
type; otherwise the first maximum and this candidate close the target. -/
theorem BHTSecondMaximumGap.blueCoreRedComplementVertices_type_lt
    {red blue : SimpleGraph W2}
    (gap : BHTSecondMaximumGap red blue)
    (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    {secondMaximum : W2} (hsecond : secondMaximum ∈ gap.candidates) :
    typeLT
        (blueCoreRedComplementVertices blue gap.fusion secondMaximum) <
      RedCoreTarget := by
  rw [blueCoreRedComplementVertices_eq_redCompatibleCoreSection
    hcompl gap.fusion secondMaximum
      (gap.first_before_candidates secondMaximum hsecond)]
  exact BHTSecondMaximumGap.redCompatibleCoreSection_type_lt
    gap hnoRed hsecond

/-- The section barrier together with the pre-existing cofinal blue
column is the exact per-candidate normal form.  No synchronization
between different candidates is asserted. -/
structure BHTRedCoreSectionBarrier
    (red blue : SimpleGraph W2) : Type 1 where
  gap : BHTSecondMaximumGap red blue
  red_section_short : ∀ y ∈ gap.candidates,
    typeLT (redCompatibleCoreSection red gap.fusion y) < RedCoreTarget
  blue_section_strictlyCofinal : ∀ y ∈ gap.candidates,
    StrictlyCofinalBlueColumn blue gap.fusion.core y
  blue_section_card : ∀ y ∈ gap.candidates,
    #(blueColumn blue gap.fusion.core y) = ℵ_ 1

def BHTSecondMaximumGap.to_redCoreSectionBarrier
    {red blue : SimpleGraph W2}
    (gap : BHTSecondMaximumGap red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget) :
    BHTRedCoreSectionBarrier red blue := {
  gap := gap
  red_section_short :=
    fun _ hy ↦
      BHTSecondMaximumGap.redCompatibleCoreSection_type_lt
        gap hnoRed hy
  blue_section_strictlyCofinal := gap.blue_core_strictlyCofinal
  blue_section_card := gap.blue_core_card }

end Erdos1172Part3BHTRedCoreSectionBarrier
