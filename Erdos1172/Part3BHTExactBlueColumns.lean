/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.OrdinalUnaryIndivisibility

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3BHTExactBlueColumns

open Erdos1172Part3Failure
  Erdos1172Part3FiniteStars
  Erdos1172Part3OneSuccessorBarrier
  Erdos1172Part3OneSuccessorDeepMatrix
  Erdos1172Part3BHTSecondMaximumGap
  Erdos1172Part3BHTRedCoreSectionBarrier
  Erdos1172OrdinalUnaryIndivisibility

/-- `RedCoreTarget = omegaOne ^ (omega + 2)` is literally a nonzero
power of `omega`.  The exponent is left existential: only its
omega-power form, not a chosen logarithm of `omegaOne`, is used below. -/
theorem exists_redCoreTarget_eq_omega_opow :
    ∃ e : Ordinal, RedCoreTarget = ω ^ e := by
  have honePrincipal : IsPrincipal (· + ·) (omega 1) :=
    Ordinal.isPrincipal_add_omega 1
  rcases Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.mp
      honePrincipal with honeZero | ⟨e, he⟩
  · have honePos : (0 : Ordinal) < omega 1 :=
      Ordinal.omega0_pos.trans_le (Ordinal.omega0_le_omega 1)
    exact (honePos.ne' honeZero).elim
  · refine ⟨e * (ω + 2), ?_⟩
    rw [RedCoreTarget, ← he, Ordinal.opow_mul]

private theorem typeLT_val_image
    {S : Type} [LinearOrder S] [WellFoundedLT S] (t : Set S)
    (f : S → W2) (hf : StrictMono f) :
    typeLT (f '' t) = typeLT t := by
  have heq : typeLT t = typeLT (f '' t) :=
    ((hf.strictMonoOn t).orderIso f t).ordinalType_congr
  exact heq.symm

/-- The ambient image of a column has the same order type as the
column in the induced order on the fusion core. -/
theorem typeLT_blueColumnVertices
    {red : SimpleGraph W2} (blue : SimpleGraph W2)
    (fusion : BHTFinalFusionCore red) (y : W2) :
    typeLT (Subtype.val '' blueColumn blue fusion.core y) =
      typeLT (blueColumn blue fusion.core y) := by
  exact typeLT_val_image (blueColumn blue fusion.core y)
    Subtype.val (Subtype.strictMono_coe fusion.core)

/-- Outside the exact red target, every BHT candidate's complementary
blue column has the *full ordinal type* of the fused red core.  This is
stronger than its previously known cardinality `alephOne` and strict
cofinality. -/
theorem BHTRedCoreSectionBarrier.blueColumn_type
    {red blue : SimpleGraph W2}
    (barrier : BHTRedCoreSectionBarrier red blue)
    (hcompl : IsCompl red blue)
    {y : W2} (hy : y ∈ barrier.gap.candidates) :
    typeLT (blueColumn blue barrier.gap.fusion.core y) =
      RedCoreTarget := by
  obtain ⟨e, htarget⟩ := exists_redCoreTarget_eq_omega_opow
  have hcoreType : typeLT barrier.gap.fusion.core = ω ^ e :=
    barrier.gap.fusion.core_type.trans htarget
  obtain hblueFull | hredFull :=
    typeLT_eq_opow_or_compl_eq_opow
      (X := barrier.gap.fusion.core)
      (s := blueColumn blue barrier.gap.fusion.core y) hcoreType
  · exact hblueFull.trans htarget.symm
  · exfalso
    have himageType :
        typeLT (blueCoreRedComplementVertices blue
          barrier.gap.fusion y) = RedCoreTarget := by
      rw [blueCoreRedComplementVertices]
      exact (typeLT_val_image
        ((blueColumn blue barrier.gap.fusion.core y)ᶜ)
        Subtype.val
        (Subtype.strictMono_coe barrier.gap.fusion.core)).trans
          (hredFull.trans htarget.symm)
    have hshort := barrier.red_section_short y hy
    rw [← blueCoreRedComplementVertices_eq_redCompatibleCoreSection
      hcompl barrier.gap.fusion y
        (barrier.gap.first_before_candidates y hy)] at hshort
    rw [himageType] at hshort
    exact (lt_irrefl RedCoreTarget) hshort

/-- Ambient version: the full-type blue column is an exact red clique
lying before its candidate and blue-complete to it. -/
theorem BHTRedCoreSectionBarrier.exists_exactRedCore_blueTo_candidate
    {red blue : SimpleGraph W2}
    (barrier : BHTRedCoreSectionBarrier red blue)
    (hcompl : IsCompl red blue)
    {y : W2} (hy : y ∈ barrier.gap.candidates) :
    ∃ columnVertices : Set W2,
      red.IsClique columnVertices ∧
      typeLT columnVertices = RedCoreTarget ∧
      (∀ x ∈ columnVertices, x < y) ∧
      ∀ x ∈ columnVertices, blue.Adj x y := by
  let columnVertices : Set W2 :=
    Subtype.val '' blueColumn blue barrier.gap.fusion.core y
  refine ⟨columnVertices, ?_, ?_, ?_, ?_⟩
  · apply barrier.gap.fusion.core_red.subset
    rintro x ⟨xCore, _hxBlue, rfl⟩
    exact xCore.property
  · exact (typeLT_blueColumnVertices blue barrier.gap.fusion y).trans
      (Erdos1172Part3BHTExactBlueColumns.BHTRedCoreSectionBarrier.blueColumn_type
        barrier hcompl hy)
  · rintro x ⟨xCore, _hxBlue, rfl⟩
    exact (barrier.gap.fusion.core_before_first xCore xCore.property).trans
      (barrier.gap.first_before_candidates y hy)
  · rintro x ⟨xCore, hxBlue, rfl⟩
    exact hxBlue

end Erdos1172Part3BHTExactBlueColumns
