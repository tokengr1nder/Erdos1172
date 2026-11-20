/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3BHTExactBlueColumns

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3BHTFiniteCommonBlueColumns

open Erdos1172Part3Failure
  Erdos1172Part3FiniteStars
  Erdos1172Part3OneSuccessorBarrier
  Erdos1172Part3OneSuccessorDeepMatrix
  Erdos1172Part3BHTSecondMaximumGap
  Erdos1172Part3BHTRedCoreSectionBarrier
  Erdos1172Part3BHTExactBlueColumns
  Erdos1172OrdinalUnaryIndivisibility

private theorem typeLT_image_eq
    {S X : Type} [LinearOrder S] [WellFoundedLT S]
    [LinearOrder X] [WellFoundedLT X]
    (t : Set S) (f : S → X) (hf : StrictMono f) :
    typeLT (f '' t) = typeLT t := by
  have heq : typeLT t = typeLT (f '' t) :=
    ((hf.strictMonoOn t).orderIso f t).ordinalType_congr
  exact heq.symm

/-- The type of an arbitrary union is bounded by the natural sum of the
types of its two pieces.  Unlike ordinary ordinal addition, this bound
is valid when the pieces are interleaved. -/
theorem typeLT_union_le_naturalSum
    {X : Type} [LinearOrder X] [WellFoundedLT X]
    (s t : Set X) :
    typeLT (s ∪ t : Set X) ≤ naturalSum (typeLT s) (typeLT t) := by
  let united : Set X := s ∪ t
  let left : Set united := {x | (x : X) ∈ s}
  have hleftImage : Subtype.val '' left = s := by
    ext x
    constructor
    · rintro ⟨xUnited, hxLeft, rfl⟩
      exact hxLeft
    · intro hx
      let xUnited : united := ⟨x, Or.inl hx⟩
      exact ⟨xUnited, hx, rfl⟩
  have hleftType : typeLT left = typeLT s := by
    rw [← hleftImage]
    exact (typeLT_image_eq left Subtype.val
      (Subtype.strictMono_coe united)).symm
  have hrightImageSub :
      Subtype.val '' (leftᶜ : Set united) ⊆ t := by
    rintro x ⟨xUnited, hxNotLeft, rfl⟩
    have hxUnited : (xUnited : X) ∈ (s ∪ t : Set X) :=
      xUnited.property
    rcases hxUnited with hxS | hxT
    · exact (hxNotLeft hxS).elim
    · exact hxT
  have hrightLe : typeLT (leftᶜ : Set united) ≤ typeLT t := by
    have himageType :
        typeLT (Subtype.val '' (leftᶜ : Set united)) =
          typeLT (leftᶜ : Set united) :=
      typeLT_image_eq (leftᶜ : Set united) Subtype.val
        (Subtype.strictMono_coe united)
    rw [← himageType]
    exact Ordinal.type_mono hrightImageSub
  have hpartition :=
    typeLT_le_naturalSum_partition (X := united) left
  rw [hleftType] at hpartition
  have hnatural :=
    (naturalSum_strictMono_right (typeLT s)).monotone hrightLe
  exact hpartition.trans hnatural

theorem typeLT_union_lt_opow
    {X : Type} [LinearOrder X] [WellFoundedLT X]
    {s t : Set X} {e : Ordinal}
    (hs : typeLT s < ω ^ e) (ht : typeLT t < ω ^ e) :
    typeLT (s ∪ t : Set X) < ω ^ e :=
  (typeLT_union_le_naturalSum s t).trans_lt
    (naturalSum_lt_opow hs ht)

/-- The common blue predecessor column for a finite list of candidates.
The empty list gives the whole fusion core. -/
def finiteCommonBlueColumn
    {red : SimpleGraph W2} (blue : SimpleGraph W2)
    (fusion : BHTFinalFusionCore red) : List W2 → Set fusion.core
  | [] => Set.univ
  | y :: ys => blueColumn blue fusion.core y ∩
      finiteCommonBlueColumn blue fusion ys

@[simp] theorem finiteCommonBlueColumn_nil
    {red : SimpleGraph W2} (blue : SimpleGraph W2)
    (fusion : BHTFinalFusionCore red) :
    finiteCommonBlueColumn blue fusion [] = Set.univ := rfl

@[simp] theorem finiteCommonBlueColumn_cons
    {red : SimpleGraph W2} (blue : SimpleGraph W2)
    (fusion : BHTFinalFusionCore red) (y : W2) (ys : List W2) :
    finiteCommonBlueColumn blue fusion (y :: ys) =
      blueColumn blue fusion.core y ∩
        finiteCommonBlueColumn blue fusion ys := rfl

/-- Each literal column complement is short inside the induced fusion
core order. -/
theorem BHTRedCoreSectionBarrier.blueColumn_compl_type_lt
    {red blue : SimpleGraph W2}
    (barrier : BHTRedCoreSectionBarrier red blue)
    (hcompl : IsCompl red blue)
    {y : W2} (hy : y ∈ barrier.gap.candidates) :
    typeLT ((blueColumn blue barrier.gap.fusion.core y)ᶜ :
      Set barrier.gap.fusion.core) <
      RedCoreTarget := by
  have himageType :
      typeLT (Subtype.val ''
          ((blueColumn blue barrier.gap.fusion.core y)ᶜ :
            Set barrier.gap.fusion.core)) =
        typeLT ((blueColumn blue barrier.gap.fusion.core y)ᶜ :
          Set barrier.gap.fusion.core) :=
    typeLT_image_eq _ Subtype.val
      (Subtype.strictMono_coe barrier.gap.fusion.core)
  have himageShort :
      typeLT (Subtype.val ''
          ((blueColumn blue barrier.gap.fusion.core y)ᶜ :
            Set barrier.gap.fusion.core)) <
        RedCoreTarget := by
    change typeLT (blueCoreRedComplementVertices blue
      barrier.gap.fusion y) < RedCoreTarget
    rw [blueCoreRedComplementVertices_eq_redCompatibleCoreSection
      hcompl barrier.gap.fusion y
        (barrier.gap.first_before_candidates y hy)]
    exact barrier.red_section_short y hy
  rwa [himageType] at himageShort

private theorem finiteCommonBlueColumn_compl_type_lt
    {red blue : SimpleGraph W2}
    (barrier : BHTRedCoreSectionBarrier red blue)
    (hcompl : IsCompl red blue)
    (ys : List W2)
    (hys : ∀ y ∈ ys, y ∈ barrier.gap.candidates) :
    typeLT ((finiteCommonBlueColumn blue barrier.gap.fusion ys)ᶜ :
      Set barrier.gap.fusion.core) <
      RedCoreTarget := by
  obtain ⟨e, htarget⟩ := exists_redCoreTarget_eq_omega_opow
  rw [htarget]
  induction ys with
  | nil =>
      change typeLT (Set.univᶜ : Set barrier.gap.fusion.core) < ω ^ e
      let _ : IsEmpty (Set.univᶜ : Set barrier.gap.fusion.core) :=
        ⟨fun x ↦ x.property (Set.mem_univ x)⟩
      rw [Ordinal.type_eq_zero_of_empty]
      exact Ordinal.opow_pos e Ordinal.omega0_pos
  | cons y ys ih =>
      rw [finiteCommonBlueColumn_cons, Set.compl_inter]
      apply typeLT_union_lt_opow
      · rw [← htarget]
        exact
          Erdos1172Part3BHTFiniteCommonBlueColumns.BHTRedCoreSectionBarrier.blueColumn_compl_type_lt
            barrier hcompl (hys y (by simp))
      · exact ih (fun z hz ↦ hys z (by simp [hz]))

/-- Finite compatibility is automatic in the BHT second-maximum gap:
every finite family of candidates has a common blue predecessor column
of exact type `RedCoreTarget`. -/
theorem BHTRedCoreSectionBarrier.finiteCommonBlueColumn_type
    {red blue : SimpleGraph W2}
    (barrier : BHTRedCoreSectionBarrier red blue)
    (hcompl : IsCompl red blue)
    (ys : List W2)
    (hys : ∀ y ∈ ys, y ∈ barrier.gap.candidates) :
    typeLT (finiteCommonBlueColumn blue barrier.gap.fusion ys) =
      RedCoreTarget := by
  obtain ⟨e, htarget⟩ := exists_redCoreTarget_eq_omega_opow
  have hcoreType : typeLT barrier.gap.fusion.core = ω ^ e :=
    barrier.gap.fusion.core_type.trans htarget
  obtain hcommonFull | hcomplFull :=
    typeLT_eq_opow_or_compl_eq_opow
      (X := barrier.gap.fusion.core)
      (s := (finiteCommonBlueColumn blue barrier.gap.fusion ys :
        Set barrier.gap.fusion.core))
      hcoreType
  · exact hcommonFull.trans htarget.symm
  · have hshort := finiteCommonBlueColumn_compl_type_lt
      barrier hcompl ys hys
    rw [hcomplFull, htarget.symm] at hshort
    exact (lt_irrefl RedCoreTarget hshort).elim

theorem finiteCommonBlueColumn_blue
    {red : SimpleGraph W2} (blue : SimpleGraph W2)
    (fusion : BHTFinalFusionCore red) (ys : List W2) :
    ∀ x ∈ finiteCommonBlueColumn blue fusion ys,
      ∀ y ∈ ys, blue.Adj (x : W2) y := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
      intro x hx z hz
      simp only [finiteCommonBlueColumn_cons, Set.mem_inter_iff] at hx
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hx.1
      · exact ih x hx.2 z hz

end Erdos1172Part3BHTFiniteCommonBlueColumns
