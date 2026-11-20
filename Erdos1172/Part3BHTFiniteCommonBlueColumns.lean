/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3BHTExactBlueColumns

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3BHTFiniteCommonBlueColumns

open Erdos1172Part3Failure Erdos1172Part3OneSuccessorBarrier Erdos1172Part3BHTExactBlueColumns Erdos1172OrdinalUnaryIndivisibility

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

end Erdos1172Part3BHTFiniteCommonBlueColumns
