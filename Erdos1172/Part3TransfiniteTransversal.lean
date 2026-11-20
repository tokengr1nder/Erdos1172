/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3TransfiniteIncidence

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3TransfiniteTransversal

open Erdos1172Part3Failure Erdos1172Part3TransfiniteIncidence

/-- The range of a strictly increasing map from `ω₂` to itself has exact
order type `ω₂`. -/
private theorem typeLT_range_eq_omegaTwo_of_strictMono (f : W2 → W2)
    (hf : StrictMono f) : typeLT (Set.range f) = ω_ 2 := by
  have htype :=
    ((hf.strictMonoOn Set.univ).orderIso f Set.univ).ordinalType_congr
  have himageRange : typeLT (f '' Set.univ) = typeLT (Set.range f) :=
    (OrderIso.setCongr (f '' Set.univ) (Set.range f)
      Set.image_univ).ordinalType_congr
  calc
    typeLT (Set.range f) = typeLT (f '' Set.univ) := himageRange.symm
    _ = typeLT (Set.univ : Set W2) := htype.symm
    _ = typeLT W2 := OrderIso.Set.univ.ordinalType_congr
    _ = ω_ 2 := by simpa only [W2] using Ordinal.type_toType (ω_ 2 : Ordinal.{0})

/-- Sharp transversal split inside the full incidence obstruction.  One
maximum is chosen from every arm.  The maxima form a strictly increasing
`ω₂` spine containing a blue transversal of exact type `ω₁ + 1`.
For two transversal maxima from ordered arms, their mutual edge is blue,
yet the later maximum has a different red predecessor in the whole
earlier arm. -/
def FullOmegaTwoTransversalSplit
    (red blue : SimpleGraph W2) : Prop :=
  ∃ (indexedArms : W2 → Set W2) (representatives : W2 → W2)
      (transversal : Set W2),
    StrictMono representatives ∧
    typeLT (Set.range representatives) = ω_ 2 ∧
    (∀ a, blue.IsClique (indexedArms a) ∧
      typeLT (indexedArms a) = ω_ 1 + 1) ∧
    (∀ a, representatives a ∈ indexedArms a) ∧
    (∀ a, ∀ x ∈ indexedArms a, x ≤ representatives a) ∧
    transversal ⊆ Set.range representatives ∧
    blue.IsClique transversal ∧ typeLT transversal = ω_ 1 + 1 ∧
    ∀ a b, a < b → representatives a ∈ transversal →
      representatives b ∈ transversal →
      blue.Adj (representatives a) (representatives b) ∧
      ∃ x ∈ indexedArms a,
        x ≠ representatives a ∧ red.Adj x (representatives b)

/-- The full incidence obstruction yields an exact red target, or the
sharp blue-transversal/red-predecessor split. -/
theorem fullOmegaTwoIncidence_redTarget_or_transversalSplit
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (hobs : FullOmegaTwoIncidenceObstruction red blue) :
    OrdinalRamsey.HasCliqueOfType red
        Erdos1172Part3FiniteStars.RedTarget ∨
      FullOmegaTwoTransversalSplit red blue := by
  classical
  obtain ⟨arms, harms, hordered, hsuccessor, hincidence⟩ := hobs
  let stage : W2 → ArmIndex := fun a ↦ ⟨(a : Ordinal), a.toOrd.2⟩
  have hstageStrict : StrictMono stage := by
    intro a b hab
    change (a : Ordinal) < (b : Ordinal)
    rw [← Ordinal.ToType.mk.apply_symm_apply a,
      ← Ordinal.ToType.mk.apply_symm_apply b] at hab
    exact (Ordinal.ToType.mk.lt_iff_lt).mp hab
  have hmaxExists (a : W2) :
      ∃ maximum : arms (stage a), IsMax maximum :=
    exists_max_of_type_omegaOne_add_one (harms (stage a)).2
  let maximum (a : W2) : arms (stage a) :=
    Classical.choose (hmaxExists a)
  have hmaximumMax (a : W2) : IsMax (maximum a) :=
    Classical.choose_spec (hmaxExists a)
  let indexedArms : W2 → Set W2 := fun a ↦ arms (stage a)
  let representatives : W2 → W2 := fun a ↦ maximum a
  have hrepresentativeMem (a : W2) :
      representatives a ∈ indexedArms a := (maximum a).property
  have hrepresentativeMax (a : W2) (x : W2) (hx : x ∈ indexedArms a) :
      x ≤ representatives a := by
    have hxMax : (⟨x, hx⟩ : arms (stage a)) ≤ maximum a :=
      le_of_not_gt ((isMax_iff_forall_not_lt.mp (hmaximumMax a)) ⟨x, hx⟩)
    exact hxMax
  have hrepresentativesStrict : StrictMono representatives := by
    intro a b hab
    exact hordered (stage a) (stage b) (hstageStrict hab)
      (representatives a) (hrepresentativeMem a)
      (representatives b) (hrepresentativeMem b)
  have hrepresentativesType :
      typeLT (Set.range representatives) = ω_ 2 :=
    typeLT_range_eq_omegaTwo_of_strictMono representatives
      hrepresentativesStrict
  obtain ⟨transversal, htransversalSub, htransversalRed,
      htransversalType⟩ |
      ⟨transversal, htransversalSub, htransversalBlue,
        htransversalType⟩ :=
    OrdinalRamsey.on_set_of_type
      (Erdos1172Part3CHAsymmetric.red_target_or_blue_omegaOne_add_one hCH)
      red blue hcompl (Set.range representatives) hrepresentativesType
  · exact Or.inl ⟨transversal, htransversalRed, htransversalType⟩
  · right
    refine ⟨indexedArms, representatives, transversal,
      hrepresentativesStrict, hrepresentativesType, ?_,
      hrepresentativeMem, hrepresentativeMax, htransversalSub,
      htransversalBlue, htransversalType, ?_⟩
    · intro a
      exact harms (stage a)
    · intro a b hab ha hb
      have hblue : blue.Adj (representatives a) (representatives b) :=
        htransversalBlue ha hb (hrepresentativesStrict hab).ne
      obtain ⟨x, hx, hred⟩ :=
        hincidence (stage a) (stage b) (hstageStrict hab)
          (representatives b) (hrepresentativeMem b)
      have hxne : x ≠ representatives a := by
        intro hxa
        subst x
        rw [← hcompl.compl_eq, SimpleGraph.compl_adj] at hblue
        exact hblue.2 hred
      exact ⟨hblue, x, hx, hxne, hred⟩

/-- Global exact-target-or-transversal normal form under CH. -/
theorem part3_exact_or_fullOmegaTwoTransversalSplit
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red
        Erdos1172Part3FiniteStars.RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      FullOmegaTwoTransversalSplit red blue := by
  obtain htarget | hobs :=
    part3_exact_or_fullOmegaTwoIncidenceObstruction hCH red blue hcompl
  · exact Or.inl htarget
  · obtain hred | hsplit :=
      fullOmegaTwoIncidence_redTarget_or_transversalSplit
        hCH red blue hcompl hobs
    · exact Or.inl (Or.inl hred)
    · exact Or.inr hsplit

end Erdos1172Part3TransfiniteTransversal
