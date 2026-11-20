/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CHAsymmetric
public import Erdos1172.Part3OmegaOneNeighborProfileBridge

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3OmegaOneRectangleRefinement

open Erdos1172Part3Failure Erdos1172Part3FiniteStars
  Erdos1172Part3CHAsymmetric Erdos1172Part3OmegaOneNeighborProfiles
  Erdos1172Part3OmegaOneNeighborProfileBridge

/-- An ordered complete-red rectangle whose two sides are respectively
blue of exact types `omegaOne` and `omegaOne + 1`. -/
def OrderedBlueOmegaOneByOmegaOneAddOneRedRectangle
    (red blue : SimpleGraph W2) : Prop :=
  ∃ (left right : Set W2),
    blue.IsClique left ∧ typeLT left = ω_ 1 ∧
    blue.IsClique right ∧ typeLT right = ω_ 1 + 1 ∧
    (∀ x ∈ left, ∀ y ∈ right, x < y) ∧
    ∀ x ∈ left, ∀ y ∈ right, red.Adj x y

/-- Under CH, the `omegaTwo` side of an `omegaOne`-by-`omegaTwo`
red rectangle either contains the exact Part 3 red target, or can be
thinned to a blue side of exact type `omegaOne + 1`. -/
theorem HasOmegaOneByOmegaTwoRedRectangle.redTarget_or_orderedBlueRefinement
    (hCH : CH) {red blue : SimpleGraph W2} (hcompl : IsCompl red blue)
    (hrectangle : HasOmegaOneByOmegaTwoRedRectangle red blue) :
    OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      OrderedBlueOmegaOneByOmegaOneAddOneRedRectangle red blue := by
  obtain ⟨left, right, hleftBlue, hleftType, hrightType,
      hbefore, hcross⟩ := hrectangle
  obtain ⟨redRight, hredRightSub, hredRightClique, hredRightType⟩ |
      ⟨blueRight, hblueRightSub, hblueRightClique, hblueRightType⟩ :=
    OrdinalRamsey.on_set_of_type
      (ErdosRadoCHAsym.ordinalRamsey_omegaTwo_omegaTwo_omegaOne_add_one
        hCH)
      red blue hcompl right hrightType
  · left
    obtain ⟨target, htargetSub, htargetType⟩ :=
      Ordinal.exists_subset_typeLT_eq redRight
        (part3_red_target_lt_omegaTwo.le.trans_eq hredRightType.symm)
    exact ⟨target, hredRightClique.subset htargetSub, htargetType⟩
  · right
    exact ⟨left, blueRight, hleftBlue, hleftType,
      hblueRightClique, hblueRightType,
      (fun x hx y hy ↦ hbefore x hx y (hblueRightSub hy)),
      fun x hx y hy ↦ hcross x hx y (hblueRightSub hy)⟩

/-- Global CH normal form obtained by discharging the constant
full-neighbourhood branch of the profile dichotomy with the asymmetric
Erdos--Rado relation. -/
theorem part3_exact_or_orderedBlueOmegaOneByOmegaOneAddOneRedRectangle_or_injectiveNeighborhoodResidual
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      OrderedBlueOmegaOneByOmegaOneAddOneRedRectangle red blue ∨
      StationaryInjectiveOmegaOneBaseNeighborhoodResidualWithFan
        red blue := by
  obtain hexact | hrectangle | hresidual :=
    part3_exact_or_omegaOneByOmegaTwoRedRectangle_or_injectiveNeighborhoodResidual
      hCH red blue hcompl
  · exact Or.inl hexact
  · obtain hred | hrefined :=
      HasOmegaOneByOmegaTwoRedRectangle.redTarget_or_orderedBlueRefinement
        hCH hcompl hrectangle
    · exact Or.inl (Or.inl hred)
    · exact Or.inr (Or.inl hrefined)
  · exact Or.inr (Or.inr hresidual)

end Erdos1172Part3OmegaOneRectangleRefinement
