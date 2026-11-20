/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3OmegaOneRectangleRefinement
public import Erdos1172.Part3OmegaOneNeighborUltrametric

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3OmegaOneFinalBarrier

open Erdos1172Part3Failure Erdos1172Part3OmegaOneRectangleRefinement
  Erdos1172Part3OmegaOneNeighborProfileBridge
  Erdos1172Part3OmegaOneNeighborUltrametric

/-- Current sharp global Part 3 normal form under CH.  The constant
full-neighbourhood branch is refined to an ordered complete-red rectangle
between exact blue `omegaOne` and `omegaOne + 1` sides.  The nonconstant
branch is the bounded locally compact `W2` first-difference ultrametric,
with the entire stationary fan and countable predecessor system retained. -/
theorem part3_exact_or_orderedBlueRectangle_or_neighborhoodUltrametric
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red
        Erdos1172Part3FiniteStars.RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      OrderedBlueOmegaOneByOmegaOneAddOneRedRectangle red blue ∨
      LocallyCompactUltrametricOmegaOneBaseNeighborhoodResidualWithFan
        red blue := by
  obtain htarget | hrectangle | hresidual :=
    part3_exact_or_orderedBlueOmegaOneByOmegaOneAddOneRedRectangle_or_injectiveNeighborhoodResidual
      hCH red blue hcompl
  · exact Or.inl htarget
  · exact Or.inr (Or.inl hrectangle)
  · exact Or.inr (Or.inr
      (StationaryInjectiveOmegaOneBaseNeighborhoodResidualWithFan.to_locallyCompactUltrametric
        hCH hresidual))

end Erdos1172Part3OmegaOneFinalBarrier
