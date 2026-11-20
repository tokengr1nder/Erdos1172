/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CofinalFiniteCuts
public import Erdos1172.Part3FiniteSupport

@[expose] public section

/-!
# Finite coordinate witnesses for cover membership

The covering families are upward open in the product of omegaOne:
membership has a witness consisting of finitely many coordinate lower
bounds. This concrete property is retained through profile coding,
images, and unions for use with function decisions.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3CofinalCoverSupport

open ErdosRadoCHAsym (W1)

theorem line_supported {V : Type} [LinearOrder V]
    (data : Erdos1172Part3CofinalLineCover.LineCoverData V) : FinitelySupported data.cover := by
  intro f x hx
  rcases hx with hx | hx
  · exact ⟨∅, fun _ _ => Or.inl hx⟩
  · refine ⟨{data.row x}, fun g hg => Or.inr ?_⟩
    exact hx.trans_le (hg (data.row x) (Finset.mem_singleton_self _))

end Erdos1172Part3CofinalCoverSupport
