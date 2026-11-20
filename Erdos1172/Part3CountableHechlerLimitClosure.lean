/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CountableHechlerLimit

@[expose] public section

open Cardinal Ordinal Set Order

namespace Erdos1172Part3CountableHechlerLimitClosure

open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3FiniteHechlerStages (stage stage_countablyClosed)
open Erdos1172Part3CountableHechlerLimit
open Erdos1172Part3PrescribedBaseFusion

variable {hGCH : GCH}

/-- The coordinates of the lower bound are constructed coherently.
Independent lower bounds at the finite stages would not suffice. -/
theorem countablyClosed : CountablyClosed (Limit hGCH) := by
  intro C hne hC hchain
  obtain ⟨first, hfirst⟩ := stage_countablyClosed hGCH 0 ((atMap 0) '' C)
    (hne.image (atMap 0)) (hC.image (atMap 0)) (hchain.image (atMap 0))
  obtain ⟨q, _, hq⟩ := exists_limit_starting_with
    (fun n p => ∀ c ∈ C, p ≤ c.point n) first
    (fun c hc => hfirst (c.point 0) ⟨c, hc, rfl⟩) (by
      intro n p hp
      have hbase : ∀ r ∈ (atMap (n + 1)) '' C, p ≤ r.base := by
        rintro _ ⟨c, hc, rfl⟩
        change p ≤ (c.point (n + 1)).base
        rw [c.coherent n]
        exact hp c hc
      obtain ⟨r, hrbase, hrlower⟩ := exists_chain_lower_with_base
        ((atMap (n + 1)) '' C) (hC.image (atMap (n + 1)))
        (hchain.image (atMap (n + 1))) p hbase
      exact ⟨r, hrbase, fun c hc => hrlower (c.point (n + 1)) ⟨c, hc, rfl⟩⟩)
  exact ⟨q, fun c hc n => hq n c hc⟩

end Erdos1172Part3CountableHechlerLimitClosure
