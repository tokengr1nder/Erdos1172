/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3StationaryDecisions
public import Erdos1172.Part3CenteredStationaryLoss

@[expose] public section

/-!
# A square block joined to stationary future decisions

Row bounds for the blue losses in an ordered red square give an actual
clique-decision system with a stationary future. The common block is
represented by decisions in the concrete countably closed Hechler order;
it is not asserted to be one ground block with a ground stationary future.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3StationarySquareDecisions

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3HechlerOrder
open Erdos1172Part3StationaryDecisions
open Erdos1172Part3ClosedDecisionSystem (CliqueDecisions)

theorem exists_strict_tail (bound : W1) :
    ∃ f : W1 → W1, StrictMono f ∧ ∀ i, bound < f i := by
  let _ : IsRegularCardinalOrder W1 := ⟨by
    rw [cof_W1, Cardinal.ord_aleph]
    simp only [W1, Ordinal.type_toType, le_refl]⟩
  have hcof : ℵ₀ < Order.cof W1 := by
    rw [cof_W1]
    exact Cardinal.aleph0_lt_aleph.mpr (by norm_num)
  let e := Order.enum (Set.Ioi bound)
    (Set.isClub_Ioi_of_aleph0_lt_cof hcof bound).isCofinal
  exact ⟨fun i => (e i).val, (Subtype.strictMono_coe _).comp e.strictMono,
    fun i => (e i).property⟩

noncomputable def tail (bound : W1) : W1 → W1 := (exists_strict_tail bound).choose

theorem tail_strict (bound : W1) : StrictMono (tail bound) :=
  (exists_strict_tail bound).choose_spec.1

theorem lt_tail (bound i : W1) : bound < tail bound i :=
  (exists_strict_tail bound).choose_spec.2 i

abbrev Square : Type := W1 ×ₗ W1

end Erdos1172Part3StationarySquareDecisions
