/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CompleteRestriction
public import Erdos1172.Part3IteratedHechlerPreservation

@[expose] public section

/-!
# Canonical empty-tail restrictions for the constructed orders

The base restriction is complete for both one added Hechler stage and
the already constructed countable extension. The countable inclusion
is defined coordinate by coordinate with genuinely empty stems and
sides; it is not an arbitrary coherent extension chosen by existence.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3CanonicalBaseRestriction

open Erdos1172Part3CompleteRestriction (CompleteRestriction)
open Erdos1172Part3IteratedHechlerOrder (Condition emptyOver liftBase liftBase_le base_le)

variable {P : Type} [Preorder P]

theorem le_emptyOver (p : Condition P) (q : P) (hpq : p.base ≤ q) : p ≤ emptyOver q := by
  refine ⟨hpq, ?_, ?_, ?_⟩
  · intro i v hv
    cases hv
  · exact Set.empty_subset _
  · intro i hi v hv F hF
    exact hF.elim

theorem emptyOver_mono {p q : P} (hpq : p ≤ q) : emptyOver p ≤ emptyOver q :=
  le_emptyOver (emptyOver p) q hpq

def oneStage : CompleteRestriction (Condition P) P where
  restrict := ⟨Condition.base, fun _ _ h => base_le h⟩
  embed := ⟨emptyOver, fun _ _ h => emptyOver_mono h⟩
  restrict_embed _ := rfl
  below_embed p := le_emptyOver p p.base le_rfl
  lift p q hqp := ⟨liftBase p q, liftBase_le p hqp, rfl⟩

end Erdos1172Part3CanonicalBaseRestriction
