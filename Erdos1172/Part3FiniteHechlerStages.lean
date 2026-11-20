/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3IteratedHechlerCentering

@[expose] public section

/-!
# Finite towers of explicit dominating-function stages

Every successor uses small names for functions over the preceding
decision order. Closure, countable centeredness, the omegaTwo chain
condition, and the GCH size bound are proved at every finite stage.
This is not yet a countable-limit construction or the higher-core BHT
recursion, and it does not assert the Part 3 partition relation.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3FiniteHechlerStages

open ErdosRadoCHAsym (W1)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3FunctionDecisions (FunctionDecisions BoundedAt)
open Erdos1172Part3StationaryDecisions (OmegaTwoCC)
open Erdos1172Part3IteratedHechlerOrder (Condition)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)

structure SmallClosedCenteredOrder where
  Carrier : Type
  order : Preorder Carrier
  closed : @CountablyClosed Carrier order
  centered : @CountablyCenteredCode Carrier order
  small : #Carrier ≤ ℵ_ 2

instance (P : SmallClosedCenteredOrder) : Preorder P.Carrier := P.order

noncomputable def initial (hGCH : GCH) : SmallClosedCenteredOrder where
  Carrier := Erdos1172Part3HechlerOrder.Condition
  order := inferInstance
  closed := Erdos1172Part3HechlerOrder.countablyClosed
  centered := Erdos1172Part3IteratedHechlerCentering.hechlerCentered hGCH.toCH
  small := Erdos1172Part3HechlerCentering.mk_Condition_le hGCH

noncomputable def extend (hGCH : GCH) (P : SmallClosedCenteredOrder) :
    SmallClosedCenteredOrder where
  Carrier := Condition P.Carrier
  order := inferInstance
  closed := Erdos1172Part3IteratedHechlerClosure.countablyClosed P.closed
  centered := P.centered.extend hGCH.toCH
  small := Erdos1172Part3IteratedHechlerCentering.mk_Condition_le hGCH P.small

noncomputable def stage (hGCH : GCH) : ℕ → SmallClosedCenteredOrder
  | 0 => initial hGCH
  | n + 1 => extend hGCH (stage hGCH n)

theorem stage_succ_carrier (hGCH : GCH) (n : ℕ) :
    (stage hGCH (n + 1)).Carrier = Condition (stage hGCH n).Carrier := rfl

theorem stage_countablyClosed (hGCH : GCH) (n : ℕ) :
    CountablyClosed (stage hGCH n).Carrier := (stage hGCH n).closed

theorem stage_omegaTwoCC (hGCH : GCH) (n : ℕ) : OmegaTwoCC (stage hGCH n).Carrier :=
  (stage hGCH n).centered.omegaTwoCC

theorem stage_card_le (hGCH : GCH) (n : ℕ) : #(stage hGCH n).Carrier ≤ ℵ_ 2 :=
  (stage hGCH n).small

/-- At every finite successor, every earlier-stage function decision
system is eventually bounded below a strengthening of any condition.
There is no restriction to functions fixed in the original ground type. -/
theorem stage_bounds_earlier_functions (hGCH : GCH) (n : ℕ)
    (p0 : Condition (stage hGCH n).Carrier)
    (F : FunctionDecisions (stage hGCH n).Carrier W1 W1) :
    ∃ p : Condition (stage hGCH n).Carrier, p ≤ p0 ∧ ∃ bound : W1,
      ∀ q : Condition (stage hGCH n).Carrier, q ≤ p → ∀ i : W1, bound < i →
        ∀ v : W1, q.stem i = some v → BoundedAt F q.base i v :=
  Erdos1172Part3IteratedHechlerClosure.exists_eventual_bound_for_function
    (stage_omegaTwoCC hGCH n) p0 F

end Erdos1172Part3FiniteHechlerStages
