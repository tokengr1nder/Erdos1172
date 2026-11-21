/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedAvoidance
public import Erdos1172.Part3CountableDecisionFusion

@[expose] public section

/-!
# Simultaneously following countably many named neighborhoods

Every active neighborhood is decided at the cut before choosing the next
vertex. Positive decisions give small complements; negative decisions
remain negative at every later strengthening. Thus the output control
law quantifies over all subsequent conditions.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedNeighborhoodStep

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularNamedIdeal
open Erdos1172Part3NamedAvoidance
open Erdos1172Part3NamedPositiveExtension (colorGraph)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3CountableRankClosure (Local)

variable {P I : Type} [Preorder P] [LinearOrder I]
variable {G H : SimpleGraph W2} {r : Code P I G ↪ W2}
variable {σ : NiceCliqueName P I W2 G ↪ W2} {source : RegularName P W2} {a : W2}

def Control (H : SimpleGraph W2) (index : Local r a ↪ W1) (i : W1) (p : P) (y : W2) : Prop :=
  ∀ c : Local r a, index c < i → ∀ q : P, q ≤ p →
    (eval G H c.val).holds q a → (eval G H c.val).holds q y

abbrev Active (index : Local r a ↪ W1) (i : W1) := {c : Local r a // index c < i}

theorem mk_active_le (index : Local r a ↪ W1) (i : W1) : #(Active index i) ≤ ℵ₀ := by
  let e : Active index i ↪ Set.Iio i :=
    ⟨fun c => ⟨index c.val, c.property⟩,
      fun _ _ h => Subtype.ext (index.injective (congrArg Subtype.val h))⟩
  exact (Cardinal.mk_le_of_injective e.injective).trans
    (Erdos1172Part3RelationalDecisionFusion.mk_Iio_W1_le_aleph0 i)

theorem exists_extension_controlled (hclosed : CountablyClosed P)
    (ha : GoodCut r σ H source a) (b : Bool) (U : RegularName P W2)
    (index : Local r a ↪ W1) (i : W1) (p : P)
    (hpositive : (neg (smallName r H a)).holds p U)
    (selected : Set W2) (hcount : selected.Countable)
    (hbelow : selected ⊆ Set.Iio a)
    (hcolor : ∀ x ∈ selected, (colorGraph G H b).Adj x a) :
    ∃ q : P, q ≤ p ∧ ∃ y : W2, y < a ∧ U.holds q y ∧ Control H index i q y ∧
      ∀ x ∈ selected, x < y ∧ (colorGraph G H b).Adj x y := by
  classical
  let D (q : P) (c : Active index i) : Prop :=
    (eval G H c.val.val).holds q a ∨ (neg (eval G H c.val.val)).holds q a
  obtain ⟨q, hqp, hdec⟩ := exists_common_countable_witnesses hclosed p D (by
    intro p q c hqp h
    rcases h with h | h
    · exact Or.inl ((eval G H c.val.val).persistent hqp h)
    · exact Or.inr ((neg (eval G H c.val.val)).persistent hqp h))
    (fun s _ c => exists_deciding_refinement (eval G H c.val.val) s a) (mk_active_le index i)
  let V (c : Active index i) : RegularName P W2 :=
    if (eval G H c.val.val).holds q a then neg (eval G H c.val.val) else ground ∅
  have hV : ∀ c, (smallName r H a).holds q (V c) := by
    intro c
    dsimp only [V]
    split_ifs with h
    · exact named_complement_small ha q c.val.property h
    · exact smallName_empty ha q
  have havoid := small_iJoin hclosed ha (mk_active_le index i) q V hV
  obtain ⟨s, hsq, y, hya, hUy, hny, hcross⟩ := exists_actual_extension_avoiding
    hclosed ha b U (join V) q ((neg (smallName r H a)).persistent hqp hpositive)
      havoid selected hcount hbelow hcolor
  refine ⟨s, hsq.trans hqp, y, hya, hUy, ?_, hcross⟩
  intro c hci t hts hct
  let j : Active index i := ⟨c, hci⟩
  by_cases hcq : (eval G H c.val).holds q a
  · have hnegV : (all (fun j => neg (V j))).holds s y := by
      simpa only [neg_join] using hny
    have hn : (neg (neg (eval G H c.val))).holds s y := by
      simpa only [V, j, if_pos hcq] using hnegV j
    rw [Erdos1172Part3RegularMembership.neg_neg] at hn
    exact (eval G H c.val).persistent hts hn
  · have hn := (hdec j).resolve_left hcq
    exact (hn t (hts.trans hsq) hct).elim

end Erdos1172Part3NamedNeighborhoodStep
