/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3RegularMembership

@[expose] public section

/-!
# Uniform reflection for condition-dependent neighborhoods

The chain condition supplies a small set of tests for universal truth,
simultaneously for all conditions. A club of cuts then reflects every
locally coded regular name. The condition is not required to have a code
below the cut. Source membership may itself depend on the condition.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3RegularNeighborhoodReflection

open Erdos1172Part3RegularMembership
open Erdos1172Part3StationaryDecisions
open Erdos1172Part3ClosedDecisionSystem (DenseBelow)
open ErdosRadoCHAsym (W2)
open Erdos1172Part3NeighborhoodCode (alephZero_lt_cof_W2)

variable {P X : Type} [Preorder P]

/-- A single small set detects universal truth at every condition.
Its tests are chosen from a predense antichain of deciding conditions. -/
theorem exists_small_universal_test (hcc : OmegaTwoCC P) (U : RegularName P X) :
    ∃ tests : Set X, #(tests) ≤ ℵ_ 1 ∧
      ∀ p : P, (∀ x ∈ tests, U.holds p x) → ∀ x : X, U.holds p x := by
  classical
  let D : Set P := {p | (∀ x : X, U.holds p x) ∨ ∃ x : X, (neg U).holds p x}
  have hD : DenseBelow D := by
    intro p
    by_cases hp : ∀ x : X, U.holds p x
    · exact ⟨p, Or.inl hp, le_rfl⟩
    · push Not at hp
      obtain ⟨x, hx⟩ := hp
      obtain ⟨q, hqp, hq⟩ := (not_holds_iff_exists_neg U p x).mp hx
      exact ⟨q, Or.inr ⟨x, hq⟩, hqp⟩
  obtain ⟨A, hAD, hA, hpredense⟩ := exists_predense_antichain D hD
  have hAsmall : #A ≤ ℵ_ 1 := by
    have h := hcc A hA
    have hsucc : (ℵ_ 2 : Cardinal) = Order.succ (ℵ_ 1) := by
      rw [Cardinal.succ_aleph, show (1 : Ordinal.{0}) + 1 = 2 by norm_num]
    rwa [hsucc, Order.lt_succ_iff] at h
  let B : Set P := {q | q ∈ A ∧ ∃ x : X, (neg U).holds q x}
  let value (q : B) : X := q.property.2.choose
  have hvalue (q : B) : (neg U).holds q.val (value q) := q.property.2.choose_spec
  refine ⟨Set.range value, ?_, ?_⟩
  · exact Cardinal.mk_range_le.trans ((Cardinal.mk_subtype_mono (fun q hq => hq.1)).trans hAsmall)
  · intro p hp x
    by_contra hx
    obtain ⟨q, hqp, hq⟩ := (not_holds_iff_exists_neg U p x).mp hx
    obtain ⟨t, htA, s, hsq, hst⟩ := hpredense q
    rcases hAD htA with htall | htbad
    · exact hq s hsq (U.persistent hst (htall x))
    · let tB : B := ⟨t, htA, htbad⟩
      exact hvalue tB s hst (U.persistent (hsq.trans hqp) (hp (value tB) ⟨tB, rfl⟩))

/-- The test set has a strict ordinal bound independent of the condition. -/
theorem exists_uniform_reflection_bound (hcc : OmegaTwoCC P)
    (U : RegularName P W2) :
    ∃ b : W2, ∀ a : W2, b < a → ∀ p : P, (∀ x < a, U.holds p x) → ∀ x : W2, U.holds p x := by
  obtain ⟨tests, hsmall, htests⟩ := exists_small_universal_test hcc U
  obtain ⟨b, hb⟩ := Erdos1172Part3CoreObjectCode.exists_objectBound ⟨tests, hsmall⟩
  exact ⟨b, fun a hba p hp => htests p (fun x hx => hp x ((hb x hx).trans hba))⟩

theorem exists_club_reflects_regular {C : Type} (hcc : OmegaTwoCC P)
    (r : C ↪ W2) (named : C → RegularName P W2) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, ∀ c : C, r c < a →
      ∀ p : P, (∀ x < a, (named c).holds p x) → ∀ x : W2, (named c).holds p x := by
  choose bound hbound using fun c => exists_uniform_reflection_bound hcc (named c)
  exact ⟨{a | ∀ c, r c < a → bound c < a},
    ClubClosure.isClub_rankClosed r bound alephZero_lt_cof_W2,
    fun a ha c hc p => hbound c a (ha c hc) p⟩

/-- Reflection of inclusion retains every strengthening in its statement;
the source is an arbitrary regular name, not necessarily a ground set. -/
theorem exists_club_reflects_named_inclusion {C : Type} (hcc : OmegaTwoCC P)
    (r : C ↪ W2) (named : C → RegularName P W2) (source : RegularName P W2) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, ∀ c : C, r c < a →
      ∀ p : P,
        (∀ x < a, ∀ q : P, q ≤ p → source.holds q x → (named c).holds q x) →
        ∀ x : W2, ∀ q : P, q ≤ p → source.holds q x → (named c).holds q x :=
  exists_club_reflects_regular hcc r (fun c => implication source (named c))

end Erdos1172Part3RegularNeighborhoodReflection
