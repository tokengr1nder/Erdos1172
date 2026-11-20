/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3StationaryDecisions

@[expose] public section

/-!
# Ground clubs contained in explicit club-decision systems

The omegaTwo chain condition bounds the possible values on a maximal
antichain. Closure points of these bounds form a ground club contained
in every condition's club decisions. Consequently the stationary
possibility predicate survives intersection with all such systems.

The decision and dense-limit laws are explicit premises. No generic
extension, iteration, or BHT homogeneous set is asserted here.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3ClubDecisions

open Erdos1172Part3NeighborhoodCode (W2 cof_W2 alephZero_lt_cof_W2)
open Erdos1172Part3StationaryDecisions
open Erdos1172Part3ClosedDecisionSystem (DenseBelow)
open Erdos1172Part3TwoSuccessorBootstrap (stationary_inter_club)

variable {P : Type} [Preorder P]

/-- A persistent membership system with dense unboundedness and the
dense form of closure at nonzero limits. The cofinality premise itself
excludes successor points whenever a condition exists. -/
structure ClubDecisions (P : Type) [Preorder P] where
  member : P → W2 → Prop
  persistent : Persistent member
  unbounded : ∀ p : P, ∀ a : W2,
    ∃ q : P, q ≤ p ∧ ∃ b : W2, a < b ∧ member q b
  closed : ∀ p : P, ∀ a : W2, (Set.Iio a).Nonempty →
    (∀ b : W2, b < a → ∀ q : P, q ≤ p →
      ∃ r : P, r ≤ q ∧ ∃ c : W2, b < c ∧ c < a ∧ member r c) → member p a

/-- Ordinary clubs give constant decision systems. This also checks the
nonzero-limit convention in the definition. -/
def ClubDecisions.ofClub (P : Type) [Preorder P] (C : Set W2) (hC : IsClub C) :
    ClubDecisions P where
  member := fun _ a => a ∈ C
  persistent := fun _ h => h
  unbounded := by
    intro p a
    obtain ⟨b, hab⟩ := Set.exists_gt_of_aleph0_lt_cof alephZero_lt_cof_W2 a
    obtain ⟨c, hc, hbc⟩ := hC.isCofinal b
    exact ⟨p, le_rfl, c, hab.trans_le hbc, hc⟩
  closed := by
    intro p a hne hdense
    have hcofinal : ∀ b : W2, b < a → ∃ c ∈ C ∩ Set.Iio a, b < c := by
      intro b hba
      obtain ⟨r, _, c, hbc, hca, hc⟩ := hdense b hba p le_rfl
      exact ⟨c, ⟨hc, hca⟩, hbc⟩
    obtain ⟨b, hba⟩ := hne
    obtain ⟨c, hc, _⟩ := hcofinal b hba
    apply hC.isLUB_mem (fun _ hx => hx.1) ⟨c, hc⟩
    refine ⟨fun _ hx => hx.2.le, ?_⟩
    intro d hd
    by_contra h
    have hda : d < a := lt_of_not_ge h
    obtain ⟨e, he, hde⟩ := hcofinal d hda
    exact hde.not_ge (hd he)

/-- A chain-condition order cannot have an unbounded club-decision
system avoiding every ground club. All conditions contain one common
ground club, rather than merely possibly meeting it. -/
theorem ClubDecisions.exists_common_ground_club (C : ClubDecisions P)
    (hcc : OmegaTwoCC P) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, ∀ p : P, C.member p a := by
  classical
  let D (a : W2) : Set P := {p | ∃ b : W2, a < b ∧ C.member p b}
  have hD : ∀ a : W2, DenseBelow (D a) := by
    intro a p
    obtain ⟨q, hqp, b, hab, hqb⟩ := C.unbounded p a
    exact ⟨q, ⟨b, hab, hqb⟩, hqp⟩
  choose A hAD hA hpredense using fun a => exists_predense_antichain (D a) (hD a)
  let value (a : W2) (q : A a) : W2 := (hAD a q.property).choose
  have hvalue (a : W2) (q : A a) : a < value a q ∧ C.member q.val (value a q) :=
    (hAD a q.property).choose_spec
  have hbound (a : W2) : ∃ b : W2, ∀ q : A a, value a q < b := by
    have hsmall : #(Set.range (value a)) < Order.cof W2 := by
      rw [cof_W2]
      exact Cardinal.mk_range_le.trans_lt (hcc (A a) (hA a))
    obtain ⟨b, hb⟩ := not_isCofinal_iff.mp
      (fun hc => hsmall.not_ge (Order.cof_le hc))
    exact ⟨b, fun q => hb (value a q) ⟨q, rfl⟩⟩
  choose bound hbound using hbound
  obtain ⟨a0⟩ : Nonempty W2 := Set.nonempty_of_aleph0_lt_cof alephZero_lt_cof_W2
  let club : Set W2 := {a | ClubClosure.ClosedUnder bound a} ∩ Set.Ioi a0
  have hclub : IsClub club :=
    (ClubClosure.isClub_closedUnder bound alephZero_lt_cof_W2).inter
      alephZero_lt_cof_W2.ne'
      (Set.isClub_Ioi_of_aleph0_lt_cof alephZero_lt_cof_W2 a0)
  refine ⟨club, hclub, ?_⟩
  intro a ha p
  apply C.closed p a ⟨a0, ha.2⟩
  intro b hba q hqp
  obtain ⟨s, hsA, r, hrq, hrs⟩ := hpredense b q
  refine ⟨r, hrq, value b ⟨s, hsA⟩, (hvalue b ⟨s, hsA⟩).1, ?_, ?_⟩
  · exact (hbound b ⟨s, hsA⟩).trans (ha.1 b hba)
  · exact C.persistent hrs (hvalue b ⟨s, hsA⟩).2

/-- Stationary possibilities remain stationary after intersecting an
arbitrary explicit club-decision system. -/
theorem stationaryAt_inter_club (hcc : OmegaTwoCC P)
    (U : P → W2 → Prop) {p : P} (hU : StationaryAt U p) (C : ClubDecisions P) :
    StationaryAt (fun q a => U q a ∧ C.member q a) p := by
  obtain ⟨club, hclub, hmem⟩ := C.exists_common_ground_club hcc
  intro q hqp
  apply (stationary_inter_club (hU q hqp) hclub).mono
  rintro a ⟨⟨r, hrq, hra⟩, hac⟩
  exact ⟨r, hrq, hra, hmem a hac r⟩

/-- Characterize stationary possibilities by meeting every club-decision
system below every strengthening. This makes the preservation claim
precise without referring to an unconstructed forcing universe. -/
theorem stationaryAt_iff_meets_clubDecisions (hcc : OmegaTwoCC P)
    (U : P → W2 → Prop) (p : P) :
    StationaryAt U p ↔ ∀ q : P, q ≤ p → ∀ C : ClubDecisions P,
      ∃ r : P, r ≤ q ∧ ∃ a : W2, U r a ∧ C.member r a := by
  constructor
  · intro hU q hqp C
    obtain ⟨a, r, hrq, hra, hCa⟩ :=
      ((stationaryAt_inter_club hcc U hU C) q hqp).nonempty
    exact ⟨r, hrq, a, hra, hCa⟩
  · intro h q hqp club hclub
    obtain ⟨r, hrq, a, hra, hCa⟩ := h q hqp (ClubDecisions.ofClub P club hclub)
    exact ⟨a, ⟨r, hrq, hra⟩, hCa⟩

end Erdos1172Part3ClubDecisions
