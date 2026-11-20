/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3ClosedDecisionSystem

@[expose] public section

open Cardinal Ordinal Set Order

namespace Erdos1172Part3ClosedDenseRequirements

open ErdosRadoCHAsym (W1)
open Erdos1172Part3ClosedDecisionSystem

variable {P : Type} [Preorder P]

theorem countablyClosed_Iic (hclosed : CountablyClosed P) (p0 : P) :
    CountablyClosed (Set.Iic p0) := by
  intro C hne hcount hchain
  let D : Set P := Subtype.val '' C
  have hDchain : IsChain (· ≤ ·) D := by
    rintro p ⟨q, hq, rfl⟩ r ⟨s, hs, rfl⟩ _
    exact hchain.total hq hs
  obtain ⟨lower, hlower⟩ := hclosed D (hne.image _) (hcount.image _) hDchain
  obtain ⟨p, hp⟩ := hne
  have hlower0 : lower ≤ p0 := (hlower p.val ⟨p, hp, rfl⟩).trans p.property
  exact ⟨⟨lower, hlower0⟩, fun q hq => hlower q.val ⟨q, hq, rfl⟩⟩

/-- Any family of at most omegaOne dense requirements can be met on
one descending omegaOne sequence, retaining a witness stage for each
requirement. There is no lower bound of the completed sequence. -/
theorem exists_antitone_dense_sequence_of_card {I : Type}
    (hclosed : CountablyClosed P) (p0 : P) (D : I → Set P)
    (hD : ∀ i, DenseBelow (D i)) (hI : #I ≤ ℵ_ 1) :
    ∃ f : W1 → P, Antitone f ∧ (∀ j, f j ≤ p0) ∧
      ∀ i : I, ∃ j : W1, f j ∈ D i := by
  classical
  obtain ⟨index⟩ : Nonempty (I ↪ W1) := (Cardinal.le_def _ _).mp (by
    simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using hI)
  let E (j : W1) : Set P := {p | ∀ i : I, index i = j → p ∈ D i}
  have hE : ∀ j, DenseBelow (E j) := by
    intro j p
    by_cases h : ∃ i : I, index i = j
    · obtain ⟨q, hq, hqp⟩ := hD h.choose p
      refine ⟨q, ?_, hqp⟩
      intro i hi
      have heq : i = h.choose := index.injective (hi.trans h.choose_spec.symm)
      simpa only [heq] using hq
    · exact ⟨p, fun i hi => (h ⟨i, hi⟩).elim, le_rfl⟩
  obtain ⟨f, hanti, hstart, hmeet⟩ := exists_antitone_dense_sequence hclosed p0 E hE
  exact ⟨f, hanti, hstart, fun i => ⟨index i, hmeet (index i) i rfl⟩⟩

end Erdos1172Part3ClosedDenseRequirements
