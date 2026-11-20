/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCohenCountableUnion
public import Erdos1172.Part4InternalNameSequence

@[expose] public section

/-!
# Countable binary assignments with arbitrary Boolean coefficients

Each coefficient is realized by an actual mixed name: one on that Boolean
piece and zero on its complement. The mixed name belongs to the internal
two-element set at top. The same-condition countable-assignment construction
then supplies one actual condition realizing all coefficients, with the
two conditional pair-membership laws retained separately.

No global Boolean branch is selected. Coordinate membership, separation,
and freshness over the original domain remain explicit local hypotheses.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCohen

open ErdosPartialInjection

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- The actual binary mixed name with coefficient b for the value one. -/
def binaryAssignmentName (b : B) : bSet B :=
  two_term_mixture b bᶜ inf_compl_eq_bot (1 : bSet B) (0 : bSet B)

theorem binaryAssignmentName_eq_one (b : B) :
    b ≤ binaryAssignmentName b =ᴮ (1 : bSet B) :=
  (mixing_lemma_two_term b bᶜ inf_compl_eq_bot (1 : bSet B) (0 : bSet B)).1

theorem binaryAssignmentName_eq_zero (b : B) :
    bᶜ ≤ binaryAssignmentName b =ᴮ (0 : bSet B) :=
  (mixing_lemma_two_term b bᶜ inf_compl_eq_bot (1 : bSet B) (0 : bSet B)).2

/-- Both components are in two, so the mixed name belongs to two at top. -/
theorem binaryAssignmentName_mem_two (b : B) :
    (⊤ : B) ≤ binaryAssignmentName b ∈ᴮ two := by
  have Hone : (⊤ : B) ≤ (1 : bSet B) ∈ᴮ two :=
    check_mem (PSet.ofNat_mem_of_lt (show 1 < 2 by omega))
  have Hzero : (⊤ : B) ≤ (0 : bSet B) ∈ᴮ two :=
    check_mem (PSet.ofNat_mem_of_lt (show 0 < 2 by omega))
  exact (two_term_mixture_mem_top (two : bSet B) (1 : bSet B) (0 : bSet B)
    b bᶜ inf_compl_eq_bot sup_compl_eq_top (top_unique Hone) (top_unique Hzero)).ge

end bSet.ErdosCohen
