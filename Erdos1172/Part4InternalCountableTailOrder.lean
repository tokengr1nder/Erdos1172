/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCountableTailRun

@[expose] public section

/-!
# Whole-block support and strict order of the actual countable tail

Every statement is extracted from the actual candidate law. The initial
family and the full strict-prefix image are retained, so all initial
points precede all tail points and successive tail blocks are separated.
No final point map, homogeneous target, or model existence is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCountableTailOrder

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosCanonicalBlocks ErdosBlockCandidate
open ErdosCountableTailRun ErdosSmallPoolOperations

theorem tailCandidate_of_pair
    {color : Bool} {R J E S B Tail i A : bSet 𝔹} {Γ : 𝔹}
    (Htail : Γ ≤ tailCandidatesLaw color R J E S B Tail)
    (Hpair : Γ ≤ pair i A ∈ᴮ Tail) :
    Γ ≤ blockCandidate color R J E S
      (binary_union B (image i (bv_powerset omegaTwo) Tail)) ∅ A :=
  ((le_inf (Htail.trans ((iInf_le _ i).trans (iInf_le _ A))) Hpair).trans
    bv_imp_elim).trans inf_le_left

theorem tailObject_of_pair
    {color : Bool} {R J E S B Tail i A : bSet 𝔹} {Γ : 𝔹}
    (Htail : Γ ≤ tailCandidatesLaw color R J E S B Tail)
    (Hpair : Γ ≤ pair i A ∈ᴮ Tail) : Γ ≤ A ∈ᴮ blockObjects color R :=
  blockCandidate_object (tailCandidate_of_pair Htail Hpair)

theorem tail_initial_before
    {color : Bool} {R J E S B Tail i A b x y : bSet 𝔹} {Γ : 𝔹}
    (Htail : Γ ≤ tailCandidatesLaw color R J E S B Tail)
    (Hpair : Γ ≤ pair i A ∈ᴮ Tail) (Hb : Γ ≤ b ∈ᴮ B)
    (Hx : Γ ≤ x ∈ᴮ b) (Hy : Γ ≤ y ∈ᴮ A) : Γ ≤ x ∈ᴮ y :=
  objectsBefore_apply (blockCandidate_before (tailCandidate_of_pair Htail Hpair))
    (mem_of_mem_subset subset_binary_union_left Hb) Hx Hy

theorem tail_tail_before
    {color : Bool} {R J E S B Tail i j A b x y : bSet 𝔹} {Γ : 𝔹}
    (HTail : Γ ≤ is_function bSet.omega (bv_powerset omegaTwo) Tail)
    (Htail : Γ ≤ tailCandidatesLaw color R J E S B Tail)
    (Hi : Γ ≤ pair i b ∈ᴮ Tail) (Hj : Γ ≤ pair j A ∈ᴮ Tail)
    (Hij : Γ ≤ i ∈ᴮ j) (Hx : Γ ≤ x ∈ᴮ b) (Hy : Γ ≤ y ∈ᴮ A) :
    Γ ≤ x ∈ᴮ y :=
  objectsBefore_apply (blockCandidate_before (tailCandidate_of_pair Htail Hj))
    (mem_of_mem_subset subset_binary_union_right
      (mem_image Hi Hij (mem_codomain_of_is_function Hi HTail))) Hx Hy

end bSet.ErdosCountableTailOrder
