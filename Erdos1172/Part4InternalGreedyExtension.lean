/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalGreedyPartial
public import Erdos1172.Part4InternalInjectionExtension
public import Erdos1172.Part4InternalPartialInjectionDomain

@[expose] public section

/-!
# Successor extension of an internal greedy graph

The least admissible value at the actual current domain is above every
old value, so its freshness is proved rather than assumed. Adjoining it
preserves the complete least-choice law, because a functional extension
cannot alter the graph on any prefix on which the old graph was total.
All names and Boolean conditions are arbitrary; this step requires no
ideal, CH, or separately assumed successful enumeration.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosGreedyPartial

open ErdosOmegaTwo ErdosPartialInjection ErdosInjectionExtension
open ErdosRowCandidates ErdosOrdinalLeast

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

private theorem mem_insert1_value {x y A : bSet 𝔹} :
    x ∈ᴮ bSet.insert1 y A = x =ᴮ y ⊔ x ∈ᴮ A :=
  mem_insert1

private theorem insert_cases {p q f : bSet 𝔹} {Γ v : 𝔹}
    (Hp : Γ ≤ p ∈ᴮ bSet.insert1 q f)
    (Hnew : ∀ {Δ : 𝔹}, Δ ≤ Γ → Δ ≤ p =ᴮ q → Δ ≤ v)
    (Hold : ∀ {Δ : 𝔹}, Δ ≤ Γ → Δ ≤ p ∈ᴮ f → Δ ≤ v) : Γ ≤ v := by
  have Hsplit : Γ ≤ p =ᴮ q ⊔ p ∈ᴮ f :=
    Hp.trans (mem_insert1_value (x := p) (y := q) (A := f)).le
  exact (le_inf le_rfl Hsplit).trans
    (bv_or_elim_right (Hnew inf_le_left inf_le_right) (Hold inf_le_left inf_le_right))

/-- An admissible next value cannot already occur in the prefix image.
This is a local Boolean statement, including arbitrary mixed names. -/
theorem rowCandidate_fresh_image {D seed F f y : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' D omegaOne f)
    (Hy : Γ ≤ y ∈ᴮ rowCandidates D seed F f) :
    Γ ≤ (y ∈ᴮ image D omegaOne f)ᶜ := by
  have Hlegal := (mem_rowCandidates_iff Hf).mp Hy
  have Hprevious : Γ ≤ ⨅ j, ⨅ v,
      _root_.imp (j ∈ᴮ D ⊓ pair j v ∈ᴮ f) (v ∈ᴮ y) :=
    Hlegal.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  rw [← imp_bot, ← deduction]
  obtain ⟨j, Hj⟩ := exists_convert
    (mem_image_iff.mp (show Γ ⊓ y ∈ᴮ image D omegaOne f ≤
      y ∈ᴮ image D omegaOne f from inf_le_right)).2
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  have Hyy : Γ ⊓ y ∈ᴮ image D omegaOne f ≤ y ∈ᴮ y :=
    (le_inf (inf_le_left.trans
      (Hprevious.trans ((iInf_le _ j).trans (iInf_le _ y)))) Hj).trans bv_imp_elim
  exact bot_of_mem_self' Hyy

/-- Add the actual least legal candidate at the actual next ordinal
coordinate. Freshness and support follow from candidate membership, and
every old least-choice equation is preserved by functional extension. -/
theorem greedyPartial_insert_next {seed F f y : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ greedyPartial seed F f)
    (HD : Γ ≤ graphDomain omegaOne omegaOne f ∈ᴮ omegaOne)
    (Hy : Γ ≤ leastIn
      (rowCandidates (graphDomain omegaOne omegaOne f) seed F f) y) :
    Γ ≤ greedyPartial seed F
      (bSet.insert1 (pair (graphDomain omegaOne omegaOne f) y) f) := by
  let D := graphDomain omegaOne omegaOne f
  let g := bSet.insert1 (pair D y) f
  have Hpartial : Γ ≤ partialGraph omegaOne omegaOne f := Hf.trans inf_le_left
  have Hfunction : Γ ≤ is_injective_function D omegaOne f :=
    greedyPartial_function Hf
  have Hweak : Γ ≤ is_func' D omegaOne f :=
    Hfunction.trans (inf_le_left.trans inf_le_left)
  have Hcandidate : Γ ≤ y ∈ᴮ rowCandidates D seed F f := leastIn_mem Hy
  have Hyω : Γ ≤ y ∈ᴮ omegaOne := mem_of_mem_subset rowCandidates_subset Hcandidate
  have Hfresh : Γ ≤ (y ∈ᴮ image D omegaOne f)ᶜ :=
    rowCandidate_fresh_image Hweak Hcandidate
  have Hnotself : Γ ≤ (D ∈ᴮ D)ᶜ := by
    rw [← imp_bot, ← deduction]
    exact bot_of_mem_self' inf_le_right
  have Hnewfunction : Γ ≤ is_injective_function (succ D) omegaOne g :=
    is_injective_function_insertPair Hfunction Hnotself Hyω Hfresh
  have Hnewpartial : Γ ≤ partialGraph omegaOne omegaOne g :=
    partialGraph_of_ordinal_function
      (Ord_succ (partialGraph_domain_Ord omegaOne_Ord Hpartial))
      (Ord.succ_le_of_lt omegaOne_Ord HD) Hnewfunction
  have Hnewfunc : Γ ≤ is_func g :=
    Hnewfunction.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
  have HcandidateEq : Γ ≤ rowCandidates D seed F f =ᴮ rowCandidates D seed F g :=
    rowCandidates_eq_of_extension subset_insertPair Hnewfunc Hweak
  have HyleastNew : Γ ≤ leastIn (rowCandidates D seed F g) y :=
    bv_rw'' (ϕ := fun C => leastIn C y) HcandidateEq Hy (leastIn_ext_set y)
  refine le_inf Hnewpartial ?_
  apply le_iInf
  intro i
  apply le_iInf
  intro x
  rw [← deduction]
  let Δ := Γ ⊓ pair i x ∈ᴮ g
  have HΔ : Δ ≤ Γ := inf_le_left
  apply insert_cases (show Δ ≤ pair i x ∈ᴮ g from inf_le_right)
  · intro Λ HΛ Hnew
    have HiD : Λ ≤ i =ᴮ D := eq_of_eq_pair_left' Hnew
    have Hxy : Λ ≤ x =ᴮ y := eq_of_eq_pair_right' Hnew
    have Hstage : Λ ≤ rowCandidates i seed F g =ᴮ rowCandidates D seed F g :=
      rowCandidates_congr_stage seed F g HiD
    have Hleastiy : Λ ≤ leastIn (rowCandidates i seed F g) y :=
      bv_rw' (ϕ := fun C => leastIn C y) Hstage
        (H_new := (HΛ.trans HΔ).trans HyleastNew) (h_congr := leastIn_ext_set y)
    exact bv_rw' (ϕ := leastIn (rowCandidates i seed F g)) Hxy (H_new := Hleastiy)
      (h_congr := leastIn_ext_value (rowCandidates i seed F g))
  · intro Λ HΛ Hold
    have HfΛ : Λ ≤ greedyPartial seed F f := (HΛ.trans HΔ).trans Hf
    have Hprefix : Λ ≤ is_func' i omegaOne f :=
      greedyPartial_is_func'_prefix HfΛ Hold
    have Heq : Λ ≤ rowCandidates i seed F f =ᴮ rowCandidates i seed F g :=
      rowCandidates_eq_of_extension subset_insertPair
        ((HΛ.trans HΔ).trans Hnewfunc) Hprefix
    exact bv_rw'' (ϕ := fun C => leastIn C x) Heq
      (greedyLaw_apply (HfΛ.trans inf_le_right) Hold) (leastIn_ext_set x)

end bSet.ErdosGreedyPartial
