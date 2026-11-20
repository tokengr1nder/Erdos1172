/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSimultaneousRunStopping
public import Erdos1172.Part4InternalSimultaneousRunLaws

@[expose] public section

/-!
# The successful branch of a simultaneous run

An explicit Boolean hypothesis excludes the endpoint sentinel from the
guarded vertex range. Under this hypothesis the actual decoded graph is
an increasing injective homogeneous omega-one sequence. Its vertices lie
below, and have the same color to, the endpoint. This module does not
construct a successful run or assert a success-or-stopping dichotomy.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousRun

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosSimultaneousEntry ErdosSimultaneousHistory

/-- The success premise concerns the actual guarded internal range,
not inequality of chosen external representatives. -/
theorem run_vertex_ne_top_of_success {P top i y : bSet 𝔹} {Γ : 𝔹}
    (Hsuccess : Γ ≤ (rangeMem omegaOne (vertexHistory P) top)ᶜ)
    (Hcurrent : Γ ≤ pair i y ∈ᴮ vertexHistory P) : Γ ≤ (y =ᴮ top)ᶜ := by
  rw [← imp_bot, ← deduction]
  have HtopPair : Γ ⊓ y =ᴮ top ≤ pair i top ∈ᴮ vertexHistory P :=
    bv_rw'' (ϕ := fun z => pair i z ∈ᴮ vertexHistory P) inf_le_right
      (inf_le_left.trans Hcurrent) B_ext_pair_mem_right
  have Hrange : Γ ⊓ y =ᴮ top ≤ rangeMem omegaOne (vertexHistory P) top :=
    le_iSup_of_le i (le_inf
      (inf_le_left.trans (mem_vertexHistory_iff.mp Hcurrent).1) HtopPair)
  exact bv_absurd _ Hrange (inf_le_left.trans Hsuccess)

/-- Increasingness needs only the entry laws and absence of the sentinel;
full totality is used later to identify an actual omega-one injection. -/
theorem run_vertex_increasing
    {color : Bool} {R S top P : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hsuccess : Γ ≤ (rangeMem omegaOne (vertexHistory P) top)ᶜ) :
    Γ ≤ increasingOn omegaOne (vertexHistory P) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro j
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ (((i ∈ᴮ omegaOne ⊓ j ∈ᴮ omegaOne) ⊓ i ∈ᴮ j) ⊓
    (pair i x ∈ᴮ vertexHistory P ⊓ pair j y ∈ᴮ vertexHistory P))
  have Hcurrent : Δ ≤ pair j y ∈ᴮ vertexHistory P :=
    inf_le_right.trans (inf_le_right.trans inf_le_right)
  exact (nonstop_stage_above_previous (inf_le_left.trans Hlaw) Hcurrent
    (run_vertex_ne_top_of_success (inf_le_left.trans Hsuccess) Hcurrent)
    (inf_le_right.trans (inf_le_left.trans inf_le_right))
    (inf_le_right.trans (inf_le_right.trans inf_le_left))).trans inf_le_left

/-- No graph restriction or replacement enumeration is introduced. -/
theorem run_vertex_is_injective
    {color : Bool} {R S top P : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ is_function omegaOne entrySpace P)
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hsuccess : Γ ≤ (rangeMem omegaOne (vertexHistory P) top)ᶜ) :
    Γ ≤ is_injective_function omegaOne omegaTwo (vertexHistory P) := by
  have Hfunction := vertexHistory_is_function_of_run HP
  have Hinc := run_vertex_increasing Hlaw Hsuccess
  refine le_inf Hfunction ?_
  apply le_iInf
  intro i
  apply le_iInf
  intro j
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ (pair i x ∈ᴮ vertexHistory P ⊓
    pair j y ∈ᴮ vertexHistory P ⊓ x =ᴮ y)
  have Hix : Δ ≤ pair i x ∈ᴮ vertexHistory P :=
    inf_le_right.trans (inf_le_left.trans inf_le_left)
  have Hjy : Δ ≤ pair j y ∈ᴮ vertexHistory P :=
    inf_le_right.trans (inf_le_left.trans inf_le_right)
  exact increasingOn_injective_on omegaOne_Ord (inf_le_left.trans Hinc)
    (mem_domain_of_is_function Hix (inf_le_left.trans Hfunction))
    (mem_domain_of_is_function Hjy (inf_le_left.trans Hfunction)) Hix Hjy
    (inf_le_right.trans inf_le_right)

private theorem or_cases {Γ a b v : 𝔹}
    (H : Γ ≤ a ⊔ b)
    (Hleft : ∀ {Δ : 𝔹}, Δ ≤ Γ → Δ ≤ a → Δ ≤ v)
    (Hright : ∀ {Δ : 𝔹}, Δ ≤ Γ → Δ ≤ b → Δ ≤ v) : Γ ≤ v :=
  (le_inf le_rfl H).trans
    (bv_or_elim_right (Hleft inf_le_left inf_le_right) (Hright inf_le_left inf_le_right))

/-- Internal preimages are extracted at the original Boolean condition.
Their ordinal trichotomy is split locally, not as an external disjunction. -/
theorem run_vertex_graphColor_of_range
    {color : Bool} {R S top P x y : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ is_function omegaOne entrySpace P)
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hsuccess : Γ ≤ (rangeMem omegaOne (vertexHistory P) top)ᶜ)
    (Hx : Γ ≤ rangeMem omegaOne (vertexHistory P) x)
    (Hy : Γ ≤ rangeMem omegaOne (vertexHistory P) y) (Hxy : Γ ≤ x ∈ᴮ y) :
    Γ ≤ graphColor color R x y := by
  obtain ⟨i, Hi⟩ := exists_convert Hx
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  obtain ⟨j, Hj⟩ := exists_convert Hy
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  have Hfunction := is_func'_of_is_function (vertexHistory_is_function_of_run HP)
  have Htri := epsilon_trichotomy_of_Ord (Hi.trans inf_le_left)
    (Hj.trans inf_le_left) omegaOne_Ord
  apply or_cases Htri
  · intro Δ HΔ HeqOrLt
    apply or_cases HeqOrLt
    · intro Λ HΛ Heq
      have Hvalues : Λ ≤ x =ᴮ y := eq_of_is_func'_of_eq
        ((HΛ.trans HΔ).trans Hfunction) Heq
        ((HΛ.trans HΔ).trans (Hi.trans inf_le_right))
        ((HΛ.trans HΔ).trans (Hj.trans inf_le_right))
      exact (bot_of_mem_self' (mem_congr Hvalues bv_refl
        ((HΛ.trans HΔ).trans Hxy))).trans bot_le
    · intro Λ HΛ Hij
      have Hcurrent := (HΛ.trans HΔ).trans (Hj.trans inf_le_right)
      exact (nonstop_stage_above_previous ((HΛ.trans HΔ).trans Hlaw) Hcurrent
        (run_vertex_ne_top_of_success ((HΛ.trans HΔ).trans Hsuccess) Hcurrent)
        Hij ((HΛ.trans HΔ).trans (Hi.trans inf_le_right))).trans inf_le_right
  · intro Δ HΔ Hji
    have Hcurrent := HΔ.trans (Hi.trans inf_le_right)
    rw [graphColor_symm color R x y]
    exact (nonstop_stage_above_previous (HΔ.trans Hlaw) Hcurrent
      (run_vertex_ne_top_of_success (HΔ.trans Hsuccess) Hcurrent)
      Hji (HΔ.trans (Hj.trans inf_le_right))).trans inf_le_right

theorem run_vertex_homogeneous
    {color : Bool} {R S top P : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ is_function omegaOne entrySpace P)
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hsuccess : Γ ≤ (rangeMem omegaOne (vertexHistory P) top)ᶜ) :
    Γ ≤ homogeneousUnion color R omegaOne omegaOne (vertexHistory P) (vertexHistory P) := by
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  simp only [sup_self]
  let Δ := Γ ⊓ ((rangeMem omegaOne (vertexHistory P) x ⊓
    rangeMem omegaOne (vertexHistory P) y) ⊓ x ∈ᴮ y)
  have Hxy : Δ ≤ x ∈ᴮ y := inf_le_right.trans inf_le_right
  apply (le_graphColor_iff_oriented color R Hxy).mp
  exact run_vertex_graphColor_of_range (inf_le_left.trans HP) (inf_le_left.trans Hlaw)
    (inf_le_left.trans Hsuccess)
    (inf_le_right.trans (inf_le_left.trans inf_le_left))
    (inf_le_right.trans (inf_le_left.trans inf_le_right)) Hxy

end bSet.ErdosSimultaneousRun
