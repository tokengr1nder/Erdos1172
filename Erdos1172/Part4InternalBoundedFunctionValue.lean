/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalRelationGraph

@[expose] public section

/-!
# Proof-independent, globally congruent bounded graph evaluation

The vendor `function_eval` is chosen from a witness theorem and depends
on a function proof, the Boolean condition, and a domain-membership proof.
Here the value is instead a fixed set operation on the graph, codomain,
and argument: the union of the bounded image of the argument singleton.

Congruence holds without any functionality or membership hypotheses.
When the graph is an actual bounded function, this operation equals its
actual value at the same Boolean condition. No coherent external choice
of individual value witnesses is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosBoundedFunctionValue

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

def graphValue (V F x : bSet 𝔹) : bSet 𝔹 :=
  bv_union (image ({x} : bSet 𝔹) V F)

theorem graphValue_congr_input (V F : bSet 𝔹) : B_congr (graphValue V F) := by
  intro x y Γ H
  exact B_congr_bv_union (B_congr_image_left (eq_singleton_of_eq H))

theorem graphValue_congr_graph (V x : bSet 𝔹) : B_congr (fun F => graphValue V F x) := by
  intro F G Γ H
  exact B_congr_bv_union (B_congr_image_right H)

/-- This equality is local to the original condition. It is proved from
the actual graph, not inferred from a global equality of chosen witnesses. -/
theorem graphValue_eq_of_pair {D V F x y : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function D V F) (Hpair : Γ ≤ pair x y ∈ᴮ F) :
    Γ ≤ graphValue V F x =ᴮ y := by
  have Hyimage : Γ ≤ y ∈ᴮ image ({x} : bSet 𝔹) V F :=
    mem_image Hpair (mem_singleton_of_eq bv_refl) (mem_codomain_of_is_function Hpair HF)
  apply mem_ext
  · apply le_iInf
    intro t
    rw [← deduction]
    let Δ := Γ ⊓ t ∈ᴮ graphValue V F x
    obtain ⟨z, Hz⟩ := exists_convert (mem_bv_union_iff.mp
      (show Δ ≤ t ∈ᴮ graphValue V F x from inf_le_right))
      (B_ext_inf B_ext_mem_left B_ext_mem_right)
    obtain ⟨w, Hw⟩ := exists_convert (mem_image_iff.mp (Hz.trans inf_le_left)).2
      (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    have Hwx : Δ ≤ w =ᴮ x := eq_mem_singleton (Hw.trans inf_le_left)
    have Hzy : Δ ≤ z =ᴮ y := eq_of_is_function_of_eq (inf_le_left.trans HF) Hwx
      (Hw.trans inf_le_right) (inf_le_left.trans Hpair)
    exact mem_congr bv_refl Hzy (Hz.trans inf_le_right)
  · apply le_iInf
    intro t
    rw [← deduction]
    exact mem_bv_union_iff.mpr
      (le_iSup_of_le y (le_inf (inf_le_left.trans Hyimage) inf_le_right))

/-- Both boundedness and the original graph pair hold for the single
proof-independent value operation, without shrinking the condition. -/
theorem graphValue_spec {D V F x : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function D V F) (Hx : Γ ≤ x ∈ᴮ D) :
    Γ ≤ graphValue V F x ∈ᴮ V ⊓ pair x (graphValue V F x) ∈ᴮ F := by
  have Hex : Γ ≤ ⨆ y, y ∈ᴮ V ⊓ pair x y ∈ᴮ F :=
    (le_inf ((is_total_of_is_function HF).trans (iInf_le _ x)) Hx).trans bv_imp_elim
  obtain ⟨y, Hy⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Heq : Γ ≤ graphValue V F x =ᴮ y := graphValue_eq_of_pair HF (Hy.trans inf_le_right)
  exact le_inf (mem_congr (bv_symm Heq) bv_refl (Hy.trans inf_le_left))
    (mem_congr (pair_congr bv_refl (bv_symm Heq)) bv_refl (Hy.trans inf_le_right))

theorem graphValue_mem {D V F x : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function D V F) (Hx : Γ ≤ x ∈ᴮ D) :
    Γ ≤ graphValue V F x ∈ᴮ V :=
  (graphValue_spec HF Hx).trans inf_le_left

theorem graphValue_pair_mem {D V F x : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function D V F) (Hx : Γ ≤ x ∈ᴮ D) :
    Γ ≤ pair x (graphValue V F x) ∈ᴮ F :=
  (graphValue_spec HF Hx).trans inf_le_right

end bSet.ErdosBoundedFunctionValue
