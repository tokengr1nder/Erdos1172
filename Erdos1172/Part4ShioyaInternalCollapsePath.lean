/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalProjectedWord
public import Erdos1172.Part4InternalBoundedImageRecursionTotal
public import Erdos1172.Part4InternalFusionHistoryCongruence

@[expose] public section

/-! # Ordinal recursion of cones along a named collapse path -/

set_option autoImplicit false
noncomputable section
universe u
open scoped Flypitch
open Lattice
namespace bSet.ErdosShioyaInternal.CollapsePath
open ErdosBoundedFunctionValue ErdosBoundedImageRecursion ErdosRelationGraph ErdosFusionHistoryCongruence
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

/-- A condition surviving all earlier stages. -/
def survives (past p : N) : B := allIn past (fun C => p ∈ᴮ C)

private theorem survives_ext {H p : N → N} (hH : B_congr H) (hp : B_congr p) :
    B_ext (fun z => survives (H z) (p z)) :=
  allIn_ext hH (fun C => B_ext_term (fun t => t ∈ᴮ C) p B_ext_mem_left hp)

def test (R past label p : N) : B :=
  survives past p ⊓ (survives past label ⟹ edge R p label)

private theorem test_ext {R H label p : N → N} (hR : B_congr R) (hH : B_congr H)
    (hl : B_congr label) (hp : B_congr p) : B_ext (fun z => test (R z) (H z) (label z) (p z)) :=
  B_ext_inf (survives_ext hH hp) (B_ext_imp (h₁ := survives_ext hH hl) (h₂ := edge_ext hR hp hl))

/-- At each stage retain all past constraints. When the proposed label
survives them, also restrict to its principal lower cone. -/
def next (P R input i past : N) : N :=
  comprehend (test R past (graphValue P input i)) P

theorem next_mem {Γ : B} {P R input i H x : N} :
    Γ ≤ x ∈ᴮ next P R input i H ↔ Γ ≤ x ∈ᴮ P ∧ Γ ≤ survives H x ∧
      Γ ≤ (survives H (graphValue P input i) ⟹ edge R x (graphValue P input i)) := by
  rw [next,mem_comprehend_and (test_ext (const_congr _) (const_congr _) (const_congr _) id_congr),test,le_inf_iff]

private theorem next_stage (P R input H : N) : B_congr (fun i => next P R input i H) :=
  comprehend_parameter_congr P (fun i => test R H (graphValue P input i))
    (fun _ => test_ext (const_congr _) (const_congr _) (const_congr _) id_congr)
    (fun _ => test_ext (const_congr _) (const_congr _) (graphValue_congr_input _ _) (const_congr _))

private theorem next_past (P R input i : N) : B_congr (next P R input i) :=
  comprehend_parameter_congr P (fun H => test R H (graphValue P input i))
    (fun _ => test_ext (const_congr _) (const_congr _) (const_congr _) id_congr)
    (fun _ => test_ext (const_congr _) id_congr (const_congr _) (const_congr _))

theorem next_congr {P R f g i j H J : N} {Γ : B} (values : Γ ≤ graphValue P f i =ᴮ graphValue P g j)
    (histories : Γ ≤ H =ᴮ J) : Γ ≤ next P R f i H =ᴮ next P R g j J := by
  have hl : B_congr (fun t => comprehend (test R H t) P) := comprehend_parameter_congr P (fun t => test R H t)
    (fun _ => test_ext (const_congr _) (const_congr _) (const_congr _) id_congr)
    (fun _ => test_ext (const_congr _) (const_congr _) id_congr (const_congr _))
  exact bv_trans (hl values) (next_past P R g j histories)

def trace (P R input : N) (history : N) : B :=
  imageRecLaw (bv_powerset P) (next P R input) history

/-- One internal graph of cone values on the full mixed ordinal domain. -/
theorem exists_trace {Γ : B} {length : N} (P R input : N) (ord : Γ ≤ Ord length) :
    ∃ h : N, Γ ≤ is_function length (bv_powerset P) h ∧ Γ ≤ trace P R input h := by
  obtain ⟨h,hh⟩ := exists_bounded_image_recursion (Φ := next P R input) ord
    (next_stage P R input) (next_past P R input) (le_iInf fun i => le_iInf fun H =>
      projection_imp.mpr fun _ _ _ => mem_powerset_iff.mpr
        (comprehend_subset (ϕ := test R H (graphValue P input i)) P))
  exact ⟨h,hh.trans inf_le_left,hh.trans inf_le_right⟩

theorem nested {Γ : B} {P R input h length i j C D : N}
    (hf : Γ ≤ is_function length (bv_powerset P) h) (law : Γ ≤ trace P R input h)
    (hi : Γ ≤ edge h i C) (hj : Γ ≤ edge h j D) (hij : Γ ≤ i ∈ᴮ j) : Γ ≤ D ⊆ᴮ C := by
  have hc := (projection_function_bounds hf hi).2
  have inPast := mem_image hi hij hc
  have form := imageRecLaw_apply law hj
  rw [subset_unfold']
  refine le_iInf fun x => projection_imp.mpr ?_
  intro Δ hd hx
  have step := next_mem.mp (mem_congr bv_refl (hd.trans form) hx)
  exact allIn_elim step.2.1 (hd.trans inPast)

/-- Every row surviving the past is taken on the same guard as its input
label. On the complementary guard the path retains precisely the past. -/
theorem row_mem {Γ : B} {P R input h i C x : N} (law : Γ ≤ trace P R input h) (hi : Γ ≤ edge h i C) :
    Γ ≤ x ∈ᴮ C ↔ Γ ≤ x ∈ᴮ P ∧ Γ ≤ survives (image i (bv_powerset P) h) x ∧
      Γ ≤ (survives (image i (bv_powerset P) h) (graphValue P input i) ⟹ edge R x (graphValue P input i)) := by
  have eq := imageRecLaw_apply law hi
  exact ⟨fun hx => next_mem.mp (mem_congr bv_refl eq hx),
    fun hx => mem_congr bv_refl (bv_symm eq) (next_mem.mpr hx)⟩

end bSet.ErdosShioyaInternal.CollapsePath
