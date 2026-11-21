/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalColargeIntersection

@[expose] public section

/-!
Actual traces of arbitrary internal histories. The coordinate trace is the
graph j |-> X(j,sigma); the section trace is j |-> S(sigma,Y(j)). Separation
inside the relevant product supplies exact graph support, even when the
input relations are merely weak total-functional graphs. No external
choice of a coherent family of names is used.
-/

noncomputable section

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousTraces

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosPartition ErdosRelationGraph ErdosColargeIntersection

def rowHistory (δ X σ : bSet 𝔹) : bSet 𝔹 :=
  relationGraph δ omegaOne (fun j v => pair (pair j σ) v ∈ᴮ X)

private theorem rowHistory_ext_left (X σ v : bSet 𝔹) :
    B_ext (fun j => pair (pair j σ) v ∈ᴮ X) :=
  B_ext_pair_left (ϕ := fun p => pair p v ∈ᴮ X) B_ext_pair_mem_left

private theorem rowHistory_ext_row (X j v : bSet 𝔹) :
    B_ext (fun σ => pair (pair j σ) v ∈ᴮ X) :=
  B_ext_pair_right (ϕ := fun p => pair p v ∈ᴮ X) B_ext_pair_mem_left

theorem mem_rowHistory_iff {δ X σ j v : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair j v ∈ᴮ rowHistory δ X σ ↔
      Γ ≤ j ∈ᴮ δ ∧ Γ ≤ v ∈ᴮ omegaOne ∧ Γ ≤ pair (pair j σ) v ∈ᴮ X :=
  mem_relationGraph_iff (rowHistory_ext_left X σ) (fun _ => B_ext_pair_mem_right)

theorem rowHistory_apply {δ X σ j v : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ pair j v ∈ᴮ rowHistory δ X σ) : Γ ≤ pair (pair j σ) v ∈ᴮ X :=
  (mem_rowHistory_iff.mp H).2.2

/-- At a guarded coordinate the trace agrees with every value of the
original weak function, not only with a separately chosen representative. -/
theorem rowHistory_pair_iff {δ X σ j v : bSet 𝔹} {Γ : 𝔹}
    (HX : Γ ≤ is_func' (prod δ omegaOne) omegaOne X)
    (Hσ : Γ ≤ σ ∈ᴮ omegaOne) (Hj : Γ ≤ j ∈ᴮ δ) :
    (Γ ≤ pair j v ∈ᴮ rowHistory δ X σ) ↔ Γ ≤ pair (pair j σ) v ∈ᴮ X := by
  constructor
  · exact rowHistory_apply
  · intro Hpair
    exact mem_rowHistory_iff.mpr ⟨Hj,
      value_mem_codomain HX (mem_prod_iff.mpr ⟨Hj, Hσ⟩) Hpair, Hpair⟩

theorem rowHistory_is_function {δ X σ : bSet 𝔹} {Γ : 𝔹}
    (HX : Γ ≤ is_func' (prod δ omegaOne) omegaOne X)
    (Hσ : Γ ≤ σ ∈ᴮ omegaOne) :
    Γ ≤ is_function δ omegaOne (rowHistory δ X σ) := by
  apply relationGraph_is_function (P := fun j v => pair (pair j σ) v ∈ᴮ X)
    (rowHistory_ext_left X σ) (fun _ => B_ext_pair_mem_right)
  · apply le_iInf
    intro j
    rw [← deduction]
    exact (le_inf (inf_le_left.trans ((HX.trans inf_le_right).trans (iInf_le _ (pair j σ))))
      (mem_prod_iff.mpr ⟨inf_le_right, inf_le_left.trans Hσ⟩)).trans bv_imp_elim
  · intro j₁ j₂ v₁ v₂ Δ HΔ _ _ _ _ H₁ H₂ Hjj
    exact eq_of_is_func_of_eq (HΔ.trans (HX.trans inf_le_left)) (pair_congr Hjj bv_refl) H₁ H₂

def sectionTraceRel (S Y σ j A : bSet 𝔹) : 𝔹 :=
  ⨆ y, pair j y ∈ᴮ Y ⊓ pair (pair σ y) A ∈ᴮ S

def sectionTrace (δ S Y σ : bSet 𝔹) : bSet 𝔹 :=
  relationGraph δ (bv_powerset omegaOne) (sectionTraceRel S Y σ)

private theorem sectionTraceRel_ext_left (S Y σ A : bSet 𝔹) :
    B_ext (fun j => sectionTraceRel S Y σ j A) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_pair_mem_left B_ext_const)

private theorem sectionTraceRel_ext_right (S Y σ j : bSet 𝔹) :
    B_ext (sectionTraceRel S Y σ j) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_pair_mem_right)

private theorem sectionTraceRel_ext_middle (S Y σ j A : bSet 𝔹) :
    B_ext (fun y => pair j y ∈ᴮ Y ⊓ pair (pair σ y) A ∈ᴮ S) :=
  B_ext_inf B_ext_pair_mem_right
    (B_ext_pair_right (ϕ := fun p => pair p A ∈ᴮ S) B_ext_pair_mem_left)

theorem mem_sectionTrace_iff {δ S Y σ j A : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair j A ∈ᴮ sectionTrace δ S Y σ ↔
      Γ ≤ j ∈ᴮ δ ∧ Γ ≤ A ∈ᴮ bv_powerset omegaOne ∧
        Γ ≤ ⨆ y, pair j y ∈ᴮ Y ⊓ pair (pair σ y) A ∈ᴮ S :=
  mem_relationGraph_iff (sectionTraceRel_ext_left S Y σ) (sectionTraceRel_ext_right S Y σ)

theorem sectionTrace_witness {δ S Y σ j A : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ pair j A ∈ᴮ sectionTrace δ S Y σ) :
    ∃ y : bSet 𝔹, Γ ≤ pair j y ∈ᴮ Y ∧ Γ ≤ pair (pair σ y) A ∈ᴮ S := by
  obtain ⟨y, Hy⟩ := exists_convert (mem_sectionTrace_iff.mp H).2.2
    (sectionTraceRel_ext_middle S Y σ j A)
  exact ⟨y, Hy.trans inf_le_left, Hy.trans inf_le_right⟩

/-- Functionality of Y identifies its known value with the existential
intermediary of the section graph, at the original Boolean condition. -/
theorem sectionTrace_value_of_pair {δ S Y σ j y A : bSet 𝔹} {Γ : 𝔹}
    (Hfunc : Γ ≤ is_func Y) (Hjy : Γ ≤ pair j y ∈ᴮ Y)
    (HjA : Γ ≤ pair j A ∈ᴮ sectionTrace δ S Y σ) :
    Γ ≤ pair (pair σ y) A ∈ᴮ S := by
  obtain ⟨z, Hjz, HzA⟩ := sectionTrace_witness HjA
  have Hyz : Γ ≤ y =ᴮ z := eq_of_is_func_of_eq Hfunc bv_refl Hjy Hjz
  exact bv_rw' (ϕ := fun v => pair (pair σ v) A ∈ᴮ S) Hyz
    (h_congr := B_ext_pair_right (ϕ := fun p => pair p A ∈ᴮ S) B_ext_pair_mem_left)
    (H_new := HzA)

theorem sectionTrace_pair_iff {δ S Y σ j y A : bSet 𝔹} {Γ : 𝔹}
    (HY : Γ ≤ is_func' δ omegaTwo Y)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Hσ : Γ ≤ σ ∈ᴮ omegaOne) (Hj : Γ ≤ j ∈ᴮ δ)
    (Hjy : Γ ≤ pair j y ∈ᴮ Y) :
    (Γ ≤ pair j A ∈ᴮ sectionTrace δ S Y σ) ↔ Γ ≤ pair (pair σ y) A ∈ᴮ S := by
  constructor
  · exact sectionTrace_value_of_pair (HY.trans inf_le_left) Hjy
  · intro Hpair
    have Hy : Γ ≤ y ∈ᴮ omegaTwo := value_mem_codomain HY Hj Hjy
    exact mem_sectionTrace_iff.mpr ⟨Hj,
      value_mem_codomain HS (mem_prod_iff.mpr ⟨Hσ, Hy⟩) Hpair,
      le_iSup_of_le y (le_inf Hjy Hpair)⟩

theorem sectionTrace_is_function {δ S Y σ : bSet 𝔹} {Γ : 𝔹}
    (HY : Γ ≤ is_func' δ omegaTwo Y)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Hσ : Γ ≤ σ ∈ᴮ omegaOne) :
    Γ ≤ is_function δ (bv_powerset omegaOne) (sectionTrace δ S Y σ) := by
  apply relationGraph_is_function (P := sectionTraceRel S Y σ)
    (sectionTraceRel_ext_left S Y σ) (sectionTraceRel_ext_right S Y σ)
  · apply le_iInf
    intro j
    rw [← deduction]
    let Δ := Γ ⊓ j ∈ᴮ δ
    have HYtotal : Δ ≤ ⨆ y, y ∈ᴮ omegaTwo ⊓ pair j y ∈ᴮ Y :=
      (le_inf (inf_le_left.trans ((HY.trans inf_le_right).trans (iInf_le _ j)))
        inf_le_right).trans bv_imp_elim
    obtain ⟨y, Hy⟩ := exists_convert HYtotal (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
    have HStotal : Δ ≤ ⨆ A, A ∈ᴮ bv_powerset omegaOne ⊓ pair (pair σ y) A ∈ᴮ S :=
      (le_inf (inf_le_left.trans ((HS.trans inf_le_right).trans (iInf_le _ (pair σ y))))
        (mem_prod_iff.mpr ⟨inf_le_left.trans Hσ, Hy.trans inf_le_left⟩)).trans bv_imp_elim
    obtain ⟨A, HA⟩ := exists_convert HStotal (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
    exact le_iSup_of_le A (le_inf (HA.trans inf_le_left)
      (le_iSup_of_le y (le_inf (Hy.trans inf_le_right) (HA.trans inf_le_right))))
  · intro j₁ j₂ A₁ A₂ Δ HΔ _ _ _ _ H₁ H₂ Hjj
    obtain ⟨y₁, Hy₁⟩ := exists_convert H₁ (sectionTraceRel_ext_middle S Y σ j₁ A₁)
    obtain ⟨y₂, Hy₂⟩ := exists_convert H₂ (sectionTraceRel_ext_middle S Y σ j₂ A₂)
    have Hyy : Δ ≤ y₁ =ᴮ y₂ := eq_of_is_func_of_eq
      (HΔ.trans (HY.trans inf_le_left)) Hjj (Hy₁.trans inf_le_left) (Hy₂.trans inf_le_left)
    exact eq_of_is_func_of_eq (HΔ.trans (HS.trans inf_le_left)) (pair_congr bv_refl Hyy)
      (Hy₁.trans inf_le_right) (Hy₂.trans inf_le_right)

private theorem relationGraph_param_congr {A B : bSet 𝔹}
    (P : bSet 𝔹 → bSet 𝔹 → bSet 𝔹 → 𝔹)
    (hP : ∀ a b, B_ext (fun σ => P σ a b)) :
    B_congr (fun σ => relationGraph A B (P σ)) := by
  intro σ τ Γ H
  have hExt (ρ : bSet 𝔹) : B_ext (fun z => ⨆ a, ⨆ b, z =ᴮ pair a b ⊓ P ρ a b) :=
    B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
      B_ext_inf B_ext_bv_eq_left B_ext_const))
  have hParam (z : bSet 𝔹) : B_ext (fun ρ => ⨆ a, ⨆ b, z =ᴮ pair a b ⊓ P ρ a b) :=
    B_ext_iSup (h := fun a => B_ext_iSup (h := fun b => B_ext_inf B_ext_const (hP a b)))
  unfold relationGraph
  apply mem_ext
  · apply le_iInf
    intro z
    rw [← deduction]
    have Hmem := (mem_comprehend_and (hExt σ)).mp
      (show Γ ⊓ z ∈ᴮ comprehend (fun w => ⨆ a, ⨆ b, w =ᴮ pair a b ⊓ P σ a b) (prod A B) ≤
        z ∈ᴮ comprehend (fun w => ⨆ a, ⨆ b, w =ᴮ pair a b ⊓ P σ a b) (prod A B)
        from inf_le_right)
    exact (mem_comprehend_and (hExt τ)).mpr ⟨Hmem.1,
      bv_rw'' (ϕ := fun ρ => ⨆ a, ⨆ b, z =ᴮ pair a b ⊓ P ρ a b)
        (inf_le_left.trans H) Hmem.2 (hParam z)⟩
  · apply le_iInf
    intro z
    rw [← deduction]
    have Hmem := (mem_comprehend_and (hExt τ)).mp
      (show Γ ⊓ z ∈ᴮ comprehend (fun w => ⨆ a, ⨆ b, w =ᴮ pair a b ⊓ P τ a b) (prod A B) ≤
        z ∈ᴮ comprehend (fun w => ⨆ a, ⨆ b, w =ᴮ pair a b ⊓ P τ a b) (prod A B)
        from inf_le_right)
    exact (mem_comprehend_and (hExt σ)).mpr ⟨Hmem.1,
      bv_rw'' (ϕ := fun ρ => ⨆ a, ⨆ b, z =ᴮ pair a b ⊓ P ρ a b)
        (inf_le_left.trans (bv_symm H)) Hmem.2 (hParam z)⟩

theorem rowHistory_congr_row (δ X : bSet 𝔹) : B_congr (rowHistory δ X) :=
  relationGraph_param_congr (fun σ j v => pair (pair j σ) v ∈ᴮ X)
    (rowHistory_ext_row X)

end bSet.ErdosSimultaneousTraces
