/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalDenseBasisCore
public import Erdos1172.Part4InternalGraphNeighborhood
public import Erdos1172.Part4InternalRelationGraph

@[expose] public section

/-!
Forward colored sections of an actual internal row relation, and their
coherent powerset-valued family. Membership records both strict order and
the edge color. All names and Boolean contexts remain arbitrary.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosForwardSections

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosIdeal ErdosDenseBasis ErdosRelationGraph

def forwardSection (color : Bool) (R r y : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun i => ⨆ x, pair i x ∈ᴮ r ⊓
    (x ∈ᴮ y ⊓ graphColor color R x y)) omegaOne

private theorem section_predicate_ext_index (color : Bool) (R r y : bSet 𝔹) :
    B_ext (fun i => ⨆ x, pair i x ∈ᴮ r ⊓
      (x ∈ᴮ y ⊓ graphColor color R x y)) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_pair_mem_left B_ext_const)

private theorem section_predicate_ext_endpoint (color : Bool) (R r i : bSet 𝔹) :
    B_ext (fun y => ⨆ x, pair i x ∈ᴮ r ⊓
      (x ∈ᴮ y ⊓ graphColor color R x y)) :=
  B_ext_iSup (h := fun x => B_ext_inf B_ext_const
    (B_ext_inf B_ext_mem_right (graphColor_ext_right color R x)))

theorem mem_forwardSection_iff {color : Bool} {R r y i : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ i ∈ᴮ forwardSection color R r y ↔
      (Γ ≤ i ∈ᴮ omegaOne) ∧
        Γ ≤ ⨆ x, pair i x ∈ᴮ r ⊓ (x ∈ᴮ y ⊓ graphColor color R x y) :=
  mem_comprehend_and (section_predicate_ext_index color R r y)

/-- Exact Boolean membership, including the omega-one domain guard. -/
theorem mem_forwardSection (color : Bool) (R r y i : bSet 𝔹) :
    i ∈ᴮ forwardSection color R r y = (i ∈ᴮ omegaOne) ⊓
      (⨆ x, pair i x ∈ᴮ r ⊓ (x ∈ᴮ y ⊓ graphColor color R x y)) := by
  apply le_antisymm
  · have H := mem_forwardSection_iff.mp
      (le_refl (i ∈ᴮ forwardSection color R r y))
    exact le_inf H.1 H.2
  · exact mem_forwardSection_iff.mpr ⟨inf_le_left, inf_le_right⟩

theorem forwardSection_subset {color : Bool} {R r y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ forwardSection color R r y ⊆ᴮ omegaOne :=
  comprehend_subset (ϕ := fun i => ⨆ x, pair i x ∈ᴮ r ⊓
    (x ∈ᴮ y ⊓ graphColor color R x y)) omegaOne

theorem forwardSection_congr (color : Bool) (R r : bSet 𝔹) :
    B_congr (forwardSection color R r) := by
  intro y₁ y₂ Γ H
  apply mem_ext
  · apply le_iInf
    intro i
    rw [← deduction]
    have Hi := mem_forwardSection_iff.mp
      (show Γ ⊓ i ∈ᴮ forwardSection color R r y₁ ≤
        i ∈ᴮ forwardSection color R r y₁ from inf_le_right)
    exact mem_forwardSection_iff.mpr ⟨Hi.1,
      bv_rw'' (ϕ := fun y => ⨆ x, pair i x ∈ᴮ r ⊓
        (x ∈ᴮ y ⊓ graphColor color R x y))
        (inf_le_left.trans H) Hi.2 (section_predicate_ext_endpoint color R r i)⟩
  · apply le_iInf
    intro i
    rw [← deduction]
    have Hi := mem_forwardSection_iff.mp
      (show Γ ⊓ i ∈ᴮ forwardSection color R r y₂ ≤
        i ∈ᴮ forwardSection color R r y₂ from inf_le_right)
    exact mem_forwardSection_iff.mpr ⟨Hi.1,
      bv_rw' (ϕ := fun y => ⨆ x, pair i x ∈ᴮ r ⊓
        (x ∈ᴮ y ⊓ graphColor color R x y))
        (inf_le_left.trans H) (h_congr := section_predicate_ext_endpoint color R r i)
        (H_new := Hi.2)⟩

/-- Fullness selects one actual row value, retaining the original context. -/
theorem exists_forwardSection_value {color : Bool} {R r y i : bSet 𝔹} {Γ : 𝔹}
    (Hi : Γ ≤ i ∈ᴮ forwardSection color R r y) :
    ∃ x : bSet 𝔹, (Γ ≤ pair i x ∈ᴮ r) ∧
      (Γ ≤ x ∈ᴮ y) ∧ Γ ≤ graphColor color R x y := by
  obtain ⟨x, Hx⟩ := exists_convert (mem_forwardSection_iff.mp Hi).2
    (B_ext_inf B_ext_pair_mem_right
      (B_ext_inf B_ext_mem_left (graphColor_ext_left color R y)))
  exact ⟨x, Hx.trans inf_le_left, Hx.trans (inf_le_right.trans inf_le_left),
    Hx.trans (inf_le_right.trans inf_le_right)⟩

/-- Single-valuedness transfers the forward edge to any known row pair.
Totality and injectivity are unnecessary for this particular implication. -/
theorem forwardSection_value_of_pair {color : Bool} {R r y i x : bSet 𝔹} {Γ : 𝔹}
    (Hfunc : Γ ≤ is_func r) (Hi : Γ ≤ i ∈ᴮ forwardSection color R r y)
    (Hix : Γ ≤ pair i x ∈ᴮ r) :
    Γ ≤ x ∈ᴮ y ⊓ graphColor color R x y := by
  obtain ⟨z, Hiz, Hzy, Hcolor⟩ := exists_forwardSection_value Hi
  have Hxz : Γ ≤ x =ᴮ z := eq_of_is_func_of_eq Hfunc bv_refl Hix Hiz
  exact bv_rw' (ϕ := fun v => v ∈ᴮ y ⊓ graphColor color R v y) Hxz
    (h_congr := B_ext_inf B_ext_mem_left (graphColor_ext_left color R y))
    (H_new := le_inf Hzy Hcolor)

theorem mem_forwardSection_of_pair {color : Bool} {R r y i x : bSet 𝔹} {Γ : 𝔹}
    (Hi : Γ ≤ i ∈ᴮ omegaOne) (Hix : Γ ≤ pair i x ∈ᴮ r)
    (Hxy : Γ ≤ x ∈ᴮ y) (Hcolor : Γ ≤ graphColor color R x y) :
    Γ ≤ i ∈ᴮ forwardSection color R r y :=
  mem_forwardSection_iff.mpr
    ⟨Hi, le_iSup_of_le x (le_inf Hix (le_inf Hxy Hcolor))⟩

def sectionFamily (color : Bool) (R r S F : bSet 𝔹) : 𝔹 :=
  ⨅ y, ⨅ A, _root_.imp (y ∈ᴮ S ⊓ pair y A ∈ᴮ F)
    (A =ᴮ forwardSection color R r y)

theorem sectionFamily_apply {color : Bool} {R r S F y A : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ sectionFamily color R r S F) (Hy : Γ ≤ y ∈ᴮ S)
    (HyA : Γ ≤ pair y A ∈ᴮ F) : Γ ≤ A =ᴮ forwardSection color R r y :=
  (le_inf (H.trans ((iInf_le _ y).trans (iInf_le _ A))) (le_inf Hy HyA)).trans
    bv_imp_elim

/-- Separation constructs the full coherent section function, rather than
assuming separately supplied witnesses for each endpoint. -/
theorem exists_forwardSection_family (color : Bool) (R r S : bSet 𝔹) {Γ : 𝔹} :
    ∃ F : bSet 𝔹, Γ ≤ is_function S (bv_powerset omegaOne) F ⊓
      sectionFamily color R r S F := by
  let P := fun y A : bSet 𝔹 => A =ᴮ forwardSection color R r y
  have hL : ∀ A, B_ext (fun y => P y A) := fun A =>
    B_ext_term (ϕ := fun X => A =ᴮ X) (t := forwardSection color R r)
      B_ext_bv_eq_right (forwardSection_congr color R r)
  have hR : ∀ y, B_ext (P y) := fun _ => B_ext_bv_eq_left
  let F := relationGraph S (bv_powerset omegaOne) P
  have Hfunction : Γ ≤ is_function S (bv_powerset omegaOne) F := by
    apply relationGraph_is_function (P := P) hL hR
    · apply le_iInf
      intro y
      rw [← deduction]
      exact le_iSup_of_le (forwardSection color R r y)
        (le_inf (mem_powerset_iff.mpr forwardSection_subset) bv_refl)
    · intro y₁ y₂ A₁ A₂ Δ _ _ _ _ _ H₁ H₂ Hyy
      exact bv_trans H₁
        (bv_trans (forwardSection_congr color R r Hyy) (bv_symm H₂))
  refine ⟨F, le_inf Hfunction ?_⟩
  apply le_iInf
  intro y
  apply le_iInf
  intro A
  rw [← deduction]
  exact ((mem_relationGraph_iff hL hR).mp
    (show Γ ⊓ (y ∈ᴮ S ⊓ pair y A ∈ᴮ F) ≤ pair y A ∈ᴮ F from
      inf_le_right.trans inf_le_right)).2.2

/-- Pointwise positive sections give the exact positive-value premise
required by the internal dense-basis centering theorem. -/
theorem positiveValues_of_sectionFamily
    {color : Bool} {R r S F J : bSet 𝔹} {Γ : 𝔹}
    (Hfamily : Γ ≤ sectionFamily color R r S F)
    (Hpositive : Γ ≤ ⨅ y, _root_.imp (y ∈ᴮ S)
      (positive omegaOne J (forwardSection color R r y))) :
    Γ ≤ positiveValues omegaOne J S F := by
  apply le_iInf
  intro y
  apply le_iInf
  intro A
  rw [← deduction]
  let Δ := Γ ⊓ (y ∈ᴮ S ⊓ pair y A ∈ᴮ F)
  have Heq : Δ ≤ A =ᴮ forwardSection color R r y :=
    sectionFamily_apply (inf_le_left.trans Hfamily)
      (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)
  have Hpos : Δ ≤ positive omegaOne J (forwardSection color R r y) :=
    (le_inf (inf_le_left.trans (Hpositive.trans (iInf_le _ y)))
      (inf_le_right.trans inf_le_left)).trans bv_imp_elim
  exact bv_rw' (ϕ := positive omegaOne J) Heq
    (h_congr := B_ext_inf B_ext_subset_left (B_ext_neg (h := B_ext_mem_left)))
    (H_new := Hpos)

end bSet.ErdosForwardSections
