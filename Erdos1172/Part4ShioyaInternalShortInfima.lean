/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalBoundedFunctionValue

@[expose] public section

/-! # Short descending sequences and their greatest lower bounds in the Boolean universe -/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
open Lattice
universe u
namespace bSet.ErdosShioyaInternal
open ErdosRelationGraph
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- Quantify over all values of a mixed graph on the named domain. -/
def rowForall (D F : bSet B) (test : bSet B → B) : B :=
  ⨅ i : bSet B, ⨅ x : bSet B, _root_.imp ((i ∈ᴮ D) ⊓ (pair i x ∈ᴮ F)) (test x)

theorem rowForall_iff {D F : bSet B} {test : bSet B → B} {Γ : B} :
    Γ ≤ rowForall D F test ↔ ∀ (i x : bSet B) (Δ : B), Δ ≤ Γ → Δ ≤ i ∈ᴮ D →
      Δ ≤ pair i x ∈ᴮ F → Δ ≤ test x := by
  constructor
  · intro h i x Δ hd hi hx
    exact (le_inf (hd.trans (h.trans (iInf_le _ i) |>.trans (iInf_le _ x))) (le_inf hi hx)).trans bv_imp_elim
  · intro h
    apply le_iInf
    intro i
    apply le_iInf
    intro x
    rw [← deduction]
    exact h i x _ inf_le_left (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)

def descendingValue (D F R : bSet B) : B :=
  ⨅ i : bSet B, ⨅ j : bSet B, ⨅ x : bSet B, ⨅ y : bSet B,
    _root_.imp (((i ∈ᴮ D ⊓ j ∈ᴮ D) ⊓ i ∈ᴮ j) ⊓ ((pair i x ∈ᴮ F) ⊓ (pair j y ∈ᴮ F))) (pair y x ∈ᴮ R)

def lowerBoundValue (D F R p : bSet B) : B := rowForall D F (fun x => pair p x ∈ᴮ R)

def glbValue (D F P R p : bSet B) : B :=
  ((p ∈ᴮ P) ⊓ lowerBoundValue D F R p) ⊓
    ⨅ t : bSet B, _root_.imp ((t ∈ᴮ P) ⊓ lowerBoundValue D F R t) (pair t p ∈ᴮ R)

/-- The bound, ordinal domain, function, order relation, and GLB are all names. An empty
domain requires a greatest point of the named poset. -/
def shortInfimaValue (K P R : bSet B) : B :=
  ⨅ D : bSet B, ⨅ F : bSet B, _root_.imp (((D ∈ᴮ K) ⊓ is_function D P F) ⊓ descendingValue D F R)
    (⨆ p : bSet B, glbValue D F P R p)

private theorem row_ext {D F : bSet B} (test : bSet B → bSet B → B) (h : ∀ y, B_ext (fun x => test x y)) :
    B_ext (fun x => rowForall D F (test x)) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun y => B_ext_imp (h₁ := B_ext_const) (h₂ := h y)))

theorem glbValue_ext_point (D F P R : bSet B) : B_ext (glbValue D F P R) :=
  B_ext_inf (B_ext_inf B_ext_mem_left (row_ext _ (fun _ => B_ext_pair_mem_left)))
    (B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_pair_mem_right)))

private theorem lower_ext_graph (D R p : bSet B) : B_ext (fun F => lowerBoundValue D F R p) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_imp (h₁ := B_ext_inf B_ext_const B_ext_mem_right) (h₂ := B_ext_const)))

theorem glbValue_ext_graph (D P R p : bSet B) : B_ext (fun F => glbValue D F P R p) :=
  B_ext_inf (B_ext_inf B_ext_const (lower_ext_graph D R p)) (B_ext_iInf (h := fun t =>
    B_ext_imp (h₁ := B_ext_inf B_ext_const (lower_ext_graph D R t)) (h₂ := B_ext_const)))

private theorem glb_ext_rel (D F P p : bSet B) : B_ext (fun R => glbValue D F P R p) :=
  B_ext_inf (B_ext_inf B_ext_const (row_ext _ (fun _ => B_ext_mem_right)))
    (B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_inf B_ext_const (row_ext _ (fun _ => B_ext_mem_right)))
      (h₂ := B_ext_mem_right)))

private theorem glb_ext_set (D F R p : bSet B) : B_ext (fun P => glbValue D F P R p) :=
  B_ext_inf (B_ext_inf B_ext_mem_right B_ext_const)
    (B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_inf B_ext_mem_right B_ext_const) (h₂ := B_ext_const)))

theorem shortInfimaValue_ext_bound (P R : bSet B) : B_ext (fun K => shortInfimaValue K P R) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_imp (h₁ := B_ext_inf (B_ext_inf B_ext_mem_right B_ext_const) B_ext_const) (h₂ := B_ext_const)))

theorem shortInfimaValue_ext_order (K P : bSet B) : B_ext (shortInfimaValue K P) := by
  apply B_ext_iInf (h := fun D => B_ext_iInf (h := fun F => B_ext_imp (h₂ := B_ext_iSup (h := glb_ext_rel D F P))
    (h₁ := B_ext_inf B_ext_const ?_)))
  exact B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_mem_right)))))

private theorem function_ext_range (D F : bSet B) : B_ext (fun P => is_function D P F) :=
  B_ext_inf (B_ext_inf B_ext_const (B_ext_iInf (h := fun _ =>
    B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_iSup (h := fun _ => B_ext_inf B_ext_mem_right B_ext_const)))))
    (B_ext_term (fun a => F ⊆ᴮ a) (fun P => prod D P) B_ext_subset_right B_congr_prod_right)

theorem shortInfimaValue_ext_carrier (K R : bSet B) : B_ext (fun P => shortInfimaValue K P R) :=
  B_ext_iInf (h := fun D => B_ext_iInf (h := fun F => B_ext_imp
    (h₁ := B_ext_inf (B_ext_inf B_ext_const (function_ext_range D F)) B_ext_const)
    (h₂ := B_ext_iSup (h := glb_ext_set D F R))))

theorem shortInfimaValue_iff {K P R : bSet B} {Γ : B} :
    Γ ≤ shortInfimaValue K P R ↔ ∀ (D F : bSet B) (Δ : B), Δ ≤ Γ → Δ ≤ D ∈ᴮ K →
      Δ ≤ is_function D P F → Δ ≤ descendingValue D F R → ∃ p : bSet B, Δ ≤ glbValue D F P R p := by
  constructor
  · intro h D F Δ hd hD hf hdesc
    have hex := (le_inf (hd.trans (h.trans (iInf_le _ D) |>.trans (iInf_le _ F)))
      (le_inf (le_inf hD hf) hdesc)).trans bv_imp_elim
    exact exists_convert hex (glbValue_ext_point D F P R)
  · intro h
    apply le_iInf
    intro D
    apply le_iInf
    intro F
    rw [← deduction]
    obtain ⟨p,hp⟩ := h D F _ inf_le_left (inf_le_right.trans (inf_le_left.trans inf_le_left))
      (inf_le_right.trans (inf_le_left.trans inf_le_right)) (inf_le_right.trans inf_le_right)
    exact le_iSup_of_le p hp

/-- The subset relation on the entire internal powerset, including all mixed subsets. -/
def subsetOrder (X : bSet B) : bSet B :=
  relationGraph (bv_powerset X) (bv_powerset X) (fun x y => x ⊆ᴮ y)

theorem subsetOrder_iff {X p q : bSet B} {Γ : B} : Γ ≤ pair p q ∈ᴮ subsetOrder X ↔
    Γ ≤ p ∈ᴮ bv_powerset X ∧ Γ ≤ q ∈ᴮ bv_powerset X ∧ Γ ≤ p ⊆ᴮ q :=
  mem_relationGraph_iff (fun _ => B_ext_subset_left) (fun _ => B_ext_subset_right)

def rowIntersection (X D F : bSet B) : bSet B :=
  comprehend (fun w => rowForall D F (fun p => w ∈ᴮ p)) X

theorem mem_rowIntersection_iff {X D F z : bSet B} {Γ : B} : Γ ≤ z ∈ᴮ rowIntersection X D F ↔
    Γ ≤ z ∈ᴮ X ∧ Γ ≤ rowForall D F (fun p => z ∈ᴮ p) :=
  mem_comprehend_and (row_ext _ (fun _ => B_ext_mem_left))

/-- Separation realizes a greatest lower bound even for a graph with a mixed domain and mixed values. -/
theorem rowIntersection_glb (X D F : bSet B) {Γ : B} (hf : Γ ≤ is_function D (bv_powerset X) F) :
    Γ ≤ glbValue D F (bv_powerset X) (subsetOrder X) (rowIntersection X D F) := by
  let t := rowIntersection X D F
  have ht : Γ ≤ t ∈ᴮ bv_powerset X := mem_powerset_iff.mpr
    (comprehend_subset (ϕ := fun w => rowForall D F (fun p => w ∈ᴮ p)) X)
  refine le_inf (le_inf ht (rowForall_iff.mpr ?_)) ?_
  · intro i x Δ hd hi hx
    have hp := mem_of_mem_subset (hd.trans (subset_prod_of_is_function hf)) hx
    apply subsetOrder_iff.mpr ⟨hd.trans ht,(mem_prod_iff.mp hp).2,?_⟩
    rw [subset_unfold']
    apply le_iInf
    intro z
    rw [← deduction]
    exact rowForall_iff.mp ((mem_rowIntersection_iff.mp inf_le_right).2) i x _ le_rfl
      (inf_le_left.trans hi) (inf_le_left.trans hx)
  · apply le_iInf
    intro y
    rw [← deduction]
    have hy := inf_le_right (a := Γ) (b := (y ∈ᴮ bv_powerset X) ⊓ lowerBoundValue D F (subsetOrder X) y)
    apply subsetOrder_iff.mpr ⟨hy.trans inf_le_left,inf_le_left.trans ht,?_⟩
    rw [subset_unfold']
    apply le_iInf
    intro z
    rw [← deduction]
    apply mem_rowIntersection_iff.mpr
    refine ⟨mem_of_mem_subset (inf_le_left.trans (mem_powerset_iff.mp (hy.trans inf_le_left))) inf_le_right,
      rowForall_iff.mpr ?_⟩
    intro i x Δ hd hi hx
    have ho := rowForall_iff.mp (hy.trans inf_le_right) i x Δ (hd.trans inf_le_left) hi hx
    exact mem_of_mem_subset (subsetOrder_iff.mp ho).2.2 (hd.trans inf_le_right)

theorem powerset_shortInfima (K X : bSet B) : shortInfimaValue K (bv_powerset X) (subsetOrder X) = ⊤ :=
  top_unique (shortInfimaValue_iff.mpr fun D F _ _ _ hf _ => ⟨_,rowIntersection_glb X D F hf⟩)

theorem fullRelation_shortInfima (K P p : bSet B) {Γ : B} (hp : Γ ≤ p ∈ᴮ P) :
    Γ ≤ shortInfimaValue K P (prod P P) := by
  apply shortInfimaValue_iff.mpr
  intro D F Δ hd _ hf _
  refine ⟨p,le_inf (le_inf (hd.trans hp) (rowForall_iff.mpr ?_)) ?_⟩
  · intro i y b hb _ hy
    have h := mem_of_mem_subset (hb.trans (subset_prod_of_is_function hf)) hy
    exact mem_prod_iff.mpr ⟨hb.trans (hd.trans hp),(mem_prod_iff.mp h).2⟩
  · apply le_iInf
    intro t
    rw [← deduction]
    exact mem_prod_iff.mpr ⟨inf_le_right.trans inf_le_left,inf_le_left.trans (hd.trans hp)⟩

theorem singleton_shortInfima (K x : bSet B) :
    shortInfimaValue K ({x} : bSet B) (prod {x} {x}) = ⊤ :=
  top_unique (fullRelation_shortInfima K {x} x mem_singleton)

end bSet.ErdosShioyaInternal
