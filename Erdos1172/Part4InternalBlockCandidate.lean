/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCanonicalBlockNonempty
public import Erdos1172.Part4InternalOneBlockExtension

@[expose] public section

/-!
# Exact whole-object block candidates

The candidate predicate retains the whole earlier block objects, their
fixed selected enumeration graphs, and the whole active point set. It
requires global ordinal separation, co-large opposite-color cross rows,
and opposite-color adjacency from all active points.

All extensionality results are unconditional. The co-large cross-row
witness can be selected at the original Boolean condition. No candidate
existence, selector, recursion, or fusion conclusion is asserted here.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosBlockCandidate

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosIdeal ErdosColargeIntersection ErdosCanonicalBlocks

def objectsBefore (Earlier A : bSet 𝔹) : 𝔹 :=
  ⨅ B, ⨅ x, ⨅ y, _root_.imp (B ∈ᴮ Earlier ⊓ (x ∈ᴮ B ⊓ y ∈ᴮ A)) (x ∈ᴮ y)

def rowCross (color : Bool) (R r C A : bSet 𝔹) : 𝔹 :=
  ⨅ i, ⨅ x, ⨅ y, _root_.imp (i ∈ᴮ C ⊓ (pair i x ∈ᴮ r ⊓ y ∈ᴮ A))
    (graphColor (!color) R x y)

def oldRowsCompatible (color : Bool) (R J E Earlier A : bSet 𝔹) : 𝔹 :=
  ⨅ B, ⨅ r, _root_.imp (B ∈ᴮ Earlier ⊓ pair B r ∈ᴮ E)
    (⨆ C, colarge omegaOne J C ⊓ rowCross color R r C A)

def activeCompatible (color : Bool) (R Active A : bSet 𝔹) : 𝔹 :=
  ⨅ x, ⨅ y, _root_.imp (x ∈ᴮ Active ⊓ y ∈ᴮ A) (graphColor (!color) R x y)

def blockCandidate (color : Bool) (R J E S Earlier Active A : bSet 𝔹) : 𝔹 :=
  A ∈ᴮ blockObjects color R ⊓
    (A ⊆ᴮ S ⊓ (objectsBefore Earlier A ⊓
      (oldRowsCompatible color R J E Earlier A ⊓ activeCompatible color R Active A)))

theorem objectsBefore_ext_object (Earlier : bSet 𝔹) : B_ext (objectsBefore Earlier) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_imp (h₁ := B_ext_inf B_ext_const (B_ext_inf B_ext_const B_ext_mem_right))
      (h₂ := B_ext_const))))

theorem objectsBefore_ext_earlier (A : bSet 𝔹) : B_ext (fun Earlier => objectsBefore Earlier A) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_imp (h₁ := B_ext_inf B_ext_mem_right B_ext_const) (h₂ := B_ext_const))))

theorem rowCross_ext_object (color : Bool) (R r C : bSet 𝔹) :
    B_ext (rowCross color R r C) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_imp (h₁ := B_ext_inf B_ext_const (B_ext_inf B_ext_const B_ext_mem_right))
      (h₂ := B_ext_const))))

theorem rowCross_ext_common (color : Bool) (R r A : bSet 𝔹) :
    B_ext (fun C => rowCross color R r C A) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_imp (h₁ := B_ext_inf B_ext_mem_right B_ext_const) (h₂ := B_ext_const))))

theorem rowCross_ext_row (color : Bool) (R C A : bSet 𝔹) :
    B_ext (fun r => rowCross color R r C A) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_imp (h₁ := B_ext_inf B_ext_const (B_ext_inf B_ext_mem_right B_ext_const))
      (h₂ := B_ext_const))))

theorem colarge_ext_common (κ J : bSet 𝔹) : B_ext (colarge κ J) :=
  B_ext_inf B_ext_subset_left
    (B_ext_term (ϕ := fun D => D ∈ᴮ J) (t := difference κ)
      B_ext_mem_left (B_congr_difference_right κ))

theorem oldRowsCompatible_ext_object (color : Bool) (R J E Earlier : bSet 𝔹) :
    B_ext (oldRowsCompatible color R J E Earlier) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun r =>
    B_ext_imp (h₁ := B_ext_const)
      (h₂ := B_ext_iSup (h := fun C => B_ext_inf B_ext_const
        (rowCross_ext_object color R r C)))))

theorem oldRowsCompatible_ext_earlier (color : Bool) (R J E A : bSet 𝔹) :
    B_ext (fun Earlier => oldRowsCompatible color R J E Earlier A) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_imp (h₁ := B_ext_inf B_ext_mem_right B_ext_const) (h₂ := B_ext_const)))

theorem activeCompatible_ext_object (color : Bool) (R Active : bSet 𝔹) :
    B_ext (activeCompatible color R Active) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_imp (h₁ := B_ext_inf B_ext_const B_ext_mem_right) (h₂ := B_ext_const)))

theorem activeCompatible_ext_active (color : Bool) (R A : bSet 𝔹) :
    B_ext (fun Active => activeCompatible color R Active A) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_imp (h₁ := B_ext_inf B_ext_mem_right B_ext_const) (h₂ := B_ext_const)))

theorem blockCandidate_ext_object (color : Bool) (R J E S Earlier Active : bSet 𝔹) :
    B_ext (blockCandidate color R J E S Earlier Active) :=
  B_ext_inf B_ext_mem_left (B_ext_inf B_ext_subset_left
    (B_ext_inf (objectsBefore_ext_object Earlier)
      (B_ext_inf (oldRowsCompatible_ext_object color R J E Earlier)
        (activeCompatible_ext_object color R Active))))

theorem blockCandidate_ext_earlier (color : Bool) (R J E S Active A : bSet 𝔹) :
    B_ext (fun Earlier => blockCandidate color R J E S Earlier Active A) :=
  B_ext_inf B_ext_const (B_ext_inf B_ext_const
    (B_ext_inf (objectsBefore_ext_earlier A)
      (B_ext_inf (oldRowsCompatible_ext_earlier color R J E A) B_ext_const)))

theorem blockCandidate_ext_active (color : Bool) (R J E S Earlier A : bSet 𝔹) :
    B_ext (fun Active => blockCandidate color R J E S Earlier Active A) :=
  B_ext_inf B_ext_const (B_ext_inf B_ext_const
    (B_ext_inf B_ext_const (B_ext_inf B_ext_const (activeCompatible_ext_active color R A))))

theorem objectsBefore_apply {Earlier A B x y : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ objectsBefore Earlier A) (HB : Γ ≤ B ∈ᴮ Earlier)
    (Hx : Γ ≤ x ∈ᴮ B) (Hy : Γ ≤ y ∈ᴮ A) : Γ ≤ x ∈ᴮ y :=
  (le_inf (H.trans ((iInf_le _ B).trans ((iInf_le _ x).trans (iInf_le _ y))))
    (le_inf HB (le_inf Hx Hy))).trans bv_imp_elim

theorem rowCross_apply {color : Bool} {R r C A i x y : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ rowCross color R r C A) (Hi : Γ ≤ i ∈ᴮ C)
    (Hix : Γ ≤ pair i x ∈ᴮ r) (Hy : Γ ≤ y ∈ᴮ A) :
    Γ ≤ graphColor (!color) R x y :=
  (le_inf (H.trans ((iInf_le _ i).trans ((iInf_le _ x).trans (iInf_le _ y))))
    (le_inf Hi (le_inf Hix Hy))).trans bv_imp_elim

theorem oldRowsCompatible_apply
    {color : Bool} {R J E Earlier A B r : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ oldRowsCompatible color R J E Earlier A)
    (HB : Γ ≤ B ∈ᴮ Earlier) (HBr : Γ ≤ pair B r ∈ᴮ E) :
    Γ ≤ ⨆ C, colarge omegaOne J C ⊓ rowCross color R r C A :=
  (le_inf (H.trans ((iInf_le _ B).trans (iInf_le _ r))) (le_inf HB HBr)).trans bv_imp_elim

/-- Fullness keeps the original condition while selecting the co-large
subset belonging to this same fixed ideal and this selected old row. -/
theorem oldRowsCompatible_witness
    {color : Bool} {R J E Earlier A B r : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ oldRowsCompatible color R J E Earlier A)
    (HB : Γ ≤ B ∈ᴮ Earlier) (HBr : Γ ≤ pair B r ∈ᴮ E) :
    ∃ C : bSet 𝔹, Γ ≤ colarge omegaOne J C ∧ Γ ≤ rowCross color R r C A := by
  obtain ⟨C, HC⟩ := exists_convert (oldRowsCompatible_apply H HB HBr)
    (B_ext_inf (colarge_ext_common omegaOne J) (rowCross_ext_common color R r A))
  exact ⟨C, HC.trans inf_le_left, HC.trans inf_le_right⟩

theorem activeCompatible_apply {color : Bool} {R Active A x y : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ activeCompatible color R Active A)
    (Hx : Γ ≤ x ∈ᴮ Active) (Hy : Γ ≤ y ∈ᴮ A) : Γ ≤ graphColor (!color) R x y :=
  (le_inf (H.trans ((iInf_le _ x).trans (iInf_le _ y))) (le_inf Hx Hy)).trans bv_imp_elim

theorem blockCandidate_object {color : Bool} {R J E S Earlier Active A : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ blockCandidate color R J E S Earlier Active A) :
    Γ ≤ A ∈ᴮ blockObjects color R := H.trans inf_le_left

theorem blockCandidate_subset {color : Bool} {R J E S Earlier Active A : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ blockCandidate color R J E S Earlier Active A) : Γ ≤ A ⊆ᴮ S :=
  H.trans (inf_le_right.trans inf_le_left)

theorem blockCandidate_before {color : Bool} {R J E S Earlier Active A : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ blockCandidate color R J E S Earlier Active A) : Γ ≤ objectsBefore Earlier A :=
  H.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))

theorem blockCandidate_oldRows {color : Bool} {R J E S Earlier Active A : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ blockCandidate color R J E S Earlier Active A) :
    Γ ≤ oldRowsCompatible color R J E Earlier A :=
  H.trans (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))

theorem blockCandidate_active {color : Bool} {R J E S Earlier Active A : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ blockCandidate color R J E S Earlier Active A) :
    Γ ≤ activeCompatible color R Active A :=
  H.trans (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))

theorem blockCandidate_nonempty {color : Bool} {R J E S Earlier Active A : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ blockCandidate color R J E S Earlier Active A) : Γ ≤ (A =ᴮ ∅)ᶜ :=
  blockObject_nonempty (blockCandidate_object H)

theorem blockCandidate_of_data {color : Bool} {R J E S Earlier Active A : bSet 𝔹} {Γ : 𝔹}
    (Hobject : Γ ≤ A ∈ᴮ blockObjects color R) (Hsub : Γ ≤ A ⊆ᴮ S)
    (Hbefore : Γ ≤ objectsBefore Earlier A)
    (Hold : Γ ≤ oldRowsCompatible color R J E Earlier A)
    (Hactive : Γ ≤ activeCompatible color R Active A) :
    Γ ≤ blockCandidate color R J E S Earlier Active A :=
  le_inf Hobject (le_inf Hsub (le_inf Hbefore (le_inf Hold Hactive)))

end bSet.ErdosBlockCandidate
