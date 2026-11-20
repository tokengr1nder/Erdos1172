/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaStringTransport

@[expose] public section

/-! # Surjections from local Boolean matrices

Each ordered pair of checked ordinal labels occurs in the graph with
its matrix coefficient. On any Boolean condition where rows and columns
cover and different entries of one row are disjoint, this graph is an
internal surjection on the indicated checked ordinals.
-/

set_option autoImplicit false
noncomputable section
open bSet bSet.ErdosNameTransport Lattice
open scoped Flypitch
universe u

namespace Erdos1172Shioya

open StringName
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B] (γ δ : Ordinal.{u})

def vertices (o : Ordinal.{u}) : bSet B := check'' (fun i : o.ToType => label i)

private theorem vertices_eq (o : Ordinal.{u}) : vertices (B := B) o = check (PSet.ordinalMk o) := by
  rw [PSet.ordinalMk_eq_def o, check_unfold]
  rfl

private theorem label_ne {o : Ordinal.{u}} {i k : o.ToType} (h : i ≠ k) :
    ((label i : bSet B) =ᴮ label k) = ⊥ :=
  check_bv_eq_bot_of_not_equiv fun e =>
    h (Ordinal.ToType.mk.symm.injective (Subtype.ext (PSet.eq_of_mk_equiv e)))

def matrixGraph (A : γ.ToType → δ.ToType → B) : bSet B :=
  .mk (γ.ToType × δ.ToType) (fun t => pair (label t.1) (label t.2)) (fun t => A t.1 t.2)

theorem matrixGraph_pair (A : γ.ToType → δ.ToType → B) (i : γ.ToType) (j : δ.ToType) :
    (pair (label i) (label j) ∈ᴮ matrixGraph γ δ A) = A i j := by
  rw [mem_unfold]
  change (⨆ t : γ.ToType × δ.ToType, A t.1 t.2 ⊓
    (pair (label i) (label j) =ᴮ pair (label t.1) (label t.2))) = _
  apply le_antisymm
  · apply iSup_le
    rintro ⟨k, l⟩
    by_cases hi : i = k
    · subst k
      by_cases hj : j = l
      · subst l
        exact inf_le_left
      · exact ((eq_of_eq_pair_right' inf_le_right).trans_eq (label_ne hj)).trans bot_le
    · exact ((eq_of_eq_pair_left' inf_le_right).trans_eq (label_ne hi)).trans bot_le
  · apply le_iSup_of_le (i, j)
    exact le_inf le_rfl bv_refl

variable (A : γ.ToType → δ.ToType → B) (Γ : B)

theorem matrixGraph_is_function (hrow : ∀ i, Γ ≤ ⨆ j, A i j)
    (hdisj : ∀ i j k, j ≠ k → Γ ⊓ (A i j ⊓ A i k) ≤ ⊥) :
    Γ ≤ is_function (check (PSet.ordinalMk γ)) (check (PSet.ordinalMk δ)) (matrixGraph γ δ A) := by
  rw [← vertices_eq γ, ← vertices_eq δ, is_function_eq_bounded]
  refine le_inf (le_inf ?_ ?_) ?_
  · apply le_iInf
    rintro ⟨i, j⟩
    apply le_iInf
    rintro ⟨k, l⟩
    change γ.ToType at i k
    change δ.ToType at j l
    change Γ ≤ _root_.imp (((⊤ ⊓ ⊤) ⊓ (⊤ ⊓ ⊤)) ⊓
      ((pair (label i) (label j) ∈ᴮ matrixGraph γ δ A) ⊓ (pair (label k) (label l) ∈ᴮ matrixGraph γ δ A)))
      (_root_.imp ((label i : bSet B) =ᴮ label k) (label j =ᴮ label l))
    simp only [matrixGraph_pair, top_inf_eq, ← deduction]
    by_cases hi : i = k
    · subst k
      by_cases hj : j = l
      · subst l
        exact bv_refl
      · exact (inf_le_left.trans (hdisj i j l hj)).trans bot_le
    · exact (inf_le_right.trans_eq (label_ne hi)).trans bot_le
  · apply le_iInf
    intro i
    change γ.ToType at i
    change Γ ≤ _root_.imp ⊤ (⨆ j : δ.ToType, ⊤ ⊓ (pair (label i) (label j) ∈ᴮ matrixGraph γ δ A))
    simpa only [top_imp, top_inf_eq, matrixGraph_pair] using hrow i
  · rw [subset_unfold]
    apply le_iInf
    rintro ⟨i, j⟩
    rw [← deduction]
    exact mem_prod (le_top.trans (mem_mk' (vertices γ) i)) (le_top.trans (mem_mk' (vertices δ) j))

theorem matrixGraph_is_surj (hcol : ∀ j, Γ ≤ ⨆ i, A i j) :
    Γ ≤ is_surj (check (PSet.ordinalMk γ)) (check (PSet.ordinalMk δ)) (matrixGraph γ δ A) := by
  rw [← vertices_eq γ, ← vertices_eq δ]
  unfold is_surj
  rw [← bounded_forall (h_congr := B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_pair_mem_right))]
  apply le_iInf
  intro j
  change δ.ToType at j
  change Γ ≤ _root_.imp ⊤ (⨆ w : bSet B, (w ∈ᴮ vertices γ) ⊓ (pair w (label j) ∈ᴮ matrixGraph γ δ A))
  rw [top_imp]
  apply (hcol j).trans
  apply iSup_le
  intro i
  apply le_iSup_of_le (label i)
  rw [matrixGraph_pair]
  exact le_inf (le_top.trans (mem_mk' (vertices γ) i)) le_rfl

theorem matrixGraph_surjection (hrow : ∀ i, Γ ≤ ⨆ j, A i j)
    (hcol : ∀ j, Γ ≤ ⨆ i, A i j) (hdisj : ∀ i j k, j ≠ k → Γ ⊓ (A i j ⊓ A i k) ≤ ⊥) :
    Γ ≤ is_function (check (PSet.ordinalMk γ)) (check (PSet.ordinalMk δ)) (matrixGraph γ δ A) ⊓
      is_surj (check (PSet.ordinalMk γ)) (check (PSet.ordinalMk δ)) (matrixGraph γ δ A) :=
  le_inf (matrixGraph_is_function γ δ A Γ hrow hdisj) (matrixGraph_is_surj γ δ A Γ hcol)

end Erdos1172Shioya
