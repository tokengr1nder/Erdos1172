/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
module

public import Erdos1172.Statement
public import Flypitch4.ZfcCore

@[expose] public section

/-!
The generic functional-relation and cardinal-comparison language is extracted
from `Flypitch4/Zfc.lean` at upstream commit
`ad649f89e9f3107b7e2ea97a58b2eafdfc80b815`, stopping before `CH_f`.
The source definitions and theorem statements are preserved. The final
namespace adds a parameterized least-noninjecting-ordinal formula and its
exact Boolean semantics; it does not assert existence or preservation.
-/

open Fol bSet

variable {β : Type 0} [NontrivialCompleteBooleanAlgebra β]

@[simp] lemma realize_is_func_f {f : V β} :
    boolean_realize_bounded_formula (DVec.cons f DVec.nil) is_func_f DVec.nil = is_func f := by
  simp only [is_func_f, is_func, boolean_realize_bounded_formula,
    boolean_realize_bounded_formula_and] ; rfl

@[simp] lemma realize_is_total'_f {x y f : V β} :
    boolean_realize_bounded_formula
      (DVec.cons f (DVec.cons y (DVec.cons x DVec.nil))) is_total'_f DVec.nil =
    is_total x y f := by
  simp only [is_total'_f, is_total, boolean_realize_bounded_formula,
    boolean_realize_bounded_formula_and, boolean_realize_bounded_formula_ex] ; rfl

def is_total'_f₂ : bounded_formula L_ZFC 3 :=
  bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
    (bd_ex (bd_and
      (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨4, by omega⟩))
      (mem' (pair' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)) (bd_var ⟨2, by omega⟩)))))

@[simp] lemma realize_is_total'_f₂ {x y f : V β} :
    boolean_realize_bounded_formula
      (DVec.cons f (DVec.cons y (DVec.cons x DVec.nil))) is_total'_f₂ DVec.nil =
    is_total y x f := by
  simp only [is_total'_f₂, is_total, boolean_realize_bounded_formula,
    boolean_realize_bounded_formula_and, boolean_realize_bounded_formula_ex] ; rfl

def is_func'_f₂ : bounded_formula L_ZFC 3 :=
  bd_and (is_func_f.cast (by omega)) is_total'_f₂

@[simp] lemma realize_is_func'_f {x y f : V β} :
    boolean_realize_bounded_formula
      (DVec.cons f (DVec.cons y (DVec.cons x DVec.nil))) is_func'_f DVec.nil =
    is_func' x y f := by
  simp only [is_func'_f, boolean_realize_bounded_formula_and]
  rw [boolean_realize_cast_bounded_formula (S := V β) (f := is_func_f)]
  exact congrArg₂ (fun a b : β => a ⊓ b)
    (realize_is_func_f (f := f)) (realize_is_total'_f (x := x) (y := y) (f := f))

@[simp] lemma realize_is_func'_f₂ {x y f : V β} :
    boolean_realize_bounded_formula
      (DVec.cons f (DVec.cons y (DVec.cons x DVec.nil))) is_func'_f₂ DVec.nil =
    is_func' y x f := by
  simp only [is_func'_f₂, boolean_realize_bounded_formula_and]
  rw [boolean_realize_cast_bounded_formula (S := V β) (f := is_func_f)]
  exact congrArg₂ (fun a b : β => a ⊓ b)
    (realize_is_func_f (f := f)) (realize_is_total'_f₂ (x := x) (y := y) (f := f))

/-- `at_most_f [y, x]` realizes `larger_than x y`: a subset of `x` surjects onto `y`.
The upstream prose comment reverses these arguments; the formula and theorem below are unchanged. -/
def at_most_f : bounded_formula L_ZFC 2 :=
  bd_ex (bd_ex
    (bd_and
      (bd_and
        (subset'' (bd_var ⟨1, by omega⟩) (bd_var ⟨3, by omega⟩))
        (is_func'_f₂.cast (by omega)))
      (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨3, by omega⟩))
        (bd_ex (bd_and
          (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨3, by omega⟩))
          (mem' (pair' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩)) (bd_var ⟨2, by omega⟩))))))))

@[simp] lemma realize_at_most_f {x y : V β} :
    boolean_realize_bounded_formula (DVec.cons y (DVec.cons x DVec.nil)) at_most_f DVec.nil =
    larger_than x y := by
  simp only [at_most_f, boolean_realize_bounded_formula_ex,
    boolean_realize_bounded_formula_and, larger_than]
  apply iSup_congr
  intro s
  apply iSup_congr
  intro f
  rw [boolean_realize_bounded_formula_subset' (β := β)
    (v := DVec.cons f (DVec.cons s (DVec.cons y (DVec.cons x DVec.nil))))
    (bd_var ⟨1, by omega⟩) (bd_var ⟨3, by omega⟩)]
  rw [boolean_realize_cast_bounded_formula (S := V β) (f := is_func'_f₂)]
  change (s ⊆ᴮ x ⊓
    boolean_realize_bounded_formula (S := V β)
      (DVec.cons f (DVec.cons s (DVec.cons y DVec.nil))) is_func'_f₂ DVec.nil) ⊓ _ = _
  rw [realize_is_func'_f₂ (x := y) (y := s) (f := f)]
  simp only [boolean_realize_bounded_formula, boolean_realize_bounded_formula_ex,
    boolean_realize_bounded_formula_and] ; rfl

@[simp] lemma realize_is_inj_f (f : V β) :
    boolean_realize_bounded_formula (DVec.cons f DVec.nil) is_inj_f DVec.nil = is_inj f := by
  simp only [is_inj_f, is_inj, boolean_realize_bounded_formula,
    boolean_realize_bounded_formula_and] ; rfl

@[simp] lemma realize_injects_into {x y : V β} :
    boolean_realize_bounded_formula (DVec.cons y (DVec.cons x DVec.nil)) injects_into_f DVec.nil =
    injects_into x y := by
  simp only [injects_into_f, boolean_realize_bounded_formula_ex,
    boolean_realize_bounded_formula_and, injects_into]
  apply iSup_congr
  intro f
  rw [boolean_realize_cast_bounded_formula (S := V β) (f := is_inj_f)]
  exact congrArg₂ (fun a b : β => a ⊓ b)
    (realize_is_func'_f (x := x) (y := y) (f := f)) (realize_is_inj_f f)

def non_empty_f : bounded_formula L_ZFC 1 := bd_not (bd_equal (bd_var ⟨0, by omega⟩) ∅')

@[simp] lemma non_empty_f_is_non_empty {x : V β} :
    boolean_realize_bounded_formula (DVec.cons x DVec.nil) non_empty_f DVec.nil = not_empty x := by
  simp only [non_empty_f, not_empty, boolean_realize_bounded_formula_not,
    boolean_realize_bounded_formula] ; rfl

namespace Erdos1172Part4InternalCardinalLanguage

/-- Exact Boolean interpretation of the two-parameter Hartogs specification. -/
theorem realize_least_noninjecting_ordinal_f {κ α : V β} :
    boolean_realize_bounded_formula (DVec.cons κ (DVec.cons α DVec.nil))
      least_noninjecting_ordinal_f DVec.nil =
    Ord α ⊓ ((injects_into α κ)ᶜ ⊓
      ⨅ γ : bSet β, _root_.imp (γ ∈ᴮ α) (injects_into γ κ)) := by
  have hOrd :
      boolean_realize_bounded_formula (S := V β)
        (DVec.cons κ (DVec.cons α DVec.nil)) (Ord_f ↑ᶠᵇ' 1 # 0) DVec.nil = Ord α := by
    exact (boolean_realize_bounded_formula_insert_lift (S := V β)
      (DVec.cons α DVec.nil) κ 0 (by omega) Ord_f DVec.nil).trans (Ord_f_is_Ord (x := α))
  have hsmall (γ : bSet β) :
      boolean_realize_bounded_formula (S := V β)
        (DVec.cons γ (DVec.cons κ (DVec.cons α DVec.nil)))
        (subst0_bounded_formula
          (injects_into_f.cast (by omega) : bounded_formula L_ZFC 4)
          (bd_var ⟨1, by omega⟩)) DVec.nil = injects_into γ κ := by
    rw [boolean_realize_subst_formula0 (V β)
      (injects_into_f.cast (by omega) : bounded_formula L_ZFC 4)
      (bd_var ⟨1, by omega⟩) (DVec.cons γ (DVec.cons κ (DVec.cons α DVec.nil)))]
    rw [boolean_realize_cast_bounded_formula (S := V β) (f := injects_into_f)]
    exact realize_injects_into (x := γ) (y := κ)
  simp only [least_noninjecting_ordinal_f, boolean_realize_bounded_formula_and,
    boolean_realize_bounded_formula_not]
  rw [hOrd, realize_injects_into (x := α) (y := κ)]
  apply congrArg (fun q : β => Ord α ⊓ ((injects_into α κ)ᶜ ⊓ q))
  change (⨅ γ : bSet β, _root_.imp (γ ∈ᴮ α)
    (boolean_realize_bounded_formula (S := V β)
      (DVec.cons γ (DVec.cons κ (DVec.cons α DVec.nil)))
      (subst0_bounded_formula
        (injects_into_f.cast (by omega) : bounded_formula L_ZFC 4)
        (bd_var ⟨1, by omega⟩)) DVec.nil)) = _
  apply iInf_congr
  intro γ
  exact congrArg (_root_.imp (γ ∈ᴮ α)) (hsmall γ)

end Erdos1172Part4InternalCardinalLanguage
