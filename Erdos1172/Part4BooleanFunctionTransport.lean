/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanNameTransport

@[expose] public section

/-!
# Bounded transport of actual function graphs

An actual function is normalized to product-child functionality, bounded
totality, and graph support. These quantifiers range over the original
domain and codomain index types, so a complete Boolean homomorphism
preserves the exact value. Arbitrary target names are handled by the
product-membership Boolean sums in the normalization proof.

This proves transport of the supported function predicate, not unbounded
first-order elementarity or that all target names come from the source.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosNameTransport

variable {B C : Type u}
variable [NontrivialCompleteBooleanAlgebra B]
variable [NontrivialCompleteBooleanAlgebra C]

theorem map_empty (e : CompleteLatticeHom B C) :
    mapNames e (∅ : bSet B) = ∅ := by
  calc
    mapNames e (∅ : bSet B) = mapNames e (check (∅ : PSet.{u})) :=
      congrArg (mapNames e) check_empty_eq_empty.symm
    _ = check (∅ : PSet.{u}) := map_check e _
    _ = ∅ := check_empty_eq_empty

theorem map_insert1 (e : CompleteLatticeHom B C) (x y : bSet B) :
    mapNames e (bSet.insert1 x y) = bSet.insert1 (mapNames e x) (mapNames e y) := by
  cases y with
  | mk ι Y w =>
    simp only [bSet.insert1, bSet.insert, mapNames_mk]
    congr 1
    · funext i
      cases i <;> rfl
    · funext i
      cases i with
      | none => exact map_top e
      | some _ => rfl

theorem map_pair (e : CompleteLatticeHom B C) (x y : bSet B) :
    mapNames e (pair x y) = pair (mapNames e x) (mapNames e y) := by
  change mapNames e (bSet.insert1 (bSet.insert1 x ∅)
      (bSet.insert1 (bSet.insert1 x (bSet.insert1 y ∅)) ∅)) =
    bSet.insert1 (bSet.insert1 (mapNames e x) ∅)
      (bSet.insert1 (bSet.insert1 (mapNames e x) (bSet.insert1 (mapNames e y) ∅)) ∅)
  rw [map_insert1, map_insert1, map_insert1, map_insert1, map_insert1, map_empty]

theorem map_prod (e : CompleteLatticeHom B C) (x y : bSet B) :
    mapNames e (prod x y) = prod (mapNames e x) (mapNames e y) := by
  cases x with
  | mk ι X w =>
    cases y with
    | mk κ Y v =>
      simp only [prod, mapNames_mk, bSet.type, bSet.func, bSet.bval, map_pair, map_inf]

/-- Functionality quantified only over the two product-child index types.
The coefficient guards are essential, including for empty domains. -/
def boundedFunc (x y f : bSet B) : B :=
  ⨅ i : x.type × y.type, ⨅ j : x.type × y.type,
    _root_.imp
      (((x.bval i.1 ⊓ y.bval i.2) ⊓ (x.bval j.1 ⊓ y.bval j.2)) ⊓
        (pair (x.func i.1) (y.func i.2) ∈ᴮ f ⊓
          pair (x.func j.1) (y.func j.2) ∈ᴮ f))
      (_root_.imp (x.func i.1 =ᴮ x.func j.1) (y.func i.2 =ᴮ y.func j.2))

theorem boundedFunc_apply {x y f : bSet B} {Γ : B}
    (Hf : Γ ≤ boundedFunc x y f) (i j : x.type × y.type)
    (Hi : Γ ≤ x.bval i.1 ⊓ y.bval i.2)
    (Hj : Γ ≤ x.bval j.1 ⊓ y.bval j.2)
    (Hpi : Γ ≤ pair (x.func i.1) (y.func i.2) ∈ᴮ f)
    (Hpj : Γ ≤ pair (x.func j.1) (y.func j.2) ∈ᴮ f)
    (Hij : Γ ≤ x.func i.1 =ᴮ x.func j.1) :
    Γ ≤ y.func i.2 =ᴮ y.func j.2 := by
  have Hspec := Hf.trans ((iInf_le _ i).trans (iInf_le _ j))
  exact (le_inf ((le_inf Hspec (le_inf (le_inf Hi Hj) (le_inf Hpi Hpj))).trans
    bv_imp_elim) Hij).trans bv_imp_elim

theorem is_func_le_boundedFunc (x y f : bSet B) :
    is_func f ≤ boundedFunc x y f := by
  apply le_iInf
  intro i
  apply le_iInf
  intro j
  rw [← deduction, ← deduction]
  exact eq_of_is_func_of_eq (inf_le_left.trans inf_le_left) inf_le_right
    (inf_le_left.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))
    (inf_le_left.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))

/-- Product support reduces arbitrary mixed pairs to canonical product
children by distributing their membership sums, without choosing one child
at the unchanged condition. -/
theorem boundedFunc_eq_of_mem {x y f a b c d : bSet B} {Γ : B}
    (Hsub : Γ ≤ f ⊆ᴮ prod x y) (Hf : Γ ≤ boundedFunc x y f)
    (Hab : Γ ≤ pair a b ∈ᴮ f) (Hcd : Γ ≤ pair c d ∈ᴮ f)
    (Hac : Γ ≤ a =ᴮ c) : Γ ≤ b =ᴮ d := by
  have Habprod := mem_of_mem_subset Hsub Hab
  have Hcdprod := mem_of_mem_subset Hsub Hcd
  apply (le_inf le_rfl Habprod).trans
  rw [mem_unfold, inf_iSup_eq]
  apply iSup_le
  intro i
  change Γ ⊓ ((x.bval i.1 ⊓ y.bval i.2) ⊓
    (pair a b =ᴮ pair (x.func i.1) (y.func i.2))) ≤ b =ᴮ d
  apply (le_inf le_rfl (inf_le_left.trans Hcdprod)).trans
  rw [mem_unfold, inf_iSup_eq]
  apply iSup_le
  intro j
  let Δ := (Γ ⊓ ((x.bval i.1 ⊓ y.bval i.2) ⊓
    (pair a b =ᴮ pair (x.func i.1) (y.func i.2)))) ⊓
    ((x.bval j.1 ⊓ y.bval j.2) ⊓
      (pair c d =ᴮ pair (x.func j.1) (y.func j.2)))
  change Δ ≤ b =ᴮ d
  have HΓ : Δ ≤ Γ := inf_le_left.trans inf_le_left
  have Hi : Δ ≤ x.bval i.1 ⊓ y.bval i.2 :=
    inf_le_left.trans (inf_le_right.trans inf_le_left)
  have Hj : Δ ≤ x.bval j.1 ⊓ y.bval j.2 := inf_le_right.trans inf_le_left
  have Heqi : Δ ≤ pair a b =ᴮ pair (x.func i.1) (y.func i.2) :=
    inf_le_left.trans (inf_le_right.trans inf_le_right)
  have Heqj : Δ ≤ pair c d =ᴮ pair (x.func j.1) (y.func j.2) :=
    inf_le_right.trans inf_le_right
  have Hpi : Δ ≤ pair (x.func i.1) (y.func i.2) ∈ᴮ f :=
    bv_rw'' Heqi (HΓ.trans Hab) B_ext_mem_left
  have Hpj : Δ ≤ pair (x.func j.1) (y.func j.2) ∈ᴮ f :=
    bv_rw'' Heqj (HΓ.trans Hcd) B_ext_mem_left
  have Hdom : Δ ≤ x.func i.1 =ᴮ x.func j.1 :=
    bv_trans (bv_symm (eq_of_eq_pair_left' Heqi))
      (bv_trans (HΓ.trans Hac) (eq_of_eq_pair_left' Heqj))
  have Hval := boundedFunc_apply (HΓ.trans Hf) i j Hi Hj Hpi Hpj Hdom
  exact bv_trans (eq_of_eq_pair_right' Heqi)
    (bv_trans Hval (bv_symm (eq_of_eq_pair_right' Heqj)))

theorem is_func_of_boundedFunc {x y f : bSet B} {Γ : B}
    (Hsub : Γ ≤ f ⊆ᴮ prod x y) (Hf : Γ ≤ boundedFunc x y f) :
    Γ ≤ is_func f := by
  apply le_iInf
  intro a
  apply le_iInf
  intro c
  apply le_iInf
  intro b
  apply le_iInf
  intro d
  rw [← deduction, ← deduction]
  exact boundedFunc_eq_of_mem
    ((inf_le_left.trans inf_le_left).trans Hsub)
    ((inf_le_left.trans inf_le_left).trans Hf)
    (inf_le_left.trans (inf_le_right.trans inf_le_left))
    (inf_le_left.trans (inf_le_right.trans inf_le_right)) inf_le_right

theorem is_total_eq_is_total' (x y f : bSet B) :
    is_total x y f = is_total' x y f :=
  le_antisymm (is_total_iff_is_total'.mp le_rfl) (is_total_iff_is_total'.mpr le_rfl)

/-- Exact normalization includes the support guard rather than assuming it
at top or discarding off-product entries without justification. -/
theorem is_function_eq_bounded (x y f : bSet B) :
    is_function x y f =
      (boundedFunc x y f ⊓ is_total' x y f) ⊓ (f ⊆ᴮ prod x y) := by
  apply le_antisymm
  · refine le_inf (le_inf ?_ ?_) inf_le_right
    · exact (inf_le_left.trans inf_le_left).trans (is_func_le_boundedFunc x y f)
    · exact is_total_iff_is_total'.mp (inf_le_left.trans inf_le_right)
  · refine le_inf (le_inf ?_ ?_) inf_le_right
    · exact is_func_of_boundedFunc inf_le_right (inf_le_left.trans inf_le_left)
    · exact is_total_iff_is_total'.mpr (inf_le_left.trans inf_le_right)

theorem map_boundedFunc (e : CompleteLatticeHom B C) (x y f : bSet B) :
    e (boundedFunc x y f) = boundedFunc (mapNames e x) (mapNames e y) (mapNames e f) := by
  cases x with
  | mk ι X w =>
    cases y with
    | mk κ Y v =>
      simp only [boundedFunc, mapNames_mk, bSet.type, bSet.func, bSet.bval,
        map_iInf, map_imp, map_inf, map_mem, map_bv_eq, map_pair]

theorem map_is_total' (e : CompleteLatticeHom B C) (x y f : bSet B) :
    e (is_total' x y f) = is_total' (mapNames e x) (mapNames e y) (mapNames e f) := by
  cases x with
  | mk ι X w =>
    cases y with
    | mk κ Y v =>
      simp only [is_total', mapNames_mk, bSet.type, bSet.func, bSet.bval,
        map_iInf, map_iSup, map_imp, map_inf, map_mem, map_pair]

theorem map_is_total (e : CompleteLatticeHom B C) (x y f : bSet B) :
    e (is_total x y f) = is_total (mapNames e x) (mapNames e y) (mapNames e f) := by
  rw [is_total_eq_is_total', map_is_total', is_total_eq_is_total']

/-- Exact transport of the supported-function Boolean value, proved only
after bounded normalization. No surjectivity of the map on names is used. -/
theorem map_is_function (e : CompleteLatticeHom B C) (x y f : bSet B) :
    e (is_function x y f) =
      is_function (mapNames e x) (mapNames e y) (mapNames e f) := by
  calc
    e (is_function x y f) =
        e ((boundedFunc x y f ⊓ is_total' x y f) ⊓ (f ⊆ᴮ prod x y)) :=
      congrArg e (is_function_eq_bounded x y f)
    _ = (boundedFunc (mapNames e x) (mapNames e y) (mapNames e f) ⊓
        is_total' (mapNames e x) (mapNames e y) (mapNames e f)) ⊓
        (mapNames e f ⊆ᴮ prod (mapNames e x) (mapNames e y)) := by
      rw [map_inf, map_inf, map_boundedFunc, map_is_total', map_subset, map_prod]
    _ = is_function (mapNames e x) (mapNames e y) (mapNames e f) :=
      (is_function_eq_bounded _ _ _).symm

theorem map_is_function_of (e : CompleteLatticeHom B C)
    {x y f : bSet B} {Γ : B} (Hf : Γ ≤ is_function x y f) :
    e Γ ≤ is_function (mapNames e x) (mapNames e y) (mapNames e f) := by
  rw [← map_is_function]
  exact OrderHomClass.mono e Hf

theorem le_is_function_iff (e : CompleteLatticeHom B C) (he : Function.Injective e)
    (Γ : B) (x y f : bSet B) :
    Γ ≤ is_function x y f ↔
      e Γ ≤ is_function (mapNames e x) (mapNames e y) (mapNames e f) := by
  rw [← map_is_function]
  constructor
  · intro Hf
    exact OrderHomClass.mono e Hf
  · intro Hf
    have hmeet : Γ ⊓ is_function x y f = Γ :=
      he (by rw [map_inf, inf_eq_left.mpr Hf])
    exact inf_eq_left.mp hmeet

end bSet.ErdosNameTransport
