/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanFactorPoset
public import Erdos1172.Part4InternalIdealSemantics
public import Erdos1172.Part4InternalSmallPoolOperations
public import Erdos1172.Part4InternalRelationGraph

@[expose] public section

/-! # A seed-derived kernel as a name in the source Boolean universe

Given a map of names `j`, decide locally whether a target seed belongs to
`j X`. The complement of the lower projection is the largest source condition
on which this membership is impossible. Separation on the full internal
powerset constructs the kernel on arbitrary mixed subsets. The map of names
and its preservation laws are explicit parameters.
-/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
open Lattice
universe u

namespace bSet.ErdosSeedKernel

open Erdos1172BooleanFactor ErdosIdeal

variable {B C : Type u} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

def nullValue (e : CompleteLatticeHom B C) (j : bSet B → bSet C) (s : bSet C) (X : bSet B) : B :=
  (lowerProjection e (s ∈ᴮ j X))ᶜ

theorem le_nullValue_iff (e : CompleteLatticeHom B C) (j : bSet B → bSet C)
    (s : bSet C) (X : bSet B) (Γ : B) :
    Γ ≤ nullValue e j s X ↔ e Γ ⊓ (s ∈ᴮ j X) = ⊥ := by
  unfold nullValue
  rw [le_compl_comm, lowerProjection_le_iff, map_compl', le_compl_iff_disjoint_left, disjoint_iff]

def seedKernelName (e : CompleteLatticeHom B C) (j : bSet B → bSet C)
    (s : bSet C) (K : bSet B) : bSet B :=
  comprehend (nullValue e j s) (bv_powerset K)

variable (e : CompleteLatticeHom B C) (j : bSet B → bSet C) (s : bSet C)
variable (hEq : ∀ X Y, e (X =ᴮ Y) ≤ (j X =ᴮ j Y))

include hEq in
theorem nullValue_ext : B_ext (nullValue e j s) := by
  intro X Y
  let Γ := (X =ᴮ Y) ⊓ nullValue e j s X
  apply (le_nullValue_iff e j s Y Γ).mpr
  have hmem : e Γ ⊓ (s ∈ᴮ j Y) ≤ s ∈ᴮ j X := by
    apply bv_rw' (ϕ := fun a => s ∈ᴮ a) _ (h_congr := B_ext_mem_right) (H_new := inf_le_right)
    exact inf_le_left.trans ((OrderHomClass.mono e (show Γ ≤ (X =ᴮ Y) from inf_le_left)).trans (hEq X Y))
  have hnull := (le_nullValue_iff e j s X Γ).mp inf_le_right
  exact bot_unique ((le_inf inf_le_left hmem).trans_eq hnull)

include hEq in
theorem mem_seedKernelName_iff {X K : bSet B} {Γ : B} :
    Γ ≤ X ∈ᴮ seedKernelName e j s K ↔ Γ ≤ X ⊆ᴮ K ∧ e Γ ⊓ (s ∈ᴮ j X) = ⊥ := by
  unfold seedKernelName
  rw [ErdosRelationGraph.mem_comprehend_and (nullValue_ext e j s hEq), mem_powerset_iff,
    le_nullValue_iff]

theorem seedKernelName_subset_powerset (K : bSet B) {Γ : B} :
    Γ ≤ seedKernelName e j s K ⊆ᴮ bv_powerset K :=
  comprehend_subset (ϕ := nullValue e j s) (bv_powerset K)

include hEq in
theorem positive_seedKernelName (K X : bSet B) :
    positive K (seedKernelName e j s K) X = (X ⊆ᴮ K) ⊓ lowerProjection e (s ∈ᴮ j X) := by
  have hm : (X ∈ᴮ seedKernelName e j s K) = (X ⊆ᴮ K) ⊓ nullValue e j s X := by
    apply eq_of_forall_le_iff
    intro Γ
    rw [mem_seedKernelName_iff e j s hEq, le_inf_iff, le_nullValue_iff]
  unfold positive
  rw [hm, nullValue, compl_inf, compl_compl, inf_sup_left, inf_compl_eq_bot, bot_sup_eq]

include hEq in
theorem singleton_mem_seedKernelName {Γ : B} {K x : bSet B}
    (hx : Γ ≤ x ∈ᴮ K) (hSing : e Γ ≤ j {x} ⊆ᴮ ({j x} : bSet C))
    (hMiss : e Γ ≤ (s =ᴮ j x)ᶜ) : Γ ≤ ({x} : bSet B) ∈ᴮ seedKernelName e j s K := by
  apply (mem_seedKernelName_iff e j s hEq).mpr
  constructor
  · rw [subset_unfold']
    apply le_iInf; intro y
    rw [← deduction]
    exact subst_congr_mem_left' (eq_of_mem_singleton inf_le_right) (inf_le_left.trans hx)
  · apply bot_unique
    have hmem : e Γ ⊓ (s ∈ᴮ j {x}) ≤ s ∈ᴮ ({j x} : bSet C) :=
      mem_of_mem_subset (inf_le_left.trans hSing) inf_le_right
    exact bv_absurd _ (eq_mem_singleton hmem) (inf_le_left.trans hMiss)

include hEq in
theorem seedKernelName_properIdeal (he : Function.Injective e) (K : bSet B) {Γ : B}
    (hSeed : e Γ ≤ s ∈ᴮ j K)
    (hEmpty : (⊤ : C) ≤ j ∅ =ᴮ (∅ : bSet C))
    (hSub : ∀ X Y, e (X ⊆ᴮ Y) ≤ (j X ⊆ᴮ j Y))
    (hUnion : ∀ X Y, (⊤ : C) ≤ j (binary_union X Y) ⊆ᴮ binary_union (j X) (j Y)) :
    Γ ≤ properIdeal K (seedKernelName e j s K) := by
  let J := seedKernelName e j s K
  have hmem {X : bSet B} {Δ : B} := @mem_seedKernelName_iff B C _ _ e j s hEq X K Δ
  refine le_inf (le_inf (seedKernelName_subset_powerset e j s K) (le_inf ?_ (le_inf ?_ ?_))) ?_
  · apply hmem.mpr
    refine ⟨empty_subset, bot_unique ?_⟩
    have h : e Γ ⊓ (s ∈ᴮ j ∅) ≤ s ∈ᴮ (∅ : bSet C) :=
      bv_rw'' (le_top.trans hEmpty) inf_le_right B_ext_mem_right
    exact bot_of_mem_empty h
  · apply le_iInf; intro X; apply le_iInf; intro Y
    rw [← deduction]
    let Δ := Γ ⊓ ((X ⊆ᴮ Y) ⊓ (Y ∈ᴮ J))
    have hx : Δ ≤ X ⊆ᴮ Y := inf_le_right.trans inf_le_left
    have hy := hmem.mp (show Δ ≤ Y ∈ᴮ J from inf_le_right.trans inf_le_right)
    apply hmem.mpr
    refine ⟨subset_trans' hx hy.1, bot_unique ?_⟩
    have h : e Δ ⊓ (s ∈ᴮ j X) ≤ s ∈ᴮ j Y := mem_of_mem_subset
      (inf_le_left.trans ((OrderHomClass.mono e hx).trans (hSub X Y))) inf_le_right
    exact (le_inf inf_le_left h).trans_eq hy.2
  · apply le_iInf; intro X; apply le_iInf; intro Y
    rw [← deduction]
    let Δ := Γ ⊓ ((X ∈ᴮ J) ⊓ (Y ∈ᴮ J))
    have hx := hmem.mp (show Δ ≤ X ∈ᴮ J from inf_le_right.trans inf_le_left)
    have hy := hmem.mp (show Δ ≤ Y ∈ᴮ J from inf_le_right.trans inf_le_right)
    apply hmem.mpr
    refine ⟨ErdosSmallPoolOperations.binary_union_subset hx.1 hy.1, bot_unique ?_⟩
    have hm : e Δ ⊓ (s ∈ᴮ j (binary_union X Y)) ≤ s ∈ᴮ binary_union (j X) (j Y) :=
      mem_of_mem_subset (le_top.trans (hUnion X Y)) inf_le_right
    rw [mem_binary_union] at hm
    exact (le_inf inf_le_left hm).trans_eq (by rw [inf_sup_left, hx.2, hy.2, sup_idem])
  · apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff.mpr
    let Δ := Γ ⊓ (K ∈ᴮ J)
    have hn := (hmem.mp (show Δ ≤ K ∈ᴮ J from inf_le_right)).2
    have hs : e Δ ≤ s ∈ᴮ j K := (OrderHomClass.mono e (show Δ ≤ Γ from inf_le_left)).trans hSeed
    rw [inf_eq_left.mpr hs] at hn
    exact he (hn.trans (map_bot e).symm)

end bSet.ErdosSeedKernel
