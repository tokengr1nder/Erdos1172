/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalOrder
public import Erdos1172.Part4InternalIndependentHomogeneous

@[expose] public section

/-! # Singleton internal orders and arbitrary mixed binary incidence -/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
open Lattice
universe u
namespace bSet.ErdosShioyaInternal
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

theorem allIn_intro {Γ : B} {P : N} {f : N → B}
    (h : ∀ {Δ : B}, Δ ≤ Γ → ∀ x, Δ ≤ x ∈ᴮ P → Δ ≤ f x) : Γ ≤ allIn P f :=
  le_iInf fun x => deduction.mp (h inf_le_left x inf_le_right)

theorem allIn_elim {Γ : B} {P x : N} {f : N → B}
    (h : Γ ≤ allIn P f) (hx : Γ ≤ x ∈ᴮ P) : Γ ≤ f x :=
  (le_inf (h.trans (iInf_le _ x)) hx).trans bv_imp_elim

private theorem implication {Γ c d : B} (h : ∀ {Δ}, Δ ≤ Γ → Δ ≤ c → Δ ≤ d) : Γ ≤ c ⟹ d :=
  deduction.mp (h inf_le_left inf_le_right)

theorem singleton_partialOrder (z : N) {Γ : B} : Γ ≤ partialOrderValue {z} (prod {z} {z}) := by
  refine le_inf subset_self (le_inf (allIn_intro (fun _ p hp => mem_prod hp hp)) (le_inf ?_ ?_))
  · apply allIn_intro
    intro Δ _ p hp
    apply allIn_intro
    intro Δ' hΔ q hq
    apply implication
    intro E he _
    exact bv_trans (bv_symm (eq_of_mem_singleton ((he.trans hΔ).trans hp))) (eq_of_mem_singleton (he.trans hq))
  · apply allIn_intro
    intro Δ _ p hp
    apply allIn_intro
    intro Δ' d q _
    apply allIn_intro
    intro E e t h
    exact implication (fun l _ => mem_prod (((l.trans e).trans d).trans hp) (l.trans h))

theorem singleton_separative (z : N) {Γ : B} : Γ ≤ separativeValue {z} (prod {z} {z}) := by
  apply allIn_intro
  intro Δ _ p hp
  apply allIn_intro
  intro Δ' hΔ q hq
  apply implication
  intro E hE neg
  have pos : E ≤ edge (prod {z} {z}) p q := mem_prod ((hE.trans hΔ).trans hp) (hE.trans hq)
  exact ((le_inf pos neg).trans inf_compl_eq_bot.le).trans bot_le

/-- Columns constant on P are regular open even when the set of positive
columns is an arbitrary mixed subset of the length name. -/
theorem product_regularColumns (P X L : N) {Γ : B} (hx : Γ ≤ X ⊆ᴮ L) :
    Γ ≤ regularColumnsValue P (prod P P) L (prod P X) := by
  refine le_inf (ErdosIndependentHomogeneous.prod_codomain_mono hx) ?_
  apply allIn_intro
  intro Δ _ i _
  apply le_inf
  · apply allIn_intro
    intro E _ p hp
    apply allIn_intro
    intro F f q _
    apply implication
    intro K k h
    exact mem_prod ((k.trans f).trans hp) ((mem_prod_iff.mp (h.trans inf_le_right)).2)
  · apply allIn_intro
    intro E _ p hp
    apply implication
    intro F f h
    have hmem := f.trans hp
    have existsBelow := (le_inf (allIn_elim h hmem) (mem_prod hmem hmem)).trans bv_imp_elim
    apply mem_prod hmem
    exact existsBelow.trans (iSup_le fun t => (mem_prod_iff.mp (show
      (t ∈ᴮ P) ⊓ (edge (prod P P) t p ⊓ edge (prod P X) t i) ≤ (pair t i ∈ᴮ prod P X)
      from inf_le_right.trans inf_le_right)).2)

theorem singleton_regularColumns (z X L : N) {Γ : B} (hx : Γ ≤ X ⊆ᴮ L) :
    Γ ≤ regularColumnsValue {z} (prod {z} {z}) L (prod {z} X) :=
  product_regularColumns {z} X L hx

theorem singleton_column_mem (z X i : N) : edge (prod {z} X) z i = (i ∈ᴮ X) :=
  le_antisymm (mem_prod_iff.mp le_rfl).2 (mem_prod (le_top.trans mem_singleton) le_rfl)

end bSet.ErdosShioyaInternal
