/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalIndependentMaximal
public import Erdos1172.Part4InternalIdealSemantics
public import Erdos1172.Part4InternalRelationChoice

@[expose] public section

/-!
# Maximal independent subsets cover their complement by neighborhoods

A vertex with no selected-color neighbor in an independent set can be
adjoined while preserving independence. Consequently, a maximal independent
subset of an arbitrary name X supplies a selected-color neighbor for every
vertex in X minus that subset. All statements retain an arbitrary Boolean
context; in particular, no fixed external witness is extracted from a join.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosIndependentCoverage

open ErdosPartition ErdosIndependentMaximal ErdosIdeal

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

private theorem mem_insert1_value {x y A : bSet 𝔹} :
    x ∈ᴮ bSet.insert1 y A = x =ᴮ y ⊔ x ∈ᴮ A :=
  mem_insert1

private theorem insert_cases {x y A : bSet 𝔹} {Γ v : 𝔹}
    (Hx : Γ ≤ x ∈ᴮ bSet.insert1 y A)
    (Hnew : ∀ {Δ : 𝔹}, Δ ≤ Γ → Δ ≤ x =ᴮ y → Δ ≤ v)
    (Hold : ∀ {Δ : 𝔹}, Δ ≤ Γ → Δ ≤ x ∈ᴮ A → Δ ≤ v) : Γ ≤ v := by
  have Hsplit : Γ ≤ x =ᴮ y ⊔ x ∈ᴮ A := Hx.trans (mem_insert1_value (x := x) (y := y) (A := A)).le
  exact (le_inf le_rfl Hsplit).trans
    (bv_or_elim_right (Hnew inf_le_left inf_le_right) (Hold inf_le_left inf_le_right))

private theorem no_edge_congr {color : Bool} {R x₁ x₂ y₁ y₂ : bSet 𝔹} {Γ : 𝔹}
    (Hx : Γ ≤ x₁ =ᴮ x₂) (Hy : Γ ≤ y₁ =ᴮ y₂)
    (Hedge : Γ ≤ (graphColor color R x₂ y₂)ᶜ) :
    Γ ≤ (graphColor color R x₁ y₁)ᶜ := by
  apply bv_rw' (ϕ := fun x => (graphColor color R x y₁)ᶜ) Hx
    (h_congr := B_ext_neg (h := graphColor_ext_left color R y₁))
  exact bv_rw' (ϕ := fun y => (graphColor color R x₂ y)ᶜ) Hy
    (h_congr := B_ext_neg (h := graphColor_ext_right color R x₂)) (H_new := Hedge)

/-- Adjoining a vertex with no selected-color neighbor preserves independence.
The adjoined vertex is not required to be externally distinct from old names. -/
theorem independent_insert {color : Bool} {R A y : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ independent color R A)
    (Hnone : Γ ≤ ⨅ a : bSet 𝔹, _root_.imp (a ∈ᴮ A) (graphColor color R a y)ᶜ) :
    Γ ≤ independent color R (bSet.insert1 y A) := by
  apply le_iInf
  intro a
  apply le_iInf
  intro b
  rw [← deduction]
  let Δ := Γ ⊓ (a ∈ᴮ bSet.insert1 y A ⊓ b ∈ᴮ bSet.insert1 y A)
  have Ha : Δ ≤ a ∈ᴮ bSet.insert1 y A := inf_le_right.trans inf_le_left
  have Hb : Δ ≤ b ∈ᴮ bSet.insert1 y A := inf_le_right.trans inf_le_right
  apply insert_cases Ha
  · intro Θ HΘ Hay
    apply insert_cases (HΘ.trans Hb)
    · intro Ξ HΞ Hby
      have Hself : Ξ ≤ (graphColor color R y y)ᶜ := by
        rw [graphColor_self, compl_bot]
        exact le_top
      exact no_edge_congr (HΞ.trans Hay) Hby Hself
    · intro Ξ HΞ HbA
      have Hby : Ξ ≤ (graphColor color R b y)ᶜ :=
        (le_inf (((HΞ.trans HΘ).trans inf_le_left).trans
          (Hnone.trans (iInf_le _ b))) HbA).trans bv_imp_elim
      have Hyb : Ξ ≤ (graphColor color R y b)ᶜ := by
        rw [graphColor_symm color R y b]
        exact Hby
      exact no_edge_congr (HΞ.trans Hay) bv_refl Hyb
  · intro Θ HΘ HaA
    apply insert_cases (HΘ.trans Hb)
    · intro Ξ HΞ Hby
      have Hay : Ξ ≤ (graphColor color R a y)ᶜ :=
        (le_inf (((HΞ.trans HΘ).trans inf_le_left).trans
          (Hnone.trans (iInf_le _ a))) (HΞ.trans HaA)).trans bv_imp_elim
      exact no_edge_congr bv_refl Hby Hay
    · intro Ξ HΞ HbA
      exact independent_apply (((HΞ.trans HΘ).trans inf_le_left).trans HA) (HΞ.trans HaA) HbA

/-- Every point outside a maximal independent subset has a selected-color
neighbor inside it. No nonemptiness, cardinal, ordinal, or CH premise is used. -/
theorem maximal_independent_covers {color : Bool} {R X A : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ A ⊆ᴮ X) (Hind : Γ ≤ independent color R A)
    (Hmax : Γ ≤ ⨅ B : bSet 𝔹,
      _root_.imp (B ⊆ᴮ X ⊓ independent color R B) (_root_.imp (A ⊆ᴮ B) (A =ᴮ B))) :
    Γ ≤ ⨅ y : bSet 𝔹, _root_.imp (y ∈ᴮ difference X A)
      (⨆ a : bSet 𝔹, a ∈ᴮ A ⊓ graphColor color R a y) := by
  apply le_iInf
  intro y
  rw [← deduction]
  rw [← compl_compl (⨆ a : bSet 𝔹, a ∈ᴮ A ⊓ graphColor color R a y), ← imp_bot, ← deduction]
  let Δ := (Γ ⊓ y ∈ᴮ difference X A) ⊓ (⨆ a : bSet 𝔹, a ∈ᴮ A ⊓ graphColor color R a y)ᶜ
  have HΔ : Δ ≤ Γ := inf_le_left.trans inf_le_left
  have Hy : Δ ≤ y ∈ᴮ X ⊓ (y ∈ᴮ A)ᶜ := by
    rw [← mem_difference]
    exact inf_le_left.trans inf_le_right
  have Hnone : Δ ≤ ⨅ a : bSet 𝔹, _root_.imp (a ∈ᴮ A) (graphColor color R a y)ᶜ := by
    apply le_iInf
    intro a
    rw [← deduction, ← imp_bot, ← deduction]
    have Hex : (Δ ⊓ a ∈ᴮ A) ⊓ graphColor color R a y ≤
        ⨆ b : bSet 𝔹, b ∈ᴮ A ⊓ graphColor color R b y :=
      le_iSup_of_le a (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
    exact bv_absurd _ Hex
      ((inf_le_left.trans inf_le_left).trans (show Δ ≤
        (⨆ b : bSet 𝔹, b ∈ᴮ A ⊓ graphColor color R b y)ᶜ from inf_le_right))
  have Hnew : Δ ≤ bSet.insert1 y A ⊆ᴮ X ⊓
      independent color R (bSet.insert1 y A) :=
    le_inf (ErdosRelationChoice.insert_subset_of_mem (HΔ.trans Hsub)
      (Hy.trans inf_le_left)) (independent_insert (HΔ.trans Hind) Hnone)
  have Hextend : Δ ≤ A ⊆ᴮ bSet.insert1 y A := by
    rw [subset_unfold']
    apply le_iInf
    intro z
    rw [← deduction, mem_insert1_value]
    exact inf_le_right.trans le_sup_right
  have Heq : Δ ≤ A =ᴮ bSet.insert1 y A :=
    (le_inf ((le_inf
      (HΔ.trans (Hmax.trans (iInf_le _ (bSet.insert1 y A))))
      Hnew).trans bv_imp_elim) Hextend).trans bv_imp_elim
  have Hinsert : Δ ≤ y ∈ᴮ bSet.insert1 y A := by
    rw [mem_insert1_value]
    exact bv_refl.trans le_sup_left
  exact bv_absurd _ (mem_congr bv_refl (bv_symm Heq) Hinsert) (Hy.trans inf_le_right)

end bSet.ErdosIndependentCoverage
