/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Flypitch4.BvmExtras

@[expose] public section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosRelationGraph

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

theorem mem_comprehend_and {P : bSet 𝔹 → 𝔹} (hP : B_ext P)
    {S z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ comprehend P S ↔ Γ ≤ z ∈ᴮ S ∧ Γ ≤ P z := by
  rw [mem_comprehend_iff₂ P S hP]
  constructor
  · intro H
    constructor
    · apply H.trans
      apply iSup_le; intro w
      exact bv_rw' (x := z) (y := w) (ϕ := fun z => z ∈ᴮ S)
        (inf_le_right.trans inf_le_left)
        (h_congr := B_ext_mem_left) (H_new := inf_le_left)
    · apply H.trans
      apply iSup_le; intro w
      exact bv_rw' (inf_le_right.trans inf_le_left)
        (h_congr := hP) (H_new := inf_le_right.trans inf_le_right)
  · rintro ⟨Hz, HP⟩
    exact le_iSup_of_le z (le_inf Hz (le_inf bv_refl HP))

/-- Separation inside a product realizes any extensional binary predicate. -/
noncomputable def relationGraph (A B : bSet 𝔹)
    (P : bSet 𝔹 → bSet 𝔹 → 𝔹) : bSet 𝔹 :=
  comprehend (fun z => ⨆ a, ⨆ b, z =ᴮ pair a b ⊓ P a b) (prod A B)

theorem mem_relationGraph_iff {A B : bSet 𝔹}
    {P : bSet 𝔹 → bSet 𝔹 → 𝔹}
    (hL : ∀ b, B_ext (fun a => P a b)) (hR : ∀ a, B_ext (P a))
    {a b : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair a b ∈ᴮ relationGraph A B P ↔ Γ ≤ a ∈ᴮ A ∧ Γ ≤ b ∈ᴮ B ∧ Γ ≤ P a b := by
  have hExt : B_ext (fun z : bSet 𝔹 =>
      ⨆ a', ⨆ b', z =ᴮ pair a' b' ⊓ P a' b') :=
    B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
      B_ext_inf B_ext_bv_eq_left B_ext_const))
  unfold relationGraph
  rw [mem_comprehend_and hExt]
  constructor
  · rintro ⟨Hprod, HP⟩
    refine ⟨(mem_prod_iff.mp Hprod).1, (mem_prod_iff.mp Hprod).2, ?_⟩
    apply HP.trans
    apply iSup_le; intro a'
    apply iSup_le; intro b'
    exact bv_rw' (x := a) (y := a') (ϕ := fun z => P z b)
      (eq_of_eq_pair_left' inf_le_left) (h_congr := hL b)
      (H_new := bv_rw' (x := b) (y := b') (ϕ := fun z => P a' z)
        (eq_of_eq_pair_right' inf_le_left)
        (h_congr := hR a') (H_new := inf_le_right))
  · rintro ⟨Ha, Hb, HP⟩
    exact ⟨mem_prod_iff.mpr ⟨Ha, Hb⟩, le_iSup_of_le a (le_iSup_of_le b (le_inf bv_refl HP))⟩

theorem relationGraph_subset {A B : bSet 𝔹}
    {P : bSet 𝔹 → bSet 𝔹 → 𝔹} {Γ : 𝔹} :
    Γ ≤ relationGraph A B P ⊆ᴮ prod A B :=
  comprehend_subset (ϕ := fun z => ⨆ a, ⨆ b, z =ᴮ pair a b ⊓ P a b) (prod A B)

/-- Bounded, total, single-valued predicates give actual internal functions. -/
theorem relationGraph_is_function {A B : bSet 𝔹}
    {P : bSet 𝔹 → bSet 𝔹 → 𝔹}
    (hL : ∀ b, B_ext (fun a => P a b)) (hR : ∀ a, B_ext (P a)) {Γ : 𝔹}
    (Htotal : Γ ≤ ⨅ a, _root_.imp (a ∈ᴮ A) (⨆ b, (b ∈ᴮ B) ⊓ P a b))
    (Hunique : ∀ {a₁ a₂ b₁ b₂ : bSet 𝔹} {Δ : 𝔹}, Δ ≤ Γ →
      Δ ≤ a₁ ∈ᴮ A → Δ ≤ a₂ ∈ᴮ A → Δ ≤ b₁ ∈ᴮ B → Δ ≤ b₂ ∈ᴮ B →
      Δ ≤ P a₁ b₁ → Δ ≤ P a₂ b₂ → Δ ≤ a₁ =ᴮ a₂ → Δ ≤ b₁ =ᴮ b₂) :
    Γ ≤ is_function A B (relationGraph A B P) := by
  refine le_inf (le_inf ?_ ?_) relationGraph_subset
  · apply le_iInf; intro a₁; apply le_iInf; intro a₂
    apply le_iInf; intro b₁; apply le_iInf; intro b₂
    rw [← deduction, ← deduction]
    let Δ := (Γ ⊓ (pair a₁ b₁ ∈ᴮ relationGraph A B P ⊓
      pair a₂ b₂ ∈ᴮ relationGraph A B P)) ⊓ a₁ =ᴮ a₂
    have H₁ := (mem_relationGraph_iff hL hR).mp (show Δ ≤ pair a₁ b₁ ∈ᴮ relationGraph A B P from
        inf_le_left.trans (inf_le_right.trans inf_le_left))
    have H₂ := (mem_relationGraph_iff hL hR).mp (show Δ ≤ pair a₂ b₂ ∈ᴮ relationGraph A B P from
        inf_le_left.trans (inf_le_right.trans inf_le_right))
    exact Hunique (inf_le_left.trans inf_le_left) H₁.1 H₂.1 H₁.2.1 H₂.2.1 H₁.2.2 H₂.2.2 inf_le_right
  · apply le_iInf; intro a; rw [← deduction]
    have H := (le_inf (inf_le_left.trans (Htotal.trans (iInf_le _ a)))
      (show Γ ⊓ a ∈ᴮ A ≤ a ∈ᴮ A from inf_le_right)).trans bv_imp_elim
    obtain ⟨b, Hb⟩ := exists_convert H (B_ext_inf B_ext_mem_left (hR a))
    exact le_iSup_of_le b (le_inf (Hb.trans inf_le_left)
      ((mem_relationGraph_iff hL hR).mpr
        ⟨inf_le_right, Hb.trans inf_le_left, Hb.trans inf_le_right⟩))

end bSet.ErdosRelationGraph
