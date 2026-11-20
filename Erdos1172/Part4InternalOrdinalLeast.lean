/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalInitialSegments

@[expose] public section

/-!
# Least members of arbitrary internal ordinal subsets

Boolean-valued regularity gives a membership-minimal point of a nonempty
set. When the set is contained in an ordinal, trichotomy makes this point
least. Fullness retains the original Boolean condition. Uniqueness and
extensionality are proved separately for use in coherent choice graphs.
No new existence principle, CH, or ground-set representation is assumed.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosOrdinalLeast

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

def leastIn (C x : bSet 𝔹) : 𝔹 :=
  x ∈ᴮ C ⊓ ⨅ z : bSet 𝔹, _root_.imp (z ∈ᴮ C) (x =ᴮ z ⊔ x ∈ᴮ z)

theorem leastIn_ext_set (x : bSet 𝔹) : B_ext (fun C => leastIn C x) :=
  B_ext_inf B_ext_mem_right (B_ext_iInf (h := fun _ =>
    B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const)))

theorem leastIn_ext_value (C : bSet 𝔹) : B_ext (leastIn C) :=
  B_ext_inf B_ext_mem_left (B_ext_iInf (h := fun _ =>
    B_ext_imp (h₁ := B_ext_const)
      (h₂ := B_ext_sup (h₁ := B_ext_bv_eq_left) (h₂ := B_ext_mem_left))))

theorem leastIn_mem {C x : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ leastIn C x) : Γ ≤ x ∈ᴮ C := H.trans inf_le_left

theorem leastIn_apply {C x z : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ leastIn C x) (Hz : Γ ≤ z ∈ᴮ C) :
    Γ ≤ x =ᴮ z ⊔ x ∈ᴮ z :=
  (le_inf (H.trans (inf_le_right.trans (iInf_le _ z))) Hz).trans bv_imp_elim

/-- Two least members agree internally. This uses no ordinal hypothesis:
the two strict alternatives would already be a membership two-cycle. -/
theorem leastIn_unique {C x y : bSet 𝔹} {Γ : 𝔹}
    (Hx : Γ ≤ leastIn C x) (Hy : Γ ≤ leastIn C y) : Γ ≤ x =ᴮ y := by
  have Hxy := leastIn_apply Hx (leastIn_mem Hy)
  have Hyx := leastIn_apply Hy (leastIn_mem Hx)
  apply (le_inf (le_refl Γ) Hxy).trans
  rw [inf_sup_left]
  apply sup_le
  · exact inf_le_right
  · apply (le_inf (le_refl (Γ ⊓ x ∈ᴮ y)) (inf_le_left.trans Hyx)).trans
    rw [inf_sup_left]
    apply sup_le
    · exact bv_symm inf_le_right
    · exact (bot_of_mem_mem' x y (inf_le_left.trans inf_le_right) inf_le_right).trans bot_le

/-- Locally equal candidate sets have locally equal least members. -/
theorem leastIn_unique_of_eq {C D x y : bSet 𝔹} {Γ : 𝔹}
    (HCD : Γ ≤ C =ᴮ D) (Hx : Γ ≤ leastIn C x) (Hy : Γ ≤ leastIn D y) :
    Γ ≤ x =ᴮ y :=
  leastIn_unique
    (bv_rw'' (ϕ := fun A => leastIn A x) HCD Hx (leastIn_ext_set x)) Hy

/-- Every internally nonempty subset of an arbitrary internal ordinal has
one actual least-member name at the same Boolean condition. -/
theorem exists_least_of_nonempty {κ C : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ) (HC : Γ ≤ C ⊆ᴮ κ) (Hnonempty : Γ ≤ (C =ᴮ ∅)ᶜ) :
    ∃ x : bSet 𝔹, Γ ≤ leastIn C x := by
  have Hext : B_ext (fun x : bSet 𝔹 => x ∈ᴮ C ⊓
      (⨅ z : bSet 𝔹, _root_.imp (z ∈ᴮ C) (z ∈ᴮ x)ᶜ)) :=
    B_ext_inf B_ext_mem_left (B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_neg (h := B_ext_mem_right))))
  obtain ⟨x, Hx⟩ := exists_convert (bSet_axiom_of_regularity C Hnonempty) Hext
  refine ⟨x, le_inf (Hx.trans inf_le_left) ?_⟩
  apply le_iInf
  intro z
  rw [← deduction]
  let Δ := Γ ⊓ z ∈ᴮ C
  have Hxκ : Δ ≤ x ∈ᴮ κ :=
    inf_le_left.trans (mem_of_mem_subset HC (Hx.trans inf_le_left))
  have Hzκ : Δ ≤ z ∈ᴮ κ := mem_of_mem_subset (inf_le_left.trans HC) inf_le_right
  have Hnotzx : Δ ≤ (z ∈ᴮ x)ᶜ :=
    (le_inf (inf_le_left.trans (Hx.trans (inf_le_right.trans (iInf_le _ z))))
      inf_le_right).trans bv_imp_elim
  have Htri : Δ ≤ x =ᴮ z ⊔ x ∈ᴮ z ⊔ z ∈ᴮ x :=
    epsilon_trichotomy_of_Ord Hxκ Hzκ (inf_le_left.trans Hκ)
  apply (le_inf (le_refl Δ) Htri).trans
  rw [inf_sup_left]
  exact sup_le inf_le_right
    ((bv_absurd _ inf_le_right (inf_le_left.trans Hnotzx)).trans bot_le)

end bSet.ErdosOrdinalLeast
