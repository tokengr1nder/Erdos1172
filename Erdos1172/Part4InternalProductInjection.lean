/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalHartogsRelations

@[expose] public section

/-!
# Products of internal injections

The existing bounded pair-map graph sends `(a₁, a₂)` to `(f(a₁), f(a₂))`.
Its totality, functionality, and injectivity are established for arbitrary
Boolean names and arbitrary Boolean contexts. No ground-model injection or
cardinal-preservation hypothesis is used.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosProductInjection

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

theorem prod_map_self_subset {X Y f : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ prod_map_self X Y f ⊆ᴮ prod (prod X X) (prod Y Y) :=
  subset.mk_subset

private theorem components_of_mem_prod_map_self
    {X Y f x y : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ pair x y ∈ᴮ prod_map_self X Y f) :
    ∃ a₁ a₂ b₁ b₂ : bSet 𝔹,
      (Γ ≤ x =ᴮ pair a₁ a₂) ∧ (Γ ≤ y =ᴮ pair b₁ b₂) ∧
      (Γ ≤ pair a₁ b₁ ∈ᴮ f) ∧ (Γ ≤ pair a₂ b₂ ∈ᴮ f) := by
  have Hprod : Γ ≤ pair x y ∈ᴮ prod (prod X X) (prod Y Y) :=
    mem_of_mem_subset prod_map_self_subset H
  obtain ⟨Hx, Hy⟩ := mem_prod_iff.mp Hprod
  obtain ⟨a₁, _Ha₁, a₂, _Ha₂, Heqx⟩ := mem_prod_iff₂.mp Hx
  obtain ⟨b₁, _Hb₁, b₂, _Hb₂, Heqy⟩ := mem_prod_iff₂.mp Hy
  have Hpair : Γ ≤ pair (pair a₁ a₂) (pair b₁ b₂) ∈ᴮ prod_map_self X Y f :=
    mem_congr (pair_congr Heqx Heqy) bv_refl H
  obtain ⟨_, _, _, _, H₁, H₂⟩ := mem_prod_map_self_iff.mp Hpair
  exact ⟨a₁, a₂, b₁, b₂, Heqx, Heqy, H₁, H₂⟩

private theorem output_eq_of_prod_map_self
    {X Y f x₁ x₂ y₁ y₂ : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func f)
    (H₁ : Γ ≤ pair x₁ y₁ ∈ᴮ prod_map_self X Y f)
    (H₂ : Γ ≤ pair x₂ y₂ ∈ᴮ prod_map_self X Y f)
    (Heq : Γ ≤ x₁ =ᴮ x₂) : Γ ≤ y₁ =ᴮ y₂ := by
  obtain ⟨a₁, a₂, b₁, b₂, Hx₁, Hy₁, Hab₁, Hab₂⟩ :=
    components_of_mem_prod_map_self H₁
  obtain ⟨c₁, c₂, d₁, d₂, Hx₂, Hy₂, Hcd₁, Hcd₂⟩ :=
    components_of_mem_prod_map_self H₂
  have Hac : Γ ≤ pair a₁ a₂ =ᴮ pair c₁ c₂ :=
    bv_trans (bv_symm Hx₁) (bv_trans Heq Hx₂)
  have Hbd₁ : Γ ≤ b₁ =ᴮ d₁ :=
    eq_of_is_func_of_eq Hf (eq_of_eq_pair_left' Hac) Hab₁ Hcd₁
  have Hbd₂ : Γ ≤ b₂ =ᴮ d₂ :=
    eq_of_is_func_of_eq Hf (eq_of_eq_pair_right' Hac) Hab₂ Hcd₂
  exact bv_trans Hy₁ (bv_trans (pair_congr Hbd₁ Hbd₂) (bv_symm Hy₂))

theorem prod_map_self_is_func {X Y f : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func f) : Γ ≤ is_func (prod_map_self X Y f) := by
  apply le_iInf; intro x₁
  apply le_iInf; intro x₂
  apply le_iInf; intro y₁
  apply le_iInf; intro y₂
  rw [← deduction, ← deduction]
  exact output_eq_of_prod_map_self (inf_le_left.trans (inf_le_left.trans Hf))
    (inf_le_left.trans (inf_le_right.trans inf_le_left))
    (inf_le_left.trans (inf_le_right.trans inf_le_right)) inf_le_right

private theorem input_eq_of_prod_map_self
    {X Y f x₁ x₂ y₁ y₂ : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_inj f)
    (H₁ : Γ ≤ pair x₁ y₁ ∈ᴮ prod_map_self X Y f)
    (H₂ : Γ ≤ pair x₂ y₂ ∈ᴮ prod_map_self X Y f)
    (Heq : Γ ≤ y₁ =ᴮ y₂) : Γ ≤ x₁ =ᴮ x₂ := by
  obtain ⟨a₁, a₂, b₁, b₂, Hx₁, Hy₁, Hab₁, Hab₂⟩ :=
    components_of_mem_prod_map_self H₁
  obtain ⟨c₁, c₂, d₁, d₂, Hx₂, Hy₂, Hcd₁, Hcd₂⟩ :=
    components_of_mem_prod_map_self H₂
  have Hbd : Γ ≤ pair b₁ b₂ =ᴮ pair d₁ d₂ :=
    bv_trans (bv_symm Hy₁) (bv_trans Heq Hy₂)
  have Hac₁ : Γ ≤ a₁ =ᴮ c₁ :=
    eq_of_is_inj_of_eq Hf (eq_of_eq_pair_left' Hbd) Hab₁ Hcd₁
  have Hac₂ : Γ ≤ a₂ =ᴮ c₂ :=
    eq_of_is_inj_of_eq Hf (eq_of_eq_pair_right' Hbd) Hab₂ Hcd₂
  exact bv_trans Hx₁ (bv_trans (pair_congr Hac₁ Hac₂) (bv_symm Hx₂))

theorem prod_map_self_is_inj {X Y f : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_inj f) : Γ ≤ is_inj (prod_map_self X Y f) := by
  apply le_iInf; intro x₁
  apply le_iInf; intro x₂
  apply le_iInf; intro y₁
  apply le_iInf; intro y₂
  rw [← deduction]
  exact input_eq_of_prod_map_self (inf_le_left.trans Hf)
    (inf_le_right.trans (inf_le_left.trans inf_le_left))
    (inf_le_right.trans (inf_le_left.trans inf_le_right))
    (inf_le_right.trans inf_le_right)

private theorem output_exists_of_total {X Y f a : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_total X Y f) (Ha : Γ ≤ a ∈ᴮ X) :
    ∃ b : bSet 𝔹, Γ ≤ b ∈ᴮ Y ⊓ pair a b ∈ᴮ f := by
  have H : Γ ≤ ⨆ b : bSet 𝔹, b ∈ᴮ Y ⊓ pair a b ∈ᴮ f :=
    (le_inf (Hf.trans (iInf_le _ a)) Ha).trans bv_imp_elim
  exact exists_convert H (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)

theorem prod_map_self_is_total {X Y f : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_total X Y f) :
    Γ ≤ is_total (prod X X) (prod Y Y) (prod_map_self X Y f) := by
  apply le_iInf
  intro x
  rw [← deduction]
  obtain ⟨a₁, Ha₁, a₂, Ha₂, Heqx⟩ :=
    (mem_prod_iff₂ (x := X) (y := X) (z := x)).mp
      (show Γ ⊓ x ∈ᴮ prod X X ≤ x ∈ᴮ prod X X from inf_le_right)
  obtain ⟨b₁, Hb₁⟩ := output_exists_of_total (inf_le_left.trans Hf) Ha₁
  obtain ⟨b₂, Hb₂⟩ := output_exists_of_total (inf_le_left.trans Hf) Ha₂
  apply le_iSup_of_le (pair b₁ b₂)
  refine le_inf (mem_prod (Hb₁.trans inf_le_left) (Hb₂.trans inf_le_left)) ?_
  have Hmap : Γ ⊓ x ∈ᴮ prod X X ≤
      pair (pair a₁ a₂) (pair b₁ b₂) ∈ᴮ prod_map_self X Y f :=
    mem_prod_map_self_iff.mpr
      ⟨Ha₁, Ha₂, Hb₁.trans inf_le_left, Hb₂.trans inf_le_left,
        Hb₁.trans inf_le_right, Hb₂.trans inf_le_right⟩
  exact mem_congr (pair_congr (bv_symm Heqx) bv_refl) bv_refl Hmap

/-- The concrete coordinatewise pair map is an actual bounded injection. -/
theorem prod_map_self_is_injective_function {X Y f : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_injective_function X Y f) :
    Γ ≤ is_injective_function (prod X X) (prod Y Y) (prod_map_self X Y f) :=
  le_inf
    (le_inf
      (le_inf
        (prod_map_self_is_func
          (Hf.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))))
        (prod_map_self_is_total
          (Hf.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))))
      prod_map_self_subset)
    (prod_map_self_is_inj (Hf.trans inf_le_right))

/-- Product lifting holds for internal injections in every Boolean context. -/
theorem injects_into_prod_self {X Y : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ injects_into X Y) :
    Γ ≤ injects_into (prod X X) (prod Y Y) := by
  apply injects_into_of_injection_into
  apply (injection_into_of_injects_into H).trans
  apply iSup_le
  intro f
  exact le_iSup_of_le (prod_map_self X Y f)
    (prod_map_self_is_injective_function le_rfl)

end bSet.ErdosProductInjection
