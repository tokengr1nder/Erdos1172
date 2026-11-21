/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSmallFiberBound

@[expose] public section

/-!
# Products of two different internal injections

An actual bounded relation sends a pair to the pair of its two component
images. All input and output names may be mixed. The resulting product
injection uses no ground interpretation or assumed product cardinality.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosMixedProductInjection

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosRelationGraph

def mapRel (f g x y : bSet 𝔹) : 𝔹 :=
  ⨆ a, ⨆ b, ⨆ c, ⨆ d,
    x =ᴮ pair a b ⊓ (y =ᴮ pair c d ⊓ (pair a c ∈ᴮ f ⊓ pair b d ∈ᴮ g))

theorem mapRel_ext_left (f g y : bSet 𝔹) : B_ext (fun x => mapRel f g x y) :=
  B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
    B_ext_iSup (h := fun _ => B_ext_inf B_ext_bv_eq_left B_ext_const))))

theorem mapRel_ext_right (f g x : bSet 𝔹) : B_ext (mapRel f g x) :=
  B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
    B_ext_iSup (h := fun _ => B_ext_inf B_ext_const (B_ext_inf B_ext_bv_eq_left B_ext_const)))))

theorem mapRel_witness {f g x y : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ mapRel f g x y) :
    ∃ a b c d : bSet 𝔹, (Γ ≤ x =ᴮ pair a b) ∧ (Γ ≤ y =ᴮ pair c d) ∧
      (Γ ≤ pair a c ∈ᴮ f) ∧ Γ ≤ pair b d ∈ᴮ g := by
  obtain ⟨a, Ha⟩ := exists_convert H
    (B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
      B_ext_inf (B_ext_pair_left B_ext_bv_eq_right)
        (B_ext_inf B_ext_const (B_ext_inf B_ext_pair_mem_left B_ext_const))))))
  obtain ⟨b, Hb⟩ := exists_convert Ha (B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
      B_ext_inf (B_ext_pair_right B_ext_bv_eq_right)
        (B_ext_inf B_ext_const (B_ext_inf B_ext_const B_ext_pair_mem_left)))))
  obtain ⟨c, Hc⟩ := exists_convert Hb
    (B_ext_iSup (h := fun _ => B_ext_inf B_ext_const
      (B_ext_inf (B_ext_pair_left B_ext_bv_eq_right) (B_ext_inf B_ext_pair_mem_right B_ext_const))))
  obtain ⟨d, Hd⟩ := exists_convert Hc
    (B_ext_inf B_ext_const (B_ext_inf (B_ext_pair_right B_ext_bv_eq_right)
      (B_ext_inf B_ext_const B_ext_pair_mem_right)))
  exact ⟨a, b, c, d, Hd.trans inf_le_left, Hd.trans (inf_le_right.trans inf_le_left),
    Hd.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)),
    Hd.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))⟩

def prodMap (A B C D f g : bSet 𝔹) : bSet 𝔹 :=
  relationGraph (prod A B) (prod C D) (mapRel f g)

theorem mem_prodMap_iff {A B C D f g x y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair x y ∈ᴮ prodMap A B C D f g ↔
      Γ ≤ x ∈ᴮ prod A B ∧ Γ ≤ y ∈ᴮ prod C D ∧ Γ ≤ mapRel f g x y :=
  mem_relationGraph_iff (mapRel_ext_left f g) (mapRel_ext_right f g)

theorem prodMap_is_function {A B C D f g : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_function A C f) (Hg : Γ ≤ is_function B D g) :
    Γ ≤ is_function (prod A B) (prod C D) (prodMap A B C D f g) := by
  apply relationGraph_is_function (P := mapRel f g) (mapRel_ext_left f g) (mapRel_ext_right f g)
  · apply le_iInf
    intro x
    rw [← deduction]
    let Δ := Γ ⊓ x ∈ᴮ prod A B
    obtain ⟨a, Ha, b, Hb, Hx⟩ := mem_prod_iff₂.mp (show Δ ≤ x ∈ᴮ prod A B from inf_le_right)
    have Hc : Δ ≤ ⨆ c, c ∈ᴮ C ⊓ pair a c ∈ᴮ f :=
      (le_inf (inf_le_left.trans ((is_total_of_is_function Hf).trans (iInf_le _ a))) Ha).trans
        bv_imp_elim
    have Hd : Δ ≤ ⨆ d, d ∈ᴮ D ⊓ pair b d ∈ᴮ g :=
      (le_inf (inf_le_left.trans ((is_total_of_is_function Hg).trans (iInf_le _ b))) Hb).trans
        bv_imp_elim
    obtain ⟨c, Hc⟩ := exists_convert Hc (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
    obtain ⟨d, Hd⟩ := exists_convert Hd (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
    exact le_iSup_of_le (pair c d) (le_inf (mem_prod (Hc.trans inf_le_left) (Hd.trans inf_le_left))
      (le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le c (le_iSup_of_le d
        (le_inf Hx (le_inf bv_refl (le_inf (Hc.trans inf_le_right) (Hd.trans inf_le_right)))))))))
  · intro x₁ x₂ y₁ y₂ Δ HΔ _ _ _ _ H₁ H₂ Hx
    obtain ⟨a₁, b₁, c₁, d₁, Hx₁, Hy₁, Hf₁, Hg₁⟩ := mapRel_witness H₁
    obtain ⟨a₂, b₂, c₂, d₂, Hx₂, Hy₂, Hf₂, Hg₂⟩ := mapRel_witness H₂
    have Hin : Δ ≤ pair a₁ b₁ =ᴮ pair a₂ b₂ := bv_trans (bv_symm Hx₁) (bv_trans Hx Hx₂)
    have Hc : Δ ≤ c₁ =ᴮ c₂ :=
      eq_of_is_func_of_eq (HΔ.trans (Hf.trans (inf_le_left.trans inf_le_left)))
        (eq_of_eq_pair_left' Hin) Hf₁ Hf₂
    have Hd : Δ ≤ d₁ =ᴮ d₂ :=
      eq_of_is_func_of_eq (HΔ.trans (Hg.trans (inf_le_left.trans inf_le_left)))
        (eq_of_eq_pair_right' Hin) Hg₁ Hg₂
    exact bv_trans Hy₁ (bv_trans (pair_congr Hc Hd) (bv_symm Hy₂))

theorem prodMap_is_inj {A B C D f g : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_inj f) (Hg : Γ ≤ is_inj g) :
    Γ ≤ is_inj (prodMap A B C D f g) := by
  apply le_iInf
  intro x₁
  apply le_iInf
  intro x₂
  apply le_iInf
  intro y₁
  apply le_iInf
  intro y₂
  rw [← deduction]
  let Δ := Γ ⊓ (pair x₁ y₁ ∈ᴮ prodMap A B C D f g ⊓ pair x₂ y₂ ∈ᴮ prodMap A B C D f g ⊓ y₁ =ᴮ y₂)
  have H₁ := (mem_prodMap_iff.mp (show Δ ≤ pair x₁ y₁ ∈ᴮ prodMap A B C D f g from
      inf_le_right.trans (inf_le_left.trans inf_le_left))).2.2
  have H₂ := (mem_prodMap_iff.mp (show Δ ≤ pair x₂ y₂ ∈ᴮ prodMap A B C D f g from
      inf_le_right.trans (inf_le_left.trans inf_le_right))).2.2
  obtain ⟨a₁, b₁, c₁, d₁, Hx₁, Hy₁, Hf₁, Hg₁⟩ := mapRel_witness H₁
  obtain ⟨a₂, b₂, c₂, d₂, Hx₂, Hy₂, Hf₂, Hg₂⟩ := mapRel_witness H₂
  have Hout : Δ ≤ pair c₁ d₁ =ᴮ pair c₂ d₂ :=
    bv_trans (bv_symm Hy₁) (bv_trans (inf_le_right.trans inf_le_right) Hy₂)
  have Ha : Δ ≤ a₁ =ᴮ a₂ := eq_of_is_inj_of_eq (inf_le_left.trans Hf)
    (eq_of_eq_pair_left' Hout) Hf₁ Hf₂
  have Hb : Δ ≤ b₁ =ᴮ b₂ := eq_of_is_inj_of_eq (inf_le_left.trans Hg)
    (eq_of_eq_pair_right' Hout) Hg₁ Hg₂
  exact bv_trans Hx₁ (bv_trans (pair_congr Ha Hb) (bv_symm Hx₂))

theorem prodMap_is_injective_function {A B C D f g : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_injective_function A C f) (Hg : Γ ≤ is_injective_function B D g) :
    Γ ≤ is_injective_function (prod A B) (prod C D) (prodMap A B C D f g) :=
  le_inf (prodMap_is_function (Hf.trans inf_le_left) (Hg.trans inf_le_left))
    (prodMap_is_inj (Hf.trans inf_le_right) (Hg.trans inf_le_right))

/-- Product lifting for arbitrary different source and target names. -/
theorem injects_into_prod {A B C D : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ injects_into A C) (HB : Γ ≤ injects_into B D) :
    Γ ≤ injects_into (prod A B) (prod C D) := by
  obtain ⟨f, Hf⟩ := exists_convert (injection_into_of_injects_into HA)
    ErdosSmallFiberBound.B_ext_injective_code
  obtain ⟨g, Hg⟩ := exists_convert (injection_into_of_injects_into HB)
    ErdosSmallFiberBound.B_ext_injective_code
  exact injects_into_of_injection_into
    (le_iSup_of_le (prodMap A B C D f g) (prodMap_is_injective_function Hf Hg))

end bSet.ErdosMixedProductInjection
