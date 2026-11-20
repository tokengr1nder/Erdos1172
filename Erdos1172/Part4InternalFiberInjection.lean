/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalRelationGraph

@[expose] public section

/-!
A coherent internal family of fiber injections produces an actual injection
into a product. The choice of each fiber injection is represented by a given
function graph F; no coherent choice is inferred from pointwise existence.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFiberInjection

open ErdosRelationGraph

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

def fiber (X f i : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun x => pair x i ∈ᴮ f) X

theorem mem_fiber_iff {X f i x : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ x ∈ᴮ fiber X f i ↔ Γ ≤ x ∈ᴮ X ∧ Γ ≤ pair x i ∈ᴮ f :=
  mem_comprehend_and B_ext_pair_mem_left

theorem fiber_subset {X f i : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ fiber X f i ⊆ᴮ X :=
  comprehend_subset (ϕ := fun x => pair x i ∈ᴮ f) X

/-- The supplied function F chooses an actual injective graph on every fiber. -/
def fiberInjectionFamily (X Y Z f F : bSet 𝔹) : 𝔹 :=
  ⨅ i, ⨅ g, (i ∈ᴮ Y ⊓ pair i g ∈ᴮ F) ⟹
    is_injective_function (fiber X f i) Z g

theorem fiberInjectionFamily_apply {X Y Z f F i g : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ fiberInjectionFamily X Y Z f F)
    (Hi : Γ ≤ i ∈ᴮ Y) (Hig : Γ ≤ pair i g ∈ᴮ F) :
    Γ ≤ is_injective_function (fiber X f i) Z g :=
  (le_inf (H.trans ((iInf_le _ i).trans (iInf_le _ g)))
    (le_inf Hi Hig)).trans bv_imp_elim

/-- The output records both the fiber label and the chosen local image. -/
def combinedRel (f F x p : bSet 𝔹) : 𝔹 :=
  ⨆ i, ⨆ g, ⨆ z,
    ((pair x i ∈ᴮ f ⊓ pair i g ∈ᴮ F) ⊓ pair x z ∈ᴮ g) ⊓ p =ᴮ pair i z

theorem combinedRel_ext_left (f F p : bSet 𝔹) :
    B_ext (fun x => combinedRel f F x p) := by
  unfold combinedRel
  exact B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
    B_ext_iSup (h := fun _ => B_ext_inf
      (B_ext_inf (B_ext_inf B_ext_pair_mem_left B_ext_const) B_ext_pair_mem_left)
      B_ext_const)))

theorem combinedRel_ext_right (f F x : bSet 𝔹) :
    B_ext (combinedRel f F x) := by
  unfold combinedRel
  exact B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
    B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_bv_eq_left)))

theorem combinedRel_intro {f F x p i g z : bSet 𝔹} {Γ : 𝔹}
    (Hxi : Γ ≤ pair x i ∈ᴮ f) (Hig : Γ ≤ pair i g ∈ᴮ F)
    (Hxz : Γ ≤ pair x z ∈ᴮ g) (Hp : Γ ≤ p =ᴮ pair i z) :
    Γ ≤ combinedRel f F x p :=
  le_iSup_of_le i (le_iSup_of_le g (le_iSup_of_le z
    (le_inf (le_inf (le_inf Hxi Hig) Hxz) Hp)))

/-- The maximum principle extracts witnesses at the given Boolean context. -/
theorem combinedRel_witnesses {f F x p : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ combinedRel f F x p) :
    ∃ i g z : bSet 𝔹, Γ ≤ pair x i ∈ᴮ f ∧ Γ ≤ pair i g ∈ᴮ F ∧
      Γ ≤ pair x z ∈ᴮ g ∧ Γ ≤ p =ᴮ pair i z := by
  have HiExt : B_ext (fun i : bSet 𝔹 => ⨆ g, ⨆ z,
      ((pair x i ∈ᴮ f ⊓ pair i g ∈ᴮ F) ⊓ pair x z ∈ᴮ g) ⊓ p =ᴮ pair i z) :=
    B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ => B_ext_inf
      (B_ext_inf (B_ext_inf B_ext_pair_mem_right B_ext_pair_mem_left) B_ext_const)
      (B_ext_pair_left B_ext_bv_eq_right)))
  obtain ⟨i, Hi⟩ := exists_convert H HiExt
  have HgExt : B_ext (fun g : bSet 𝔹 => ⨆ z,
      ((pair x i ∈ᴮ f ⊓ pair i g ∈ᴮ F) ⊓ pair x z ∈ᴮ g) ⊓ p =ᴮ pair i z) :=
    B_ext_iSup (h := fun _ => B_ext_inf
      (B_ext_inf (B_ext_inf B_ext_const B_ext_pair_mem_right) B_ext_mem_right)
      B_ext_const)
  obtain ⟨g, Hg⟩ := exists_convert Hi HgExt
  have HzExt : B_ext (fun z : bSet 𝔹 =>
      ((pair x i ∈ᴮ f ⊓ pair i g ∈ᴮ F) ⊓ pair x z ∈ᴮ g) ⊓ p =ᴮ pair i z) :=
    B_ext_inf (B_ext_inf B_ext_const B_ext_pair_mem_right)
      (B_ext_pair_right B_ext_bv_eq_right)
  obtain ⟨z, Hz⟩ := exists_convert Hg HzExt
  exact ⟨i, g, z, Hz.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)),
    Hz.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)),
    Hz.trans (inf_le_left.trans inf_le_right), Hz.trans inf_le_right⟩

noncomputable def combinedGraph (X Y Z f F : bSet 𝔹) : bSet 𝔹 :=
  relationGraph X (prod Y Z) (combinedRel f F)

theorem mem_combinedGraph_iff {X Y Z f F x p : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair x p ∈ᴮ combinedGraph X Y Z f F ↔
      Γ ≤ x ∈ᴮ X ∧ Γ ≤ p ∈ᴮ prod Y Z ∧ Γ ≤ combinedRel f F x p :=
  mem_relationGraph_iff (combinedRel_ext_left f F) (combinedRel_ext_right f F)

private theorem combinedRel_total {X Y Z C f F : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_function X Y f) (HF : Γ ≤ is_function Y C F)
    (Hfamily : Γ ≤ fiberInjectionFamily X Y Z f F) :
    Γ ≤ ⨅ x, x ∈ᴮ X ⟹ ⨆ p, p ∈ᴮ prod Y Z ⊓ combinedRel f F x p := by
  apply le_iInf; intro x; rw [← deduction]
  let Δ := Γ ⊓ x ∈ᴮ X
  have Hiex : Δ ≤ ⨆ i, i ∈ᴮ Y ⊓ pair x i ∈ᴮ f :=
    (le_inf (inf_le_left.trans ((is_total_of_is_function Hf).trans (iInf_le _ x)))
      inf_le_right).trans bv_imp_elim
  obtain ⟨i, Hi⟩ := exists_convert Hiex
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hgex : Δ ≤ ⨆ g, g ∈ᴮ C ⊓ pair i g ∈ᴮ F :=
    (le_inf (inf_le_left.trans ((is_total_of_is_function HF).trans (iInf_le _ i)))
      (Hi.trans inf_le_left)).trans bv_imp_elim
  obtain ⟨g, Hg⟩ := exists_convert Hgex
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hginj := fiberInjectionFamily_apply (inf_le_left.trans Hfamily)
    (Hi.trans inf_le_left) (Hg.trans inf_le_right)
  have Hxfiber : Δ ≤ x ∈ᴮ fiber X f i :=
    mem_fiber_iff.mpr ⟨inf_le_right, Hi.trans inf_le_right⟩
  have Hzex : Δ ≤ ⨆ z, z ∈ᴮ Z ⊓ pair x z ∈ᴮ g :=
    (le_inf ((is_total_of_is_function (Hginj.trans inf_le_left)).trans (iInf_le _ x))
      Hxfiber).trans bv_imp_elim
  obtain ⟨z, Hz⟩ := exists_convert Hzex
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  exact le_iSup_of_le (pair i z)
    (le_inf (mem_prod_iff.mpr ⟨Hi.trans inf_le_left, Hz.trans inf_le_left⟩)
      (combinedRel_intro (Hi.trans inf_le_right) (Hg.trans inf_le_right)
        (Hz.trans inf_le_right) bv_refl))

private theorem combinedRel_functional {X Y Z C f F x₁ x₂ p₁ p₂ : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_function X Y f) (HF : Γ ≤ is_function Y C F)
    (Hfamily : Γ ≤ fiberInjectionFamily X Y Z f F)
    (H₁ : Γ ≤ combinedRel f F x₁ p₁) (H₂ : Γ ≤ combinedRel f F x₂ p₂)
    (Hx : Γ ≤ x₁ =ᴮ x₂) : Γ ≤ p₁ =ᴮ p₂ := by
  obtain ⟨i₁, g₁, z₁, Hxi₁, Hig₁, Hxz₁, Hp₁⟩ := combinedRel_witnesses H₁
  obtain ⟨i₂, g₂, z₂, Hxi₂, Hig₂, Hxz₂, Hp₂⟩ := combinedRel_witnesses H₂
  have Hi : Γ ≤ i₁ =ᴮ i₂ := eq_of_is_function_of_eq Hf Hx Hxi₁ Hxi₂
  have Hg : Γ ≤ g₁ =ᴮ g₂ := eq_of_is_function_of_eq HF Hi Hig₁ Hig₂
  have Hginj := fiberInjectionFamily_apply Hfamily
    (mem_codomain_of_is_function Hxi₁ Hf) Hig₁
  have Hxz₂' : Γ ≤ pair x₂ z₂ ∈ᴮ g₁ := mem_congr bv_refl (bv_symm Hg) Hxz₂
  have Hz : Γ ≤ z₁ =ᴮ z₂ :=
    eq_of_is_function_of_eq (Hginj.trans inf_le_left) Hx Hxz₁ Hxz₂'
  exact bv_trans Hp₁ (bv_trans (pair_congr Hi Hz) (bv_symm Hp₂))

private theorem combinedRel_injective {X Y Z C f F x₁ x₂ p₁ p₂ : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_function X Y f) (HF : Γ ≤ is_function Y C F)
    (Hfamily : Γ ≤ fiberInjectionFamily X Y Z f F)
    (H₁ : Γ ≤ combinedRel f F x₁ p₁) (H₂ : Γ ≤ combinedRel f F x₂ p₂)
    (Hp : Γ ≤ p₁ =ᴮ p₂) : Γ ≤ x₁ =ᴮ x₂ := by
  obtain ⟨i₁, g₁, z₁, Hxi₁, Hig₁, Hxz₁, Hp₁⟩ := combinedRel_witnesses H₁
  obtain ⟨i₂, g₂, z₂, _, Hig₂, Hxz₂, Hp₂⟩ := combinedRel_witnesses H₂
  have Hpair : Γ ≤ pair i₁ z₁ =ᴮ pair i₂ z₂ :=
    bv_trans (bv_symm Hp₁) (bv_trans Hp Hp₂)
  have Hi : Γ ≤ i₁ =ᴮ i₂ := eq_of_eq_pair_left' Hpair
  have Hz : Γ ≤ z₁ =ᴮ z₂ := eq_of_eq_pair_right' Hpair
  have Hg : Γ ≤ g₁ =ᴮ g₂ := eq_of_is_function_of_eq HF Hi Hig₁ Hig₂
  have Hginj := fiberInjectionFamily_apply Hfamily
    (mem_codomain_of_is_function Hxi₁ Hf) Hig₁
  have Hxz₂' : Γ ≤ pair x₂ z₂ ∈ᴮ g₁ := mem_congr bv_refl (bv_symm Hg) Hxz₂
  exact eq_of_is_inj_of_eq (Hginj.trans inf_le_right) Hz Hxz₁ Hxz₂'

/-- The combined relation is a strongly represented internal injective function. -/
theorem combinedGraph_is_injective {X Y Z C f F : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_function X Y f) (HF : Γ ≤ is_function Y C F)
    (Hfamily : Γ ≤ fiberInjectionFamily X Y Z f F) :
    Γ ≤ is_injective_function X (prod Y Z) (combinedGraph X Y Z f F) := by
  refine le_inf ?_ ?_
  · apply relationGraph_is_function (combinedRel_ext_left f F) (combinedRel_ext_right f F)
      (combinedRel_total Hf HF Hfamily)
    intro x₁ x₂ p₁ p₂ Δ HΔ _ _ _ _ H₁ H₂ Hx
    exact combinedRel_functional (HΔ.trans Hf) (HΔ.trans HF)
      (HΔ.trans Hfamily) H₁ H₂ Hx
  · apply le_iInf; intro x₁; apply le_iInf; intro x₂
    apply le_iInf; intro p₁; apply le_iInf; intro p₂
    rw [← deduction]
    let Δ := Γ ⊓ (pair x₁ p₁ ∈ᴮ combinedGraph X Y Z f F ⊓
      pair x₂ p₂ ∈ᴮ combinedGraph X Y Z f F ⊓ p₁ =ᴮ p₂)
    have H₁ : Δ ≤ pair x₁ p₁ ∈ᴮ combinedGraph X Y Z f F :=
      inf_le_right.trans (inf_le_left.trans inf_le_left)
    have H₂ : Δ ≤ pair x₂ p₂ ∈ᴮ combinedGraph X Y Z f F :=
      inf_le_right.trans (inf_le_left.trans inf_le_right)
    exact combinedRel_injective (inf_le_left.trans Hf) (inf_le_left.trans HF)
      (inf_le_left.trans Hfamily) (mem_combinedGraph_iff.mp H₁).2.2
      (mem_combinedGraph_iff.mp H₂).2.2 (inf_le_right.trans inf_le_right)

theorem injects_into_product_of_fiber_injections {X Y Z C f F : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_function X Y f) (HF : Γ ≤ is_function Y C F)
    (Hfamily : Γ ≤ fiberInjectionFamily X Y Z f F) :
    Γ ≤ injects_into X (prod Y Z) :=
  injects_into_of_injection_into (le_iSup_of_le (combinedGraph X Y Z f F)
    (combinedGraph_is_injective Hf HF Hfamily))

end bSet.ErdosFiberInjection
