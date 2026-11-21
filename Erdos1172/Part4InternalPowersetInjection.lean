/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalRelationGraph

@[expose] public section

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

noncomputable section

namespace bSet.ErdosPowersetInjection

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- An injective relation reflects membership in its bounded image at the
same Boolean condition. -/
theorem mem_of_mem_image_of_inj {A Y f x y : bSet 𝔹} {Γ : 𝔹}
    (Hinj : Γ ≤ is_inj f) (Hxy : Γ ≤ pair x y ∈ᴮ f)
    (Hy : Γ ≤ y ∈ᴮ image A Y f) : Γ ≤ x ∈ᴮ A := by
  obtain ⟨z, Hz⟩ := exists_convert (mem_image_iff.mp Hy).2
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  have Hxz : Γ ≤ x =ᴮ z := eq_of_is_inj_of_eq Hinj bv_refl Hxy (Hz.trans inf_le_right)
  exact bv_rw' Hxz (ϕ := fun w => w ∈ᴮ A)
    (h_congr := B_ext_mem_left) (H_new := Hz.trans inf_le_left)

/-- Bounded image inclusion reflects inclusion on subsets of the domain of
an actual internal injection. The second set need not be supported there. -/
theorem subset_of_image_subset {X Y f A B : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_injective_function X Y f) (HA : Γ ≤ A ⊆ᴮ X)
    (Himage : Γ ≤ image A Y f ⊆ᴮ image B Y f) : Γ ≤ A ⊆ᴮ B := by
  rw [subset_unfold']
  apply le_iInf; intro x
  rw [← deduction]
  have HxX : Γ ⊓ x ∈ᴮ A ≤ x ∈ᴮ X := mem_of_mem_subset (inf_le_left.trans HA) inf_le_right
  have Htotal : Γ ⊓ x ∈ᴮ A ≤ is_total X Y f :=
    is_total_of_is_function (inf_le_left.trans (Hf.trans inf_le_left))
  have Hex : Γ ⊓ x ∈ᴮ A ≤ ⨆ y, y ∈ᴮ Y ⊓ pair x y ∈ᴮ f :=
    (le_inf (Htotal.trans (iInf_le _ x)) HxX).trans bv_imp_elim
  obtain ⟨y, Hy⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have HyA : Γ ⊓ x ∈ᴮ A ≤ y ∈ᴮ image A Y f :=
    mem_image (Hy.trans inf_le_right) inf_le_right (Hy.trans inf_le_left)
  have HyB : Γ ⊓ x ∈ᴮ A ≤ y ∈ᴮ image B Y f := mem_of_mem_subset (inf_le_left.trans Himage) HyA
  exact mem_of_mem_image_of_inj (inf_le_left.trans (Hf.trans inf_le_right))
    (Hy.trans inf_le_right) HyB

/-- Image equality under a local internal injection reflects equality of
arbitrary internal subsets of its domain. -/
theorem eq_of_image_eq {X Y f A B : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_injective_function X Y f)
    (HA : Γ ≤ A ⊆ᴮ X) (HB : Γ ≤ B ⊆ᴮ X)
    (Heq : Γ ≤ image A Y f =ᴮ image B Y f) : Γ ≤ A =ᴮ B :=
  subset_ext (subset_of_image_subset Hf HA (subset_of_eq Heq))
    (subset_of_image_subset Hf HB (subset_of_eq (bv_symm Heq)))

/-- The actual bounded graph of the direct-image operation on subsets. -/
def powersetImageGraph (X Y f : bSet 𝔹) : bSet 𝔹 :=
  ErdosRelationGraph.relationGraph (bv_powerset X) (bv_powerset Y)
    (fun A B => image A Y f =ᴮ B)

private theorem image_eq_ext_left (Y f B : bSet 𝔹) :
    B_ext (fun A => image A Y f =ᴮ B) :=
  B_ext_term (fun z => z =ᴮ B) (fun A => image A Y f)
    B_ext_bv_eq_left B_congr_image_left

theorem mem_powersetImageGraph_iff {X Y f A B : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair A B ∈ᴮ powersetImageGraph X Y f ↔
      Γ ≤ A ∈ᴮ bv_powerset X ∧ Γ ≤ B ∈ᴮ bv_powerset Y ∧ Γ ≤ image A Y f =ᴮ B :=
  ErdosRelationGraph.mem_relationGraph_iff
    (fun B => image_eq_ext_left Y f B) (fun _ => B_ext_bv_eq_right)

/-- Bounded image is a supported function on powersets even for an arbitrary
relation; no globally valid input-function hypothesis is used. -/
theorem powersetImageGraph_is_function {X Y f : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ is_function (bv_powerset X) (bv_powerset Y) (powersetImageGraph X Y f) := by
  apply ErdosRelationGraph.relationGraph_is_function
    (P := fun A B => image A Y f =ᴮ B)
    (fun B => image_eq_ext_left Y f B) (fun _ => B_ext_bv_eq_right)
  · apply le_iInf; intro A
    rw [← deduction]
    exact le_iSup_of_le (image A Y f) (le_inf (mem_powerset_iff.mpr image_subset) bv_refl)
  · intro A₁ A₂ B₁ B₂ Δ _ _ _ _ _ H₁ H₂ Heq
    exact bv_trans (bv_symm H₁) (bv_trans (B_congr_image_left Heq) H₂)

private theorem input_eq_of_powersetImageGraph
    {X Y f A₁ A₂ B₁ B₂ : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_injective_function X Y f)
    (H₁ : Γ ≤ pair A₁ B₁ ∈ᴮ powersetImageGraph X Y f)
    (H₂ : Γ ≤ pair A₂ B₂ ∈ᴮ powersetImageGraph X Y f)
    (Heq : Γ ≤ B₁ =ᴮ B₂) : Γ ≤ A₁ =ᴮ A₂ := by
  have H₁' := mem_powersetImageGraph_iff.mp H₁
  have H₂' := mem_powersetImageGraph_iff.mp H₂
  exact eq_of_image_eq Hf (mem_powerset_iff.mp H₁'.1)
    (mem_powerset_iff.mp H₂'.1)
    (bv_trans H₁'.2.2 (bv_trans Heq (bv_symm H₂'.2.2)))

theorem powersetImageGraph_is_inj {X Y f : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_injective_function X Y f) :
    Γ ≤ is_inj (powersetImageGraph X Y f) := by
  apply le_iInf; intro A₁
  apply le_iInf; intro A₂
  apply le_iInf; intro B₁
  apply le_iInf; intro B₂
  rw [← deduction]
  exact input_eq_of_powersetImageGraph (inf_le_left.trans Hf)
    (inf_le_right.trans (inf_le_left.trans inf_le_left))
    (inf_le_right.trans (inf_le_left.trans inf_le_right))
    (inf_le_right.trans inf_le_right)

/-- The concrete image graph is an internal injection under the original
Boolean condition, not merely for globally valid graph names. -/
theorem powersetImageGraph_is_injective_function {X Y f : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_injective_function X Y f) :
    Γ ≤ is_injective_function (bv_powerset X) (bv_powerset Y) (powersetImageGraph X Y f) :=
  le_inf powersetImageGraph_is_function (powersetImageGraph_is_inj Hf)

/-- Powersets preserve internal cardinal injection in every Boolean context. -/
theorem powerset_injects_of_injects {X Y : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ injects_into X Y) :
    Γ ≤ injects_into (bv_powerset X) (bv_powerset Y) := by
  apply injects_into_of_injection_into
  apply (injection_into_of_injects_into H).trans
  apply iSup_le; intro f
  exact le_iSup_of_le (powersetImageGraph X Y f) (powersetImageGraph_is_injective_function le_rfl)

end bSet.ErdosPowersetInjection
