/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalCollapseMeet

@[expose] public section

/-! # Prefix coherence for independently constructed native collapse paths -/

set_option autoImplicit false
noncomputable section
universe u
open scoped Flypitch
open Lattice
namespace bSet.ErdosShioyaInternal.CollapsePath
open ErdosBoundedFunctionValue ErdosBoundedImageRecursion
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

private theorem image_sub_of_values {Γ : B} {V a b f g i : N} (hf : Γ ≤ is_function a V f)
    (hg : Γ ≤ is_function b V g) (ib : Γ ≤ i ⊆ᴮ b)
    (eq : ∀ {Δ : B}, Δ ≤ Γ → ∀ {j : N}, Δ ≤ j ∈ᴮ i → Δ ≤ graphValue V f j =ᴮ graphValue V g j) :
    Γ ≤ image i V f ⊆ᴮ image i V g := by
  rw [subset_unfold']
  refine le_iInf fun x => projection_imp.mpr ?_
  intro Δ hd hx
  have hv := mem_image_iff.mp hx
  obtain ⟨j,hj⟩ := exists_convert hv.2 (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  have ji := hj.trans inf_le_left
  have gx := bv_trans (bv_symm (eq hd ji)) (graphValue_eq_of_pair (hd.trans hf) (hj.trans inf_le_right))
  have gj := graphValue_pair_mem (hd.trans hg) (mem_of_mem_subset (hd.trans ib) ji)
  exact mem_image (mem_congr (pair_congr bv_refl gx) bv_refl gj) ji hv.1

private theorem images_eq {Γ : B} {V a b f g i : N} (hf : Γ ≤ is_function a V f)
    (hg : Γ ≤ is_function b V g) (ia : Γ ≤ i ⊆ᴮ a) (ib : Γ ≤ i ⊆ᴮ b)
    (eq : ∀ {Δ : B}, Δ ≤ Γ → ∀ {j : N}, Δ ≤ j ∈ᴮ i → Δ ≤ graphValue V f j =ᴮ graphValue V g j) :
    Γ ≤ image i V f =ᴮ image i V g :=
  subset_ext (image_sub_of_values hf hg ib eq) (image_sub_of_values hg hf ia fun d _ hj => bv_symm (eq d hj))

theorem length_mono {Γ : B} {P a b f g : N} (hf : Γ ≤ is_function a P f) (hg : Γ ≤ is_function b P g)
    (sub : Γ ≤ f ⊆ᴮ g) : Γ ≤ a ⊆ᴮ b := by
  rw [subset_unfold']
  exact le_iInf fun _ => projection_imp.mpr fun _ hd hj =>
    mem_domain_of_is_function (mem_of_mem_subset (hd.trans sub) (graphValue_pair_mem (hd.trans hf) hj)) (hd.trans hg)

/-- Arbitrary histories on comparable inputs coincide at every earlier row.
The proof uses membership induction inside the Boolean universe. -/
theorem prefix_rows {Γ : B} {P R a b f g h k : N} (ord : Γ ≤ Ord a)
    (hf : Γ ≤ is_function a P f) (hg : Γ ≤ is_function b P g) (sub : Γ ≤ f ⊆ᴮ g)
    (hh : Γ ≤ is_function a (bv_powerset P) h) (hk : Γ ≤ is_function b (bv_powerset P) k)
    (hlaw : Γ ≤ trace P R f h) (klaw : Γ ≤ trace P R g k) :
    ∀ {i : N} {Δ : B}, Δ ≤ Γ → Δ ≤ i ∈ᴮ a →
      Δ ≤ graphValue (bv_powerset P) h i =ᴮ graphValue (bv_powerset P) k i := by
  let V := bv_powerset P
  let good (i : N) := (i ∈ᴮ a) ⟹ (graphValue V h i =ᴮ graphValue V k i)
  have ext : B_ext good := B_ext_imp (h₁ := B_ext_mem_left)
    (h₂ := fun _ _ => bv_trans (bv_symm (graphValue_congr_input V h inf_le_left))
      (bv_trans inf_le_right (graphValue_congr_input V k inf_le_left)))
  have ab := length_mono hf hg sub
  have induction (i : N) : Γ ≤ good i := by
    apply epsilon_induction good ext _ i
    intro j
    apply projection_imp.mpr
    intro Δ hd previous
    apply projection_imp.mpr
    intro d dΔ ja
    have base := dΔ.trans hd
    have hja := subset_of_mem_transitive ((base.trans ord).trans inf_le_right) ja
    have jb := mem_of_mem_subset (base.trans ab) ja
    have frow := graphValue_pair_mem (base.trans hf) ja
    have value := bv_symm (graphValue_eq_of_pair (base.trans hg) (mem_of_mem_subset (base.trans sub) frow))
    have past : d ≤ image j V h =ᴮ image j V k := by
      apply images_eq (base.trans hh) (base.trans hk) hja (subset_trans' hja (base.trans ab))
      intro c cd z zj
      have ih := projection_imp.mp (previous.trans (iInf_le _ z)) c (cd.trans dΔ) zj
      exact projection_imp.mp ih c le_rfl (mem_of_mem_subset (cd.trans hja) zj)
    have left := imageRecLaw_apply (base.trans hlaw) (graphValue_pair_mem (base.trans hh) ja)
    have right := imageRecLaw_apply (base.trans klaw) (graphValue_pair_mem (base.trans hk) jb)
    exact bv_trans left (bv_trans (next_congr value past) (bv_symm right))
  exact fun {i} {Δ} hd hi => projection_imp.mp (induction i) Δ hd hi

theorem prefix_image {Γ : B} {P R a b f g h k : N} (ord : Γ ≤ Ord a)
    (hf : Γ ≤ is_function a P f) (hg : Γ ≤ is_function b P g) (sub : Γ ≤ f ⊆ᴮ g)
    (hh : Γ ≤ is_function a (bv_powerset P) h) (hk : Γ ≤ is_function b (bv_powerset P) k)
    (hlaw : Γ ≤ trace P R f h) (klaw : Γ ≤ trace P R g k) :
    Γ ≤ image a (bv_powerset P) h =ᴮ image a (bv_powerset P) k :=
  images_eq hh hk subset_self (length_mono hf hg sub) fun d _ hi => prefix_rows ord hf hg sub hh hk hlaw klaw d hi

end bSet.ErdosShioyaInternal.CollapsePath
