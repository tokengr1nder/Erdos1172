/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalBoundedImageRecursionMaximal
public import Erdos1172.Part4InternalBoundedImageRecursionExtension

@[expose] public section

/-!
# Constructing an actual bounded transfinite image-recursion

The step depends on the stage and the actual set of prior state values.
A maximal lawful prefix has full ordinal domain: a proper domain could
be extended by the bounded step value, contradicting maximality. No
recursive sequence, increasing hierarchy, successful branch, or closure
hull is supplied as a premise.

This image-history engine is sufficient for set-pool closure. It does
not erase the ordered coordinate history needed by block fusion.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosBoundedImageRecursion

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosPartialInjection ErdosPrefixFunction

theorem maximal_imageRec_domain_eq {θ V P : bSet 𝔹}
    {Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹} {Γ : 𝔹}
    (Hθ : Γ ≤ Ord θ)
    (Hstage : ∀ T, B_congr (fun i => Φ i T))
    (Hpast : ∀ i, B_congr (Φ i))
    (Hbound : Γ ≤ ⨅ i, ⨅ T, _root_.imp (i ∈ᴮ θ ⊓ T ⊆ᴮ V) (Φ i T ∈ᴮ V))
    (HP : Γ ≤ imageRecPartial θ V Φ P)
    (Hmax : Γ ≤ ⨅ Q, _root_.imp (imageRecPartial θ V Φ Q) (_root_.imp (P ⊆ᴮ Q) (P =ᴮ Q))) :
    Γ ≤ graphDomain θ V P =ᴮ θ := by
  let D := graphDomain θ V P
  have Hprefix : Γ ≤ prefixGraph θ V P := HP.trans inf_le_left
  have Hfunction : Γ ≤ is_function D V P := imageRecPartial_function HP
  have Hcases := ErdosInitialSegments.eq_or_mem_of_ordinal_subset
    (prefixGraph_domain_Ord Hθ Hprefix) Hθ
    (graphDomain_subset (κ := θ) (S := V) (f := P) (Γ := Γ))
  apply (le_inf (le_refl Γ) Hcases).trans
  rw [inf_sup_left]
  apply sup_le
  · exact inf_le_right
  · let Δ := Γ ⊓ D ∈ᴮ θ
    have HΔ : Δ ≤ Γ := inf_le_left
    let y := Φ D (image D V P)
    have Hy : Δ ≤ y ∈ᴮ V :=
      (le_inf (HΔ.trans (Hbound.trans
        ((iInf_le _ D).trans (iInf_le _ (image D V P)))))
        (le_inf (show Δ ≤ D ∈ᴮ θ from inf_le_right) image_subset)).trans bv_imp_elim
    have Hextended : Δ ≤ imageRecPartial θ V Φ (bSet.insert1 (pair D y) P) :=
      imageRecPartial_insert_next Hstage Hpast (HΔ.trans HP)
        (show Δ ≤ D ∈ᴮ θ from inf_le_right) Hy bv_refl
    have Heq : Δ ≤ P =ᴮ bSet.insert1 (pair D y) P :=
      (le_inf ((le_inf (HΔ.trans (Hmax.trans
        (iInf_le _ (bSet.insert1 (pair D y) P)))) Hextended).trans bv_imp_elim)
        ErdosInjectionExtension.subset_insertPair).trans bv_imp_elim
    have Hpair : Δ ≤ pair D y ∈ᴮ P :=
      mem_congr bv_refl (bv_symm Heq) ErdosInjectionExtension.pair_mem_insertPair
    exact (bot_of_mem_self' (mem_domain_of_is_function Hpair (HΔ.trans Hfunction))).trans bot_le

theorem exists_bounded_image_recursion {θ V : bSet 𝔹}
    {Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹} {Γ : 𝔹}
    (Hθ : Γ ≤ Ord θ)
    (Hstage : ∀ T, B_congr (fun i => Φ i T))
    (Hpast : ∀ i, B_congr (Φ i))
    (Hbound : Γ ≤ ⨅ i, ⨅ T, _root_.imp (i ∈ᴮ θ ⊓ T ⊆ᴮ V) (Φ i T ∈ᴮ V)) :
    ∃ P : bSet 𝔹, Γ ≤ is_function θ V P ⊓ imageRecLaw V Φ P := by
  obtain ⟨P, HP⟩ := exists_convert
    (exists_maximal_imageRecPartial (θ := θ) (V := V) (Γ := Γ) Hpast)
    (maximal_imageRecPartial_ext θ V Hpast)
  have Hpartial : Γ ≤ imageRecPartial θ V Φ P := HP.trans inf_le_left
  have Hdomain := maximal_imageRec_domain_eq Hθ Hstage Hpast Hbound Hpartial (HP.trans inf_le_right)
  exact ⟨P, le_inf
    (bv_rw'' (ϕ := fun D => is_function D V P) Hdomain
      (imageRecPartial_function Hpartial) B_ext_is_function_left)
    (Hpartial.trans inf_le_right)⟩

end bSet.ErdosBoundedImageRecursion
