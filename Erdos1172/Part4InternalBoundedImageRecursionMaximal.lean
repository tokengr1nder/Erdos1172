/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalBoundedImageRecursion

@[expose] public section

/-!
# Maximal actual prefixes for bounded image recursion

Internal Zorn applies to the actual set of lawful prefix graphs. Its
chains are arbitrary internal names, and empty chains are covered. This
constructs a maximal prefix without assuming a recursive sequence or a
closure hierarchy. Totality is established separately by extension.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosBoundedImageRecursion

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosInjectionChain

theorem exists_maximal_imageRecMap {θ V : bSet 𝔹}
    {Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹} {Γ : 𝔹}
    (Hpast : ∀ i, B_congr (Φ i)) :
    Γ ≤ ⨆ P : bSet 𝔹, P ∈ᴮ imageRecMaps θ V Φ ⊓
      ⨅ Q : bSet 𝔹, _root_.imp (Q ∈ᴮ imageRecMaps θ V Φ)
        (_root_.imp (P ⊆ᴮ Q) (P =ᴮ Q)) := by
  have Hclosure : Γ ≤ ⨅ C : bSet 𝔹,
      _root_.imp (C ⊆ᴮ imageRecMaps θ V Φ ⊓ inclusionChain C)
        (bv_union C ∈ᴮ imageRecMaps θ V Φ) := by
    apply le_iInf
    intro C
    rw [← deduction]
    exact imageRecMaps_chain_union Hpast (inf_le_right.trans inf_le_left)
      (inf_le_right.trans inf_le_right)
  have Hzorn : Γ ≤ _root_.imp (imageRecMaps θ V Φ =ᴮ ∅)ᶜ
      (_root_.imp
        (⨅ C : bSet 𝔹,
          _root_.imp (C ⊆ᴮ imageRecMaps θ V Φ ⊓ inclusionChain C)
            (bv_union C ∈ᴮ imageRecMaps θ V Φ))
        (⨆ P : bSet 𝔹, P ∈ᴮ imageRecMaps θ V Φ ⊓
          ⨅ Q : bSet 𝔹, _root_.imp (Q ∈ᴮ imageRecMaps θ V Φ)
            (_root_.imp (P ⊆ᴮ Q) (P =ᴮ Q)))) :=
    (bSet_zorns_lemma' (Γ := Γ)).trans (iInf_le _ (imageRecMaps θ V Φ))
  exact (le_inf ((le_inf Hzorn (imageRecMaps_nonempty Hpast)).trans bv_imp_elim)
    Hclosure).trans bv_imp_elim

theorem exists_maximal_imageRecPartial {θ V : bSet 𝔹}
    {Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹} {Γ : 𝔹}
    (Hpast : ∀ i, B_congr (Φ i)) :
    Γ ≤ ⨆ P : bSet 𝔹, imageRecPartial θ V Φ P ⊓
      ⨅ Q : bSet 𝔹, _root_.imp (imageRecPartial θ V Φ Q)
        (_root_.imp (P ⊆ᴮ Q) (P =ᴮ Q)) := by
  simpa only [mem_imageRecMaps Hpast] using
    (exists_maximal_imageRecMap (θ := θ) (V := V) (Γ := Γ) Hpast)

theorem maximal_imageRecPartial_ext (θ V : bSet 𝔹)
    {Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹} (Hpast : ∀ i, B_congr (Φ i)) :
    B_ext (fun P : bSet 𝔹 => imageRecPartial θ V Φ P ⊓
      ⨅ Q : bSet 𝔹, _root_.imp (imageRecPartial θ V Φ Q)
        (_root_.imp (P ⊆ᴮ Q) (P =ᴮ Q))) :=
  B_ext_inf (imageRecPartial_ext_graph θ V Φ Hpast)
    (B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const)
      (h₂ := B_ext_imp (h₁ := B_ext_subset_left) (h₂ := B_ext_bv_eq_left))))

end bSet.ErdosBoundedImageRecursion
