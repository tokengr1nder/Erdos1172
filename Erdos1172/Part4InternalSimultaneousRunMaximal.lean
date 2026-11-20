/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSimultaneousRunPartial

@[expose] public section

/-!
Internal inclusion-chain unions preserve the exact entry laws of lawful
simultaneous prefixes. The original prefix of each entry is already total;
functionality of the union therefore preserves both decoded strict-past
histories. Internal Zorn then constructs a maximal lawful partial run.
Full domain and successful vertices are separate conclusions, not premises
or conclusions of the present maximality theorem.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousRun

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosInjectionChain ErdosPrefixFunction
open ErdosSimultaneousEntry ErdosSimultaneousHistory

/-- The chain premise is needed to establish functionality of the union,
not to transfer an individual old entry's exact laws. -/
theorem runLaw_union {color : Bool} {R S top C : bSet 𝔹} {Γ : 𝔹}
    (HfuncUnion : Γ ≤ is_func (bv_union C))
    (HrowFunctionsUnion : Γ ≤ rowFunctions (bv_union C))
    (Hfamily : Γ ≤ ⨅ P, _root_.imp (P ∈ᴮ C) (runPartial color R S top P)) :
    Γ ≤ runLaw color R S top (bv_union C) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro y
  apply le_iInf
  intro Z
  rw [← deduction]
  let Δ := Γ ⊓ pair i (pair y Z) ∈ᴮ bv_union C
  obtain ⟨P, HP⟩ := exists_convert (mem_bv_union_iff.mp
    (show Δ ≤ pair i (pair y Z) ∈ᴮ bv_union C from inf_le_right))
    (B_ext_inf B_ext_mem_left B_ext_mem_right)
  have Hpartial : Δ ≤ runPartial color R S top P :=
    (le_inf (inf_le_left.trans (Hfamily.trans (iInf_le _ P)))
      (HP.trans inf_le_left)).trans bv_imp_elim
  have Hsub : Δ ≤ P ⊆ᴮ bv_union C := ErdosIdeal.loss_subset_union (HP.trans inf_le_left)
  exact runEntry_of_extension Hsub (inf_le_left.trans HfuncUnion)
    (inf_le_left.trans HrowFunctionsUnion) Hpartial (HP.trans inf_le_right)

/-- All chains and their members are arbitrary internal names. No
injectivity, nonempty-chain, or successful-vertex premise is needed. -/
theorem runPartial_union_of_chain {color : Bool} {R S top C : bSet 𝔹} {Γ : 𝔹}
    (Hchain : Γ ≤ inclusionChain C)
    (Hfamily : Γ ≤ ⨅ P, _root_.imp (P ∈ᴮ C) (runPartial color R S top P)) :
    Γ ≤ runPartial color R S top (bv_union C) := by
  have HprefixFamily : Γ ≤ ⨅ P, _root_.imp (P ∈ᴮ C)
      (prefixGraph omegaOne entrySpace P) := by
    apply le_iInf
    intro P
    rw [← deduction]
    exact ((le_inf (inf_le_left.trans (Hfamily.trans (iInf_le _ P))) inf_le_right).trans
      bv_imp_elim).trans inf_le_left
  have HrowsFamily : Γ ≤ ⨅ P, _root_.imp (P ∈ᴮ C) (rowFunctions P) := by
    apply le_iInf
    intro P
    rw [← deduction]
    exact runPartial_rowFunctions
      ((le_inf (inf_le_left.trans (Hfamily.trans (iInf_le _ P))) inf_le_right).trans
        bv_imp_elim)
  have Hprefix : Γ ≤ prefixGraph omegaOne entrySpace (bv_union C) :=
    prefixGraph_union_of_chain Hchain HprefixFamily
  have Hrows : Γ ≤ rowFunctions (bv_union C) := rowFunctions_union HrowsFamily
  exact le_inf Hprefix (runLaw_union
    (Hprefix.trans (inf_le_right.trans inf_le_left)) Hrows Hfamily)

theorem runMaps_chain_union {color : Bool} {R S top C : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ C ⊆ᴮ runMaps color R S top) (Hchain : Γ ≤ inclusionChain C) :
    Γ ≤ bv_union C ∈ᴮ runMaps color R S top := by
  apply mem_runMaps_iff.mpr
  apply runPartial_union_of_chain Hchain
  apply le_iInf
  intro P
  rw [← deduction]
  exact mem_runMaps_iff.mp (mem_of_mem_subset (inf_le_left.trans Hsub) inf_le_right)

/-- Internal Zorn applies to the actual set of lawful prefixes, including
its empty member and the union of the empty chain. -/
theorem exists_maximal_runMap {color : Bool} {R S top : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ ⨆ P : bSet 𝔹, P ∈ᴮ runMaps color R S top ⊓
      ⨅ Q : bSet 𝔹, _root_.imp (Q ∈ᴮ runMaps color R S top)
        (_root_.imp (P ⊆ᴮ Q) (P =ᴮ Q)) := by
  have Hclosure : Γ ≤ ⨅ C : bSet 𝔹,
      _root_.imp (C ⊆ᴮ runMaps color R S top ⊓ inclusionChain C)
        (bv_union C ∈ᴮ runMaps color R S top) := by
    apply le_iInf
    intro C
    rw [← deduction]
    exact runMaps_chain_union (inf_le_right.trans inf_le_left)
      (inf_le_right.trans inf_le_right)
  have Hzorn : Γ ≤ _root_.imp (runMaps color R S top =ᴮ ∅)ᶜ
      (_root_.imp
        (⨅ C : bSet 𝔹,
          _root_.imp (C ⊆ᴮ runMaps color R S top ⊓ inclusionChain C)
            (bv_union C ∈ᴮ runMaps color R S top))
        (⨆ P : bSet 𝔹, P ∈ᴮ runMaps color R S top ⊓
          ⨅ Q : bSet 𝔹, _root_.imp (Q ∈ᴮ runMaps color R S top)
            (_root_.imp (P ⊆ᴮ Q) (P =ᴮ Q)))) :=
    (bSet_zorns_lemma' (Γ := Γ)).trans (iInf_le _ (runMaps color R S top))
  exact (le_inf ((le_inf Hzorn runMaps_nonempty).trans bv_imp_elim)
    Hclosure).trans bv_imp_elim

/-- A maximal lawful partial run is constructed without ideal or success
assumptions. Establishing full domain still requires a separate extension. -/
theorem exists_maximal_runPartial {color : Bool} {R S top : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ ⨆ P : bSet 𝔹, runPartial color R S top P ⊓
      ⨅ Q : bSet 𝔹, _root_.imp (runPartial color R S top Q)
        (_root_.imp (P ⊆ᴮ Q) (P =ᴮ Q)) := by
  simpa only [mem_runMaps] using
    (exists_maximal_runMap (color := color) (R := R) (S := S) (top := top) (Γ := Γ))

theorem maximal_runPartial_ext (color : Bool) (R S top : bSet 𝔹) :
    B_ext (fun P : bSet 𝔹 => runPartial color R S top P ⊓
      ⨅ Q : bSet 𝔹, _root_.imp (runPartial color R S top Q)
        (_root_.imp (P ⊆ᴮ Q) (P =ᴮ Q))) :=
  B_ext_inf (runPartial_ext_graph color R S top)
    (B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const)
      (h₂ := B_ext_imp (h₁ := B_ext_subset_left) (h₂ := B_ext_bv_eq_left))))

end bSet.ErdosSimultaneousRun
