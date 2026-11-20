/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalRelationChoice
public import Erdos1172.Part4InternalRelationGraph

@[expose] public section

/-!
# Noninjective functions with ordinal-prefix domains

A stopped run can repeat its endpoint, and different row coordinates can
coincide. This family therefore imposes functionality and prefix closure,
not injectivity. Its actual internal chain unions preserve those laws.
At a proper domain one more arbitrary bounded value can be adjoined.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosPrefixFunction

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosPartialInjection ErdosInjectionChain ErdosInjectionExtension
open ErdosRelationGraph ErdosRelationChoice

def prefixGraph (κ S f : bSet 𝔹) : 𝔹 :=
  (f ⊆ᴮ prod κ S) ⊓ (is_func f ⊓ prefixClosed S f)

theorem is_func_ext_graph : B_ext (is_func : bSet 𝔹 → 𝔹) := by
  unfold is_func
  exact B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_inf B_ext_mem_right B_ext_mem_right) (h₂ := B_ext_const)))))

theorem prefixGraph_ext_graph (κ S : bSet 𝔹) : B_ext (prefixGraph κ S) :=
  B_ext_inf B_ext_subset_left (B_ext_inf is_func_ext_graph (B_ext_prefixClosed S))

def prefixMaps (κ S : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun f => is_func f ⊓ prefixClosed S f) (bv_powerset (prod κ S))

theorem mem_prefixMaps_iff {κ S f : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ f ∈ᴮ prefixMaps κ S ↔ Γ ≤ prefixGraph κ S f := by
  unfold prefixMaps
  rw [mem_comprehend_and (B_ext_inf is_func_ext_graph (B_ext_prefixClosed S))]
  constructor
  · rintro ⟨Hsub, Hlaw⟩
    exact le_inf (mem_powerset_iff.mp Hsub) Hlaw
  · intro H
    exact ⟨mem_powerset_iff.mpr (H.trans inf_le_left), H.trans inf_le_right⟩

theorem prefixGraph_function {κ S f : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ prefixGraph κ S f) :
    Γ ≤ is_function (graphDomain κ S f) S f :=
  function_on_graphDomain (H.trans inf_le_left) (H.trans (inf_le_right.trans inf_le_left))

theorem prefixGraph_domain_Ord {κ S f : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ) (H : Γ ≤ prefixGraph κ S f) :
    Γ ≤ Ord (graphDomain κ S f) :=
  ErdosInitialSegments.Ord_of_transitive_subset Hκ graphDomain_subset
    (graphDomain_transitive Hκ (H.trans (inf_le_right.trans inf_le_right)))

theorem prefixGraph_is_func'_prefix {κ S f i x : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ prefixGraph κ S f) (Hpair : Γ ≤ pair i x ∈ᴮ f) :
    Γ ≤ is_func' i S f := by
  refine le_inf (H.trans (inf_le_right.trans inf_le_left)) ?_
  apply le_iInf
  intro j
  rw [← deduction]
  exact prefixClosed_apply
    (inf_le_left.trans (H.trans (inf_le_right.trans inf_le_right)))
    (inf_le_left.trans Hpair) inf_le_right

theorem empty_prefixGraph {κ S : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ prefixGraph κ S (∅ : bSet 𝔹) := by
  refine le_inf empty_subset (le_inf ((is_func'_empty (x := S)).trans inf_le_left) ?_)
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  apply le_iInf
  intro z
  rw [← deduction]
  exact (bot_of_mem_empty (inf_le_right.trans inf_le_left)).trans bot_le

theorem prefixGraph_union_of_chain {κ S T : bSet 𝔹} {Γ : 𝔹}
    (Hchain : Γ ≤ inclusionChain T)
    (Hfamily : Γ ≤ ⨅ f, _root_.imp (f ∈ᴮ T) (prefixGraph κ S f)) :
    Γ ≤ prefixGraph κ S (bv_union T) := by
  have Hsub : Γ ≤ ⨅ f, _root_.imp (f ∈ᴮ T) (f ⊆ᴮ prod κ S) := by
    apply le_iInf
    intro f
    rw [← deduction]
    exact ((le_inf (inf_le_left.trans (Hfamily.trans (iInf_le _ f))) inf_le_right).trans
      bv_imp_elim).trans inf_le_left
  have Hfunc : Γ ≤ ⨅ f, _root_.imp (f ∈ᴮ T) (is_func f) := by
    apply le_iInf
    intro f
    rw [← deduction]
    exact ((le_inf (inf_le_left.trans (Hfamily.trans (iInf_le _ f))) inf_le_right).trans
      bv_imp_elim).trans (inf_le_right.trans inf_le_left)
  have Hprefix : Γ ≤ ⨅ f, _root_.imp (f ∈ᴮ T) (prefixClosed S f) := by
    apply le_iInf
    intro f
    rw [← deduction]
    exact ((le_inf (inf_le_left.trans (Hfamily.trans (iInf_le _ f))) inf_le_right).trans
      bv_imp_elim).trans (inf_le_right.trans inf_le_right)
  exact le_inf (union_subset_of_forall_subset Hsub)
    (le_inf (is_func_union_of_chain Hchain Hfunc) (prefixClosed_union Hprefix))

/-- The next value need not be fresh: only the domain coordinate is new. -/
theorem prefixGraph_insert_next {κ S f y : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ prefixGraph κ S f)
    (HD : Γ ≤ graphDomain κ S f ∈ᴮ κ) (Hy : Γ ≤ y ∈ᴮ S) :
    Γ ≤ prefixGraph κ S (bSet.insert1 (pair (graphDomain κ S f) y) f) := by
  let D := graphDomain κ S f
  have Hfunc : Γ ≤ is_function D S f := prefixGraph_function Hf
  have Hnot : Γ ≤ (D ∈ᴮ D)ᶜ := by
    rw [← imp_bot, ← deduction]
    exact bot_of_mem_self' inf_le_right
  refine le_inf (insert_subset_of_mem (Hf.trans inf_le_left) (mem_prod HD Hy))
    (le_inf (is_func_insertPair Hfunc Hnot) ?_)
  apply le_iInf
  intro i
  apply le_iInf
  intro v
  apply le_iInf
  intro j
  rw [← deduction]
  let Δ := Γ ⊓ (pair i v ∈ᴮ bSet.insert1 (pair D y) f ⊓ j ∈ᴮ i)
  have Hpair : Δ ≤ pair i v =ᴮ pair D y ⊔ pair i v ∈ᴮ f := by
    rw [← mem_insert1]
    exact inf_le_right.trans inf_le_left
  have Hold : ∀ {Λ : 𝔹}, Λ ≤ Γ →
      Λ ≤ ⨆ w, w ∈ᴮ S ⊓ pair j w ∈ᴮ f →
      Λ ≤ ⨆ w, w ∈ᴮ S ⊓ pair j w ∈ᴮ bSet.insert1 (pair D y) f := by
    intro Λ _ Hw
    obtain ⟨w, Hw⟩ := exists_convert Hw (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
    exact le_iSup_of_le w (le_inf (Hw.trans inf_le_left)
      (mem_of_mem_subset subset_insertPair (Hw.trans inf_le_right)))
  apply (le_inf (le_refl Δ) Hpair).trans
  rw [inf_sup_left]
  apply sup_le
  · apply Hold (inf_le_left.trans inf_le_left)
    have HjD : Δ ⊓ pair i v =ᴮ pair D y ≤ j ∈ᴮ D :=
      mem_congr bv_refl (eq_of_eq_pair_left' inf_le_right)
        (inf_le_left.trans (inf_le_right.trans inf_le_right))
    exact (le_inf (inf_le_left.trans (inf_le_left.trans
      ((is_total_of_is_function Hfunc).trans (iInf_le _ j)))) HjD).trans bv_imp_elim
  · apply Hold (inf_le_left.trans inf_le_left)
    exact prefixClosed_apply
      (inf_le_left.trans (inf_le_left.trans (Hf.trans (inf_le_right.trans inf_le_right))))
      inf_le_right (inf_le_left.trans (inf_le_right.trans inf_le_right))

end bSet.ErdosPrefixFunction
