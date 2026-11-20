/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalGreedyPartial

@[expose] public section

/-!
An actual maximal partial least-choice graph, constructed by internal Zorn.
For an old pair in a union, prefix closure makes its original graph total
on the earlier coordinates. Functionality of the union then fixes the
earlier image exactly, so the old least-choice rule remains true there.
All chains and graphs are arbitrary internal names. The maximal graph is
not assumed to have full domain; that requires a separate extension proof.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosGreedyPartial

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartialInjection ErdosInjectionChain
open ErdosRowCandidates ErdosOrdinalLeast

/-- Any functional union of greedy partial graphs preserves the exact
least-choice rule. The chain hypothesis is needed only to obtain a
functional union, not for the local least-choice transfer itself. -/
theorem greedyLaw_union {seed F C : bSet 𝔹} {Γ : 𝔹}
    (Hfunc : Γ ≤ is_func (bv_union C))
    (Hfamily : Γ ≤ ⨅ f, _root_.imp (f ∈ᴮ C) (greedyPartial seed F f)) :
    Γ ≤ greedyLaw seed F (bv_union C) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro x
  rw [← deduction]
  let Δ := Γ ⊓ pair i x ∈ᴮ bv_union C
  obtain ⟨f, Hf⟩ := exists_convert (mem_bv_union_iff.mp
    (show Δ ≤ pair i x ∈ᴮ bv_union C from inf_le_right))
    (B_ext_inf B_ext_mem_left B_ext_mem_right)
  have Hp : Δ ≤ greedyPartial seed F f :=
    (le_inf (inf_le_left.trans (Hfamily.trans (iInf_le _ f)))
      (Hf.trans inf_le_left)).trans bv_imp_elim
  have Hpair : Δ ≤ pair i x ∈ᴮ f := Hf.trans inf_le_right
  have Hsub : Δ ≤ f ⊆ᴮ bv_union C :=
    ErdosIdeal.loss_subset_union (Hf.trans inf_le_left)
  have Hprefix : Δ ≤ is_func' i omegaOne f := greedyPartial_is_func'_prefix Hp Hpair
  have Heq : Δ ≤ rowCandidates i seed F f =ᴮ rowCandidates i seed F (bv_union C) :=
    rowCandidates_eq_of_extension Hsub (inf_le_left.trans Hfunc) Hprefix
  exact bv_rw'' (ϕ := fun A => leastIn A x) Heq
    (greedyLaw_apply (Hp.trans inf_le_right) Hpair) (leastIn_ext_set x)

private theorem forall_mem_mono {C : bSet 𝔹} {P Q : bSet 𝔹 → 𝔹} {Γ : 𝔹}
    (H : Γ ≤ ⨅ f, _root_.imp (f ∈ᴮ C) (P f)) (HPQ : ∀ f, P f ≤ Q f) :
    Γ ≤ ⨅ f, _root_.imp (f ∈ᴮ C) (Q f) := by
  apply le_iInf
  intro f
  rw [← deduction]
  exact ((le_inf (inf_le_left.trans (H.trans (iInf_le _ f))) inf_le_right).trans
    bv_imp_elim).trans (HPQ f)

/-- Support, injectivity, prefix closure, and the exact least-choice rule
all survive an arbitrary internal inclusion-chain union. -/
theorem greedyPartial_union_of_chain {seed F C : bSet 𝔹} {Γ : 𝔹}
    (Hchain : Γ ≤ inclusionChain C)
    (Hfamily : Γ ≤ ⨅ f, _root_.imp (f ∈ᴮ C) (greedyPartial seed F f)) :
    Γ ≤ greedyPartial seed F (bv_union C) := by
  have Hpart : Γ ≤ partialGraph omegaOne omegaOne (bv_union C) :=
    partialGraph_union_of_chain Hchain (forall_mem_mono Hfamily (fun _ => inf_le_left))
  exact le_inf Hpart (greedyLaw_union
    (Hpart.trans (inf_le_right.trans inf_le_left)) Hfamily)

theorem greedyMaps_chain_union {seed F C : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ C ⊆ᴮ greedyMaps seed F) (Hchain : Γ ≤ inclusionChain C) :
    Γ ≤ bv_union C ∈ᴮ greedyMaps seed F := by
  apply mem_greedyMaps_iff.mpr
  apply greedyPartial_union_of_chain Hchain
  apply le_iInf
  intro f
  rw [← deduction]
  exact mem_greedyMaps_iff.mp
    (mem_of_mem_subset (inf_le_left.trans Hsub) inf_le_right)

/-- Internal Zorn applies to the actual separated family, including its
empty member and its empty-chain union. -/
theorem exists_maximal_greedyMap {seed F : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ ⨆ f : bSet 𝔹, f ∈ᴮ greedyMaps seed F ⊓
      ⨅ g : bSet 𝔹, _root_.imp (g ∈ᴮ greedyMaps seed F)
        (_root_.imp (f ⊆ᴮ g) (f =ᴮ g)) := by
  have Hclosure : Γ ≤ ⨅ C : bSet 𝔹,
      _root_.imp (C ⊆ᴮ greedyMaps seed F ⊓ inclusionChain C)
        (bv_union C ∈ᴮ greedyMaps seed F) := by
    apply le_iInf
    intro C
    rw [← deduction]
    exact greedyMaps_chain_union (inf_le_right.trans inf_le_left)
      (inf_le_right.trans inf_le_right)
  have Hzorn : Γ ≤ _root_.imp (greedyMaps seed F =ᴮ ∅)ᶜ
      (_root_.imp
        (⨅ C : bSet 𝔹,
          _root_.imp (C ⊆ᴮ greedyMaps seed F ⊓ inclusionChain C)
            (bv_union C ∈ᴮ greedyMaps seed F))
        (⨆ f : bSet 𝔹, f ∈ᴮ greedyMaps seed F ⊓
          ⨅ g : bSet 𝔹, _root_.imp (g ∈ᴮ greedyMaps seed F)
            (_root_.imp (f ⊆ᴮ g) (f =ᴮ g)))) :=
    (bSet_zorns_lemma' (Γ := Γ)).trans (iInf_le _ (greedyMaps seed F))
  exact (le_inf ((le_inf Hzorn greedyMaps_nonempty).trans bv_imp_elim)
    Hclosure).trans bv_imp_elim

/-- A maximal greedy partial graph is genuinely constructed, with no
ideal assumptions and no supplied successful run. Totality is not claimed. -/
theorem exists_maximal_greedyPartial {seed F : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ ⨆ f : bSet 𝔹, greedyPartial seed F f ⊓
      ⨅ g : bSet 𝔹, _root_.imp (greedyPartial seed F g)
        (_root_.imp (f ⊆ᴮ g) (f =ᴮ g)) := by
  simpa only [mem_greedyMaps] using
    (exists_maximal_greedyMap (seed := seed) (F := F) (Γ := Γ))

theorem maximal_greedyPartial_ext (seed F : bSet 𝔹) :
    B_ext (fun f : bSet 𝔹 => greedyPartial seed F f ⊓
      ⨅ g : bSet 𝔹, _root_.imp (greedyPartial seed F g)
        (_root_.imp (f ⊆ᴮ g) (f =ᴮ g))) :=
  B_ext_inf (greedyPartial_ext_graph seed F)
    (B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const)
      (h₂ := B_ext_imp (h₁ := B_ext_subset_left) (h₂ := B_ext_bv_eq_left))))

end bSet.ErdosGreedyPartial
