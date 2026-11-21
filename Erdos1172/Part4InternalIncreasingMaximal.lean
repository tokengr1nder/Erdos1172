/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalIncreasingPartial

@[expose] public section

/-!
# Maximal increasing partial graphs with initial range

All bounds and graphs are arbitrary Boolean-valued names. The source bound
is kept fixed throughout the family. Increasingness is preserved by an
internal inclusion-chain union, and initiality of the range is preserved
by every union of such graphs. Zorn then produces a genuine maximal member
of the concrete separated family. No ordinal or cardinal hypothesis is
needed, and totality of the maximal graph is not asserted here.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosIncreasingPartial

open ErdosPartition ErdosPartialInjection ErdosInjectionChain

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

theorem rangeMem_empty (θ x : bSet 𝔹) : rangeMem θ (∅ : bSet 𝔹) x = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro i
  exact bot_of_mem_empty inf_le_right

theorem empty_increasingOn {θ : bSet 𝔹} {Γ : 𝔹} : Γ ≤ increasingOn θ (∅ : bSet 𝔹) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro j
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  exact (bot_of_mem_empty (inf_le_right.trans (inf_le_right.trans inf_le_left))).trans bot_le

theorem empty_rangeInitial {θ A : bSet 𝔹} {Γ : 𝔹} : Γ ≤ rangeInitial θ A (∅ : bSet 𝔹) := by
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  have Hrange : Γ ⊓ ((rangeMem θ (∅ : bSet 𝔹) x ⊓ y ∈ᴮ A) ⊓ y ∈ᴮ x) ≤
      rangeMem θ (∅ : bSet 𝔹) x :=
    inf_le_right.trans (inf_le_left.trans inf_le_left)
  exact (Hrange.trans (rangeMem_empty θ x).le).trans bot_le

theorem empty_increasingPartial {θ A : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ increasingPartial θ A ∅ :=
  le_inf empty_partialGraph (le_inf empty_increasingOn empty_rangeInitial)

theorem empty_mem_increasingMaps {θ A : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ (∅ : bSet 𝔹) ∈ᴮ increasingMaps θ A :=
  mem_increasingMaps_iff.mpr empty_increasingPartial

theorem increasingMaps_nonempty {θ A : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ (increasingMaps θ A =ᴮ ∅)ᶜ :=
  nonempty_of_exists_mem (increasingMaps θ A) (le_iSup_of_le (∅ : bSet 𝔹) empty_mem_increasingMaps)

/-- Two graph pairs in an inclusion-chain union lie together in one
member, where the strict-increasing law applies. -/
theorem increasingOn_union_of_chain {θ C : bSet 𝔹} {Γ : 𝔹}
    (Hchain : Γ ≤ inclusionChain C)
    (Hfamily : Γ ≤ ⨅ f : bSet 𝔹, _root_.imp (f ∈ᴮ C) (increasingOn θ f)) :
    Γ ≤ increasingOn θ (bv_union C) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro j
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ (((i ∈ᴮ θ ⊓ j ∈ᴮ θ) ⊓ i ∈ᴮ j) ⊓ (pair i x ∈ᴮ bv_union C ⊓ pair j y ∈ᴮ bv_union C))
  have Hcommon : Δ ≤ ⨆ f : bSet 𝔹,
      f ∈ᴮ C ⊓ pair i x ∈ᴮ f ⊓ pair j y ∈ᴮ f :=
    exists_common_member_of_mem_union (inf_le_left.trans Hchain)
      (inf_le_right.trans (inf_le_right.trans inf_le_left))
      (inf_le_right.trans (inf_le_right.trans inf_le_right))
  obtain ⟨f, Hf⟩ := exists_convert Hcommon
    (B_ext_inf (B_ext_inf B_ext_mem_left B_ext_mem_right) B_ext_mem_right)
  have Hinc : Δ ≤ increasingOn θ f :=
    (le_inf (inf_le_left.trans (Hfamily.trans (iInf_le _ f)))
      (Hf.trans (inf_le_left.trans inf_le_left))).trans bv_imp_elim
  exact (le_inf
    (Hinc.trans ((iInf_le _ i).trans ((iInf_le _ j).trans ((iInf_le _ x).trans (iInf_le _ y)))))
    (le_inf (inf_le_right.trans inf_le_left)
      (le_inf (Hf.trans (inf_le_left.trans inf_le_right))
        (Hf.trans inf_le_right)))).trans bv_imp_elim

/-- Initiality of the used range survives any union with the same source
bound and target, without requiring an inclusion-chain hypothesis. -/
theorem rangeInitial_union {θ A C : bSet 𝔹} {Γ : 𝔹}
    (Hfamily : Γ ≤ ⨅ f : bSet 𝔹, _root_.imp (f ∈ᴮ C) (rangeInitial θ A f)) :
    Γ ≤ rangeInitial θ A (bv_union C) := by
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ ((rangeMem θ (bv_union C) x ⊓ y ∈ᴮ A) ⊓ y ∈ᴮ x)
  have Hrange : Δ ≤ rangeMem θ (bv_union C) x := inf_le_right.trans (inf_le_left.trans inf_le_left)
  obtain ⟨i, Hi⟩ := exists_convert Hrange (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  obtain ⟨f, Hf⟩ := exists_convert (mem_bv_union_iff.mp (Hi.trans inf_le_right))
    (B_ext_inf B_ext_mem_left B_ext_mem_right)
  have Hinitial : Δ ≤ rangeInitial θ A f :=
    (le_inf (inf_le_left.trans (Hfamily.trans (iInf_le _ f)))
      (Hf.trans inf_le_left)).trans bv_imp_elim
  have Hy : Δ ≤ rangeMem θ f y :=
    rangeInitial_apply Hinitial
      (rangeMem_of_pair (Hi.trans inf_le_left) (Hf.trans inf_le_right))
      (inf_le_right.trans (inf_le_left.trans inf_le_right))
      (inf_le_right.trans inf_le_right)
  have Hsub : Δ ≤ f ⊆ᴮ bv_union C :=
    (le_inf (le_top.trans ((bv_union_spec'' C).trans (iInf_le _ f)))
      (Hf.trans inf_le_left)).trans bv_imp_elim
  exact rangeMem_mono Hsub Hy

private theorem forall_mem_mono {C : bSet 𝔹} {P Q : bSet 𝔹 → 𝔹} {Γ : 𝔹}
    (H : Γ ≤ ⨅ f : bSet 𝔹, _root_.imp (f ∈ᴮ C) (P f))
    (HPQ : ∀ f, P f ≤ Q f) :
    Γ ≤ ⨅ f : bSet 𝔹, _root_.imp (f ∈ᴮ C) (Q f) := by
  apply le_iInf
  intro f
  rw [← deduction]
  exact ((le_inf (inf_le_left.trans (H.trans (iInf_le _ f))) inf_le_right).trans
    bv_imp_elim).trans (HPQ f)

/-- Every defining condition of the actual increasing partial graph is
preserved, including prefix-closed domain and initial used range. -/
theorem increasingPartial_union_of_chain {θ A C : bSet 𝔹} {Γ : 𝔹}
    (Hchain : Γ ≤ inclusionChain C)
    (Hfamily : Γ ≤ ⨅ f : bSet 𝔹, _root_.imp (f ∈ᴮ C) (increasingPartial θ A f)) :
    Γ ≤ increasingPartial θ A (bv_union C) :=
  le_inf
    (partialGraph_union_of_chain Hchain (forall_mem_mono Hfamily (fun _ => inf_le_left)))
    (le_inf
      (increasingOn_union_of_chain Hchain
        (forall_mem_mono Hfamily (fun _ => inf_le_right.trans inf_le_left)))
      (rangeInitial_union (forall_mem_mono Hfamily (fun _ => inf_le_right.trans inf_le_right))))

theorem increasingMaps_chain_union {θ A C : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ C ⊆ᴮ increasingMaps θ A) (Hchain : Γ ≤ inclusionChain C) :
    Γ ≤ bv_union C ∈ᴮ increasingMaps θ A := by
  apply mem_increasingMaps_iff.mpr
  apply increasingPartial_union_of_chain Hchain
  apply le_iInf
  intro f
  rw [← deduction]
  exact mem_increasingMaps_iff.mp (mem_of_mem_subset (inf_le_left.trans Hsub) inf_le_right)

theorem exists_maximal_increasingMap {θ A : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ ⨆ f : bSet 𝔹, f ∈ᴮ increasingMaps θ A ⊓
      ⨅ g : bSet 𝔹, _root_.imp (g ∈ᴮ increasingMaps θ A) (_root_.imp (f ⊆ᴮ g) (f =ᴮ g)) := by
  have Hclosure : Γ ≤ ⨅ C : bSet 𝔹,
      _root_.imp (C ⊆ᴮ increasingMaps θ A ⊓ inclusionChain C)
        (bv_union C ∈ᴮ increasingMaps θ A) := by
    apply le_iInf
    intro C
    rw [← deduction]
    exact increasingMaps_chain_union (inf_le_right.trans inf_le_left)
      (inf_le_right.trans inf_le_right)
  have Hzorn : Γ ≤ _root_.imp (increasingMaps θ A =ᴮ ∅)ᶜ
      (_root_.imp
        (⨅ C : bSet 𝔹,
          _root_.imp (C ⊆ᴮ increasingMaps θ A ⊓ inclusionChain C)
            (bv_union C ∈ᴮ increasingMaps θ A))
        (⨆ f : bSet 𝔹, f ∈ᴮ increasingMaps θ A ⊓
          ⨅ g : bSet 𝔹, _root_.imp (g ∈ᴮ increasingMaps θ A) (_root_.imp (f ⊆ᴮ g) (f =ᴮ g)))) :=
    (bSet_zorns_lemma' (Γ := Γ)).trans (iInf_le _ (increasingMaps θ A))
  exact (le_inf ((le_inf Hzorn increasingMaps_nonempty).trans bv_imp_elim)
    Hclosure).trans bv_imp_elim

/-- Zorn constructs a maximal increasing partial graph with initial range,
without any ordinal or cardinal assumptions on its two bounds. -/
theorem exists_maximal_increasingPartial {θ A : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ ⨆ f : bSet 𝔹, increasingPartial θ A f ⊓
      ⨅ g : bSet 𝔹, _root_.imp (increasingPartial θ A g) (_root_.imp (f ⊆ᴮ g) (f =ᴮ g)) := by
  simpa only [mem_increasingMaps] using (exists_maximal_increasingMap (θ := θ) (A := A) (Γ := Γ))

theorem maximal_increasingPartial_ext (θ A : bSet 𝔹) :
    B_ext (fun f : bSet 𝔹 => increasingPartial θ A f ⊓
      ⨅ g : bSet 𝔹, _root_.imp (increasingPartial θ A g) (_root_.imp (f ⊆ᴮ g) (f =ᴮ g))) :=
  B_ext_inf (increasingPartial_ext_graph θ A)
    (B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const)
      (h₂ := B_ext_imp (h₁ := B_ext_subset_left) (h₂ := B_ext_bv_eq_left))))

end bSet.ErdosIncreasingPartial
