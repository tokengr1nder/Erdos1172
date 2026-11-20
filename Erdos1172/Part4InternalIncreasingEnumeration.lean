/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalIncreasingMaximal
public import Erdos1172.Part4InternalLeastUnused
public import Erdos1172.Part4InternalIncreasingExtension
public import Erdos1172.Part4InternalCardinalDichotomy

@[expose] public section

/-!
Actual increasing enumeration up to an initial ordinal, obtained by a
maximal increasing range-initial graph. Cardinality is not substituted for
order type: a least-unused-point extension proves that its domain is full.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosIncreasingPartial

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosPartialInjection ErdosPartition

theorem maximal_increasing_range_covers_of_domain_mem
    {θ κ A f : bSet 𝔹} {Γ : 𝔹}
    (Hθ : Γ ≤ Ord θ) (Hκ : Γ ≤ Ord κ) (HA : Γ ≤ A ⊆ᴮ κ)
    (Hf : Γ ≤ increasingPartial θ A f)
    (Hmax : Γ ≤ ⨅ g, _root_.imp (increasingPartial θ A g)
      (_root_.imp (f ⊆ᴮ g) (f =ᴮ g)))
    (HD : Γ ≤ graphDomain θ A f ∈ᴮ θ) :
    Γ ≤ A ⊆ᴮ image (graphDomain θ A f) A f := by
  let D := graphDomain θ A f
  have Hpart : Γ ≤ partialGraph θ A f := Hf.trans inf_le_left
  have Hfunction : Γ ≤ is_function D A f := (partialGraph_function Hpart).trans inf_le_left
  rw [subset_unfold']
  apply le_iInf
  intro u
  rw [← deduction, ← compl_compl (u ∈ᴮ image D A f), ← imp_bot, ← deduction]
  let Δ := (Γ ⊓ u ∈ᴮ A) ⊓ (u ∈ᴮ image D A f)ᶜ
  have HΔ : Δ ≤ Γ := inf_le_left.trans inf_le_left
  have Hnot : Δ ≤ (rangeMem θ f u)ᶜ := by
    rw [← imp_bot, ← deduction]
    have Him : Δ ⊓ rangeMem θ f u ≤ u ∈ᴮ image D A f :=
      (partial_rangeMem_iff_image (inf_le_left.trans (HΔ.trans Hpart))).mp inf_le_right
    exact bv_absurd _ Him (inf_le_left.trans inf_le_right)
  obtain ⟨y, Hy, Hfresh, Hleast⟩ := exists_least_unused (HΔ.trans Hpart)
    (show Δ ≤ u ∈ᴮ A from inf_le_left.trans inf_le_right) Hnot
  have Habove := range_below_unused (HΔ.trans Hκ) (HΔ.trans HA)
    (HΔ.trans Hpart) (HΔ.trans (Hf.trans (inf_le_right.trans inf_le_right))) Hy Hfresh
  have Hnew : Δ ≤ increasingPartial θ A (bSet.insert1 (pair D y) f) :=
    increasingPartial_insert_next (HΔ.trans Hθ) (HΔ.trans Hf) (HΔ.trans HD)
      Hy Hfresh Habove Hleast
  have Heq : Δ ≤ f =ᴮ bSet.insert1 (pair D y) f :=
    (le_inf ((le_inf (HΔ.trans (Hmax.trans (iInf_le _ (bSet.insert1 (pair D y) f))))
      Hnew).trans bv_imp_elim) ErdosInjectionExtension.subset_insertPair).trans bv_imp_elim
  have Hpair : Δ ≤ pair D y ∈ᴮ f :=
    mem_congr bv_refl (bv_symm Heq) ErdosInjectionExtension.pair_mem_insertPair
  exact bot_of_mem_self' (mem_domain_of_is_function Hpair (HΔ.trans Hfunction))

/-- Initiality rules out a proper maximal domain, because its range would
otherwise cover A and give an injection of theta into a strict predecessor. -/
theorem maximal_increasing_domain_eq {θ κ A f : bSet 𝔹} {Γ : 𝔹}
    (Hθ : Γ ≤ ErdosHartogs.initialOrdinal θ) (Hκ : Γ ≤ Ord κ)
    (HA : Γ ≤ A ⊆ᴮ κ) (Hlarge : Γ ≤ injects_into θ A)
    (Hf : Γ ≤ increasingPartial θ A f)
    (Hmax : Γ ≤ ⨅ g, _root_.imp (increasingPartial θ A g)
      (_root_.imp (f ⊆ᴮ g) (f =ᴮ g))) :
    Γ ≤ graphDomain θ A f =ᴮ θ := by
  have Hθord := ErdosHartogs.Ord_of_initialOrdinal Hθ
  have Hpart : Γ ≤ partialGraph θ A f := Hf.trans inf_le_left
  have HDord := partialGraph_domain_Ord Hθord Hpart
  have Hcases := ErdosInitialSegments.eq_or_mem_of_ordinal_subset HDord Hθord
    (graphDomain_subset (κ := θ) (S := A) (f := f) (Γ := Γ))
  apply (le_inf (le_refl Γ) Hcases).trans
  rw [inf_sup_left]
  apply sup_le
  · exact inf_le_right
  · let Δ := Γ ⊓ graphDomain θ A f ∈ᴮ θ
    have Hcover : Δ ≤ A ⊆ᴮ image (graphDomain θ A f) A f :=
      maximal_increasing_range_covers_of_domain_mem (inf_le_left.trans Hθord)
        (inf_le_left.trans Hκ) (inf_le_left.trans HA) (inf_le_left.trans Hf)
        (inf_le_left.trans Hmax) inf_le_right
    have Hback := injection_back_of_range_covers
      (partialGraph_function (inf_le_left.trans Hpart)) Hcover
    exact (bv_absurd _ (injects_into_trans (inf_le_left.trans Hlarge) Hback)
      (ErdosHartogs.not_injects_of_initialOrdinal (inf_le_left.trans Hθ)
        (show Δ ≤ graphDomain θ A f ∈ᴮ θ from inf_le_right))).trans bot_le

/-- A cardinal-sized subset of an ordinal admits an actual increasing
injection from the corresponding initial ordinal. No CH is required. -/
theorem exists_increasing_injection {θ κ A : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ) (HA : Γ ≤ A ⊆ᴮ κ)
    (Hθ : Γ ≤ ErdosHartogs.initialOrdinal θ) (Hlarge : Γ ≤ injects_into θ A) :
    ∃ f : bSet 𝔹, Γ ≤ is_injective_function θ A f ⊓
      (increasingOn θ f ⊓ rangeInitial θ A f) := by
  obtain ⟨f, Hf⟩ := exists_convert
    (exists_maximal_increasingPartial (θ := θ) (A := A) (Γ := Γ))
    (maximal_increasingPartial_ext θ A)
  have Hp : Γ ≤ increasingPartial θ A f := Hf.trans inf_le_left
  have Hdom := maximal_increasing_domain_eq Hθ Hκ HA Hlarge Hp (Hf.trans inf_le_right)
  have Hinj := partialGraph_function (Hp.trans inf_le_left)
  exact ⟨f, le_inf
    (bv_rw'' (ϕ := fun D => is_injective_function D A f) Hdom Hinj
      B_ext_is_injective_function_left)
    (Hp.trans inf_le_right)⟩

end bSet.ErdosIncreasingPartial
