/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalOrdinalLeast
public import Erdos1172.Part4InternalPartitionOrder
public import Erdos1172.Part4InternalRelationGraph

@[expose] public section

/-!
A strictly increasing self-map of an arbitrary internal ordinal never
decreases an index. The proof constructs the internal set of descending
indices and rules out its least member; it does not use a ground ordinal
enumeration, a global recursion hypothesis, CH, or an ideal.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosIncreasingSelfMap

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOrdinalLeast ErdosPartition

def descendingIndices (κ f : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun i => ⨆ x, pair i x ∈ᴮ f ⊓ x ∈ᴮ i) κ

theorem mem_descendingIndices_iff {κ f i : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ i ∈ᴮ descendingIndices κ f ↔ Γ ≤ i ∈ᴮ κ ∧ Γ ≤ ⨆ x, pair i x ∈ᴮ f ⊓ x ∈ᴮ i :=
  ErdosRelationGraph.mem_comprehend_and
    (B_ext_iSup (h := fun _ => B_ext_inf B_ext_pair_mem_left B_ext_mem_right))

theorem descendingIndices_subset {κ f : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ descendingIndices κ f ⊆ᴮ κ :=
  comprehend_subset (ϕ := fun i => ⨆ x, pair i x ∈ᴮ f ⊓ x ∈ᴮ i) κ

/-- A descending graph value forces a least descending index. Its image
is a smaller descending index, contradicting leastness. The graph may
contain arbitrary extra pairs outside the ordinal domain. -/
theorem bot_of_descending_value {κ f i x : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ) (Hf : Γ ≤ is_func' κ κ f)
    (Hinc : Γ ≤ increasingOn κ f) (Hi : Γ ≤ i ∈ᴮ κ)
    (Hix : Γ ≤ pair i x ∈ᴮ f) (Hxi : Γ ≤ x ∈ᴮ i) : Γ ≤ ⊥ := by
  have HiBad : Γ ≤ i ∈ᴮ descendingIndices κ f :=
    mem_descendingIndices_iff.mpr ⟨Hi, le_iSup_of_le x (le_inf Hix Hxi)⟩
  have Hnonempty : Γ ≤ (descendingIndices κ f =ᴮ ∅)ᶜ :=
    nonempty_of_exists_mem _ (le_iSup_of_le i HiBad)
  obtain ⟨j, Hj⟩ := exists_least_of_nonempty Hκ descendingIndices_subset Hnonempty
  have HjBad := mem_descendingIndices_iff.mp (leastIn_mem Hj)
  obtain ⟨y, Hy⟩ := exists_convert HjBad.2 (B_ext_inf B_ext_pair_mem_right B_ext_mem_left)
  have Hyκ : Γ ≤ y ∈ᴮ κ := mem_of_mem_Ord (Hy.trans inf_le_right) HjBad.1 Hκ
  have Htotal : Γ ≤ ⨆ z, z ∈ᴮ κ ⊓ pair y z ∈ᴮ f :=
    (le_inf ((Hf.trans inf_le_right).trans (iInf_le _ y)) Hyκ).trans bv_imp_elim
  obtain ⟨z, Hz⟩ := exists_convert Htotal (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hzy : Γ ≤ z ∈ᴮ y :=
    increasingOn_apply Hinc Hyκ HjBad.1 (Hy.trans inf_le_right)
      (Hz.trans inf_le_right) (Hy.trans inf_le_left)
  have HyBad : Γ ≤ y ∈ᴮ descendingIndices κ f :=
    mem_descendingIndices_iff.mpr ⟨Hyκ, le_iSup_of_le z (le_inf (Hz.trans inf_le_right) Hzy)⟩
  have Hmin : Γ ≤ j =ᴮ y ⊔ j ∈ᴮ y := leastIn_apply Hj HyBad
  apply (le_inf (le_refl Γ) Hmin).trans
  rw [inf_sup_left]
  apply sup_le
  · exact bot_of_mem_self'
      (mem_congr bv_refl inf_le_right (inf_le_left.trans (Hy.trans inf_le_right)))
  · exact bot_of_mem_mem' y j (inf_le_left.trans (Hy.trans inf_le_right)) inf_le_right

theorem value_not_below_index {κ f i x : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ) (Hf : Γ ≤ is_func' κ κ f)
    (Hinc : Γ ≤ increasingOn κ f) (Hi : Γ ≤ i ∈ᴮ κ)
    (Hix : Γ ≤ pair i x ∈ᴮ f) : Γ ≤ (x ∈ᴮ i)ᶜ := by
  rw [← imp_bot, ← deduction]
  exact bot_of_descending_value (inf_le_left.trans Hκ) (inf_le_left.trans Hf)
    (inf_le_left.trans Hinc) (inf_le_left.trans Hi) (inf_le_left.trans Hix) inf_le_right

/-- The nondecreasing law is an internal Boolean disjunction, not an
external case split on representations of the index and its value. -/
theorem index_le_value {κ f i x : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ) (Hf : Γ ≤ is_func' κ κ f)
    (Hinc : Γ ≤ increasingOn κ f) (Hi : Γ ≤ i ∈ᴮ κ)
    (Hix : Γ ≤ pair i x ∈ᴮ f) : Γ ≤ i =ᴮ x ⊔ i ∈ᴮ x := by
  have Hxκ : Γ ≤ x ∈ᴮ κ := value_mem_codomain Hf Hi Hix
  have Hnot : Γ ≤ (x ∈ᴮ i)ᶜ := value_not_below_index Hκ Hf Hinc Hi Hix
  have Htri := epsilon_trichotomy_of_Ord Hi Hxκ Hκ
  apply (le_inf (le_refl Γ) Htri).trans
  rw [inf_sup_left]
  exact sup_le inf_le_right ((bv_absurd _ inf_le_right (inf_le_left.trans Hnot)).trans bot_le)

theorem index_subset_value {κ f i x : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ) (Hf : Γ ≤ is_func' κ κ f)
    (Hinc : Γ ≤ increasingOn κ f) (Hi : Γ ≤ i ∈ᴮ κ)
    (Hix : Γ ≤ pair i x ∈ᴮ f) : Γ ≤ i ⊆ᴮ x := by
  apply (Ord.le_iff_lt_or_eq (Ord_of_mem_Ord Hi Hκ)
    (Ord_of_mem_Ord (value_mem_codomain Hf Hi Hix) Hκ)).mpr
  simpa only [sup_comm] using index_le_value Hκ Hf Hinc Hi Hix

end bSet.ErdosIncreasingSelfMap
