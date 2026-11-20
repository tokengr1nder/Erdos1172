/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalRelationGraph
public import Erdos1172.Part4InternalCountableRealMatrix

@[expose] public section

/-!
# Partial real enumerations of arbitrary countable subsets

An injection of a subset into omega is reversed and composed with a fixed
ambient injection into the reals, using one explicit bounded relation graph.
The graph remains partial, so empty subsets need no special enumeration.
Equal graphs, or equal actual matrix codes, recover equal original subsets.
Congruence in both the subset and its index graph is unconditional.
No coherent family of enumeration choices or cardinality bound is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCountableRealEnumeration

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosRelationGraph ErdosCountableRealMatrix

local notation "Pω" => bv_powerset (bSet.omega : bSet 𝔹)

def enumRel (T j e n r : bSet 𝔹) : 𝔹 :=
  ⨆ x, x ∈ᴮ T ⊓ (pair x n ∈ᴮ j ⊓ pair x r ∈ᴮ e)

def enumGraph (T j e : bSet 𝔹) : bSet 𝔹 :=
  relationGraph bSet.omega Pω (enumRel T j e)

private theorem enumRel_ext_index (T j e r : bSet 𝔹) :
    B_ext (fun n => enumRel T j e n r) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_const
    (B_ext_inf B_ext_pair_mem_right B_ext_const))

private theorem enumRel_ext_value (T j e n : bSet 𝔹) :
    B_ext (enumRel T j e n) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_const
    (B_ext_inf B_ext_const B_ext_pair_mem_right))

theorem mem_enumGraph_iff {T j e n r : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair n r ∈ᴮ enumGraph T j e ↔
      Γ ≤ n ∈ᴮ bSet.omega ∧ Γ ≤ r ∈ᴮ Pω ∧ Γ ≤ enumRel T j e n r :=
  mem_relationGraph_iff (enumRel_ext_index T j e) (enumRel_ext_value T j e)

theorem enumGraph_witness {T j e n r : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ pair n r ∈ᴮ enumGraph T j e) :
    ∃ x : bSet 𝔹, Γ ≤ x ∈ᴮ T ⊓ (pair x n ∈ᴮ j ⊓ pair x r ∈ᴮ e) :=
  exists_convert (mem_enumGraph_iff.mp H).2.2
    (B_ext_inf B_ext_mem_left (B_ext_inf B_ext_pair_mem_left B_ext_pair_mem_left))

theorem enumGraph_mem {T j e n r x : bSet 𝔹} {Γ : 𝔹}
    (Hn : Γ ≤ n ∈ᴮ bSet.omega) (Hr : Γ ≤ r ∈ᴮ Pω)
    (Hx : Γ ≤ x ∈ᴮ T) (Hj : Γ ≤ pair x n ∈ᴮ j) (He : Γ ≤ pair x r ∈ᴮ e) :
    Γ ≤ pair n r ∈ᴮ enumGraph T j e :=
  mem_enumGraph_iff.mpr ⟨Hn, Hr, le_iSup_of_le x (le_inf Hx (le_inf Hj He))⟩

theorem enumGraph_subset {T j e : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ enumGraph T j e ⊆ᴮ prod bSet.omega Pω := relationGraph_subset

/-- Monotonicity is unconditional and does not presume functional or
total input graphs. -/
theorem enumGraph_mono {T U j k e : bSet 𝔹} {Γ : 𝔹}
    (HT : Γ ≤ T ⊆ᴮ U) (Hj : Γ ≤ j ⊆ᴮ k) :
    Γ ≤ enumGraph T j e ⊆ᴮ enumGraph U k e := by
  rw [subset_unfold']
  apply le_iInf
  intro z
  rw [← deduction]
  let Δ := Γ ⊓ z ∈ᴮ enumGraph T j e
  obtain ⟨n, Hn, r, Hr, Hz⟩ := mem_prod_iff₂.mp
    (mem_of_mem_subset enumGraph_subset
      (show Δ ≤ z ∈ᴮ enumGraph T j e from inf_le_right))
  have Hpair : Δ ≤ pair n r ∈ᴮ enumGraph T j e := mem_congr Hz bv_refl inf_le_right
  obtain ⟨x, Hx⟩ := enumGraph_witness Hpair
  have Hnew : Δ ≤ pair n r ∈ᴮ enumGraph U k e := enumGraph_mem Hn Hr
    (mem_of_mem_subset (inf_le_left.trans HT) (Hx.trans inf_le_left))
    (mem_of_mem_subset (inf_le_left.trans Hj) (Hx.trans (inf_le_right.trans inf_le_left)))
    (Hx.trans (inf_le_right.trans inf_le_right))
  exact mem_congr (bv_symm Hz) bv_refl Hnew

theorem enumGraph_congr_set (j e : bSet 𝔹) :
    B_congr (fun T => enumGraph T j e) := by
  intro T U Γ H
  exact subset_ext (enumGraph_mono (subset_of_eq H) subset_self)
    (enumGraph_mono (subset_of_eq (bv_symm H)) subset_self)

theorem enumGraph_congr_index (T e : bSet 𝔹) :
    B_congr (fun j => enumGraph T j e) := by
  intro j k Γ H
  exact subset_ext (enumGraph_mono subset_self (subset_of_eq H))
    (enumGraph_mono subset_self (subset_of_eq (bv_symm H)))

/-- Injectivity of the index graph and functionality of the ambient
real graph suffice for functionality of the partial enumeration. -/
theorem enumGraph_is_func {T j e : bSet 𝔹} {Γ : 𝔹}
    (He : Γ ≤ is_func e) (Hj : Γ ≤ is_inj j) :
    Γ ≤ is_func (enumGraph T j e) := by
  apply le_iInf
  intro n₁
  apply le_iInf
  intro n₂
  apply le_iInf
  intro r₁
  apply le_iInf
  intro r₂
  rw [← deduction, ← deduction]
  let Δ := (Γ ⊓ (pair n₁ r₁ ∈ᴮ enumGraph T j e ⊓ pair n₂ r₂ ∈ᴮ enumGraph T j e)) ⊓
    n₁ =ᴮ n₂
  have HΔ : Δ ≤ Γ := inf_le_left.trans inf_le_left
  obtain ⟨x₁, Hx₁⟩ := enumGraph_witness
    (show Δ ≤ pair n₁ r₁ ∈ᴮ enumGraph T j e from
      inf_le_left.trans (inf_le_right.trans inf_le_left))
  obtain ⟨x₂, Hx₂⟩ := enumGraph_witness
    (show Δ ≤ pair n₂ r₂ ∈ᴮ enumGraph T j e from
      inf_le_left.trans (inf_le_right.trans inf_le_right))
  have Hx : Δ ≤ x₁ =ᴮ x₂ := eq_of_is_inj_of_eq (HΔ.trans Hj) inf_le_right
    (Hx₁.trans (inf_le_right.trans inf_le_left)) (Hx₂.trans (inf_le_right.trans inf_le_left))
  exact eq_of_is_func_of_eq (HΔ.trans He) Hx
    (Hx₁.trans (inf_le_right.trans inf_le_right))
    (Hx₂.trans (inf_le_right.trans inf_le_right))

theorem enumGraph_is_func_of_injections {A T j e : bSet 𝔹} {Γ : 𝔹}
    (He : Γ ≤ is_injective_function A Pω e)
    (Hj : Γ ≤ is_injective_function T bSet.omega j) :
    Γ ≤ is_func (enumGraph T j e) :=
  enumGraph_is_func ((is_func'_of_is_injective_function He).trans inf_le_left)
    (Hj.trans inf_le_right)

/-- Totality of the original index injection and ambient real injection
recovers every member of T from the partial graph. -/
theorem subset_of_enumGraph_subset {A T U j k e : bSet 𝔹} {Γ : 𝔹}
    (He : Γ ≤ is_injective_function A Pω e) (HT : Γ ≤ T ⊆ᴮ A)
    (Hj : Γ ≤ is_injective_function T bSet.omega j)
    (Hgraph : Γ ≤ enumGraph T j e ⊆ᴮ enumGraph U k e) : Γ ≤ T ⊆ᴮ U := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  let Δ := Γ ⊓ x ∈ᴮ T
  have Hnex : Δ ≤ ⨆ n, n ∈ᴮ bSet.omega ⊓ pair x n ∈ᴮ j :=
    (le_inf (inf_le_left.trans
      ((is_total_of_is_function (Hj.trans inf_le_left)).trans (iInf_le _ x)))
      (show Δ ≤ x ∈ᴮ T from inf_le_right)).trans bv_imp_elim
  obtain ⟨n, Hn⟩ := exists_convert Hnex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have HxA : Δ ≤ x ∈ᴮ A := mem_of_mem_subset (inf_le_left.trans HT) inf_le_right
  have Hrex : Δ ≤ ⨆ r, r ∈ᴮ Pω ⊓ pair x r ∈ᴮ e :=
    (le_inf (inf_le_left.trans
      ((is_total_of_is_function (He.trans inf_le_left)).trans (iInf_le _ x))) HxA).trans
      bv_imp_elim
  obtain ⟨r, Hr⟩ := exists_convert Hrex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hpair : Δ ≤ pair n r ∈ᴮ enumGraph T j e :=
    enumGraph_mem (Hn.trans inf_le_left) (Hr.trans inf_le_left) inf_le_right
      (Hn.trans inf_le_right) (Hr.trans inf_le_right)
  obtain ⟨z, Hz⟩ := enumGraph_witness
    (mem_of_mem_subset (inf_le_left.trans Hgraph) Hpair)
  have Hxz : Δ ≤ x =ᴮ z := eq_of_is_inj_of_eq
    (inf_le_left.trans (He.trans inf_le_right)) bv_refl (Hr.trans inf_le_right)
    (Hz.trans (inf_le_right.trans inf_le_right))
  exact mem_congr (bv_symm Hxz) bv_refl (Hz.trans inf_le_left)

theorem eq_of_enumGraph_eq {A T U j k e : bSet 𝔹} {Γ : 𝔹}
    (He : Γ ≤ is_injective_function A Pω e)
    (HT : Γ ≤ T ⊆ᴮ A) (HU : Γ ≤ U ⊆ᴮ A)
    (Hj : Γ ≤ is_injective_function T bSet.omega j)
    (Hk : Γ ≤ is_injective_function U bSet.omega k)
    (Hgraph : Γ ≤ enumGraph T j e =ᴮ enumGraph U k e) : Γ ≤ T =ᴮ U :=
  subset_ext (subset_of_enumGraph_subset He HT Hj (subset_of_eq Hgraph))
    (subset_of_enumGraph_subset He HU Hk (subset_of_eq (bv_symm Hgraph)))

end bSet.ErdosCountableRealEnumeration
