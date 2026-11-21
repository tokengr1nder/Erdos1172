/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalDenseBasisCore
public import Erdos1172.Part4CheckedOrdinalCardinality

@[expose] public section

/-! # An internal dense basis from weighted ordinal labels

Each weight specifies where its label is in the domain and where the
corresponding pair is in the graph. The cover of a positive set by the
small-loss values of these pairs is exactly the internal density law.
-/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
open Lattice
universe u

namespace bSet.ErdosWeightedDenseBasis

open ErdosIdeal ErdosDenseBasis ErdosOmegaTwo
variable {β : Type u} [NontrivialCompleteBooleanAlgebra β] (κ : Cardinal.{u})

def label (i : κ.ord.ToType) : bSet β := check (PSet.ordinalMk i.toOrd.val)

def domain (b : κ.ord.ToType → β) : bSet β := .mk κ.ord.ToType (label κ) b

theorem label_congr (X : κ.ord.ToType → bSet β) (i j : κ.ord.ToType) :
    label κ i =ᴮ label κ j ≤ X i =ᴮ X j := by
  by_cases hij : i = j
  · subst j
    exact bv_refl
  · have hne : ¬PSet.Equiv (PSet.ordinalMk i.toOrd.val) (PSet.ordinalMk j.toOrd.val) :=
      fun h => hij (Ordinal.ToType.mk.symm.injective (Subtype.ext (PSet.eq_of_mk_equiv h)))
    rw [label, label, check_bv_eq_bot_of_not_equiv hne]
    exact bot_le

def graph (b : κ.ord.ToType → β) (X : κ.ord.ToType → bSet β) : bSet β :=
  functionMk (u := domain κ b) X (label_congr κ X)

variable (b : κ.ord.ToType → β) (X : κ.ord.ToType → bSet β)

theorem label_mem (i : κ.ord.ToType) : b i ≤ label κ i ∈ᴮ domain κ b := mem_mk' (domain κ b) i

theorem pair_mem (i : κ.ord.ToType) : b i ≤ pair (label κ i) (X i) ∈ᴮ graph κ b X :=
  functionMk_self (u := domain κ b) (F := X) (h_congr := label_congr κ X)

theorem domain_subset_checked : (⊤ : β) ≤ domain κ b ⊆ᴮ check (PSet.ordinalMk κ.ord) := by
  rw [subset_unfold]
  apply le_iInf
  intro i
  rw [← deduction]
  exact le_top.trans (check_mem (PSet.mk_mem_mk_of_lt i.toOrd.property))

theorem domain_injects_into_omegaOne {Γ : β} (hκ : Γ ≤ check (PSet.ordinalMk κ.ord) =ᴮ omegaOne) :
    Γ ≤ injects_into (domain κ b) omegaOne :=
  injects_into_of_subset (bv_rw'' hκ (le_top.trans (domain_subset_checked κ b)) B_ext_subset_right)

theorem graph_is_function (K : bSet β) (hK : ∀ i, b i ≤ X i ⊆ᴮ K) :
    (⊤ : β) ≤ is_function (domain κ b) (bv_powerset K) (graph κ b X) := by
  refine le_inf (le_inf (functionMk_is_func (u := domain κ b) X (label_congr κ X)) ?_) ?_
  · apply le_iInf
    intro z
    rw [← deduction, top_inf_eq, mem_unfold]
    apply iSup_le
    intro i
    apply le_iSup_of_le (X i)
    refine le_inf (mem_powerset_iff.mpr (inf_le_left.trans (hK i))) ?_
    exact mem_congr (pair_congr (bv_symm inf_le_right) bv_refl) bv_refl
      (inf_le_left.trans (pair_mem κ b X i))
  · rw [subset_unfold]
    apply le_iInf
    intro i
    rw [← deduction, top_inf_eq]
    exact mem_prod_iff.mpr ⟨label_mem κ b i, mem_powerset_iff.mpr (hK i)⟩

theorem graph_positiveValues (K J : bSet β) (hp : ∀ i, b i ≤ positive K J (X i)) :
    (⊤ : β) ≤ positiveValues K J (domain κ b) (graph κ b X) := by
  apply le_iInf
  intro x
  apply le_iInf
  intro A
  rw [← deduction, top_inf_eq]
  apply inf_le_right.trans
  rw [mem_unfold]
  apply iSup_le
  intro i
  exact bv_rw' ((pair_eq_pair_iff.mp inf_le_right).2)
    (ϕ := positive K J) (h_congr := B_ext_inf B_ext_subset_left (B_ext_neg (h := B_ext_mem_left)))
    (H_new := inf_le_left.trans (hp i))

theorem graph_refinement_value (J A : bSet β) :
    (⨆ x : bSet β, ⨆ Y : bSet β, ((x ∈ᴮ domain κ b) ⊓ pair x Y ∈ᴮ graph κ b X) ⊓
      difference Y A ∈ᴮ J) = ⨆ i, b i ⊓ difference (X i) A ∈ᴮ J := by
  apply le_antisymm
  · apply iSup_le
    intro x
    apply iSup_le
    intro Y
    apply (inf_le_inf_right _ (inf_le_right : (x ∈ᴮ domain κ b) ⊓ pair x Y ∈ᴮ graph κ b X ≤ _)).trans
    rw [mem_unfold, iSup_inf_eq]
    apply iSup_le
    intro i
    apply le_iSup_of_le i
    exact le_inf (inf_le_left.trans inf_le_left)
      (mem_congr (difference_congr_left ((pair_eq_pair_iff.mp (inf_le_left.trans inf_le_right)).2))
        bv_refl inf_le_right)
  · apply iSup_le
    intro i
    apply le_iSup_of_le (label κ i)
    apply le_iSup_of_le (X i)
    exact le_inf (le_inf (inf_le_left.trans (label_mem κ b i)) (inf_le_left.trans (pair_mem κ b X i)))
      inf_le_right

theorem graph_denseValues_iff (K J : bSet β) (Γ : β) :
    Γ ≤ denseValues K J (domain κ b) (graph κ b X) ↔
      ∀ A : bSet β, Γ ⊓ positive K J A ≤ ⨆ i, b i ⊓ difference (X i) A ∈ᴮ J := by
  unfold denseValues
  simp only [le_iInf_iff, ← deduction, graph_refinement_value]

theorem basis_fields (K J : bSet β) {Γ : β}
    (hκ : Γ ≤ check (PSet.ordinalMk κ.ord) =ᴮ omegaOne)
    (hp : ∀ i, b i ≤ positive K J (X i))
    (hc : ∀ A : bSet β, Γ ⊓ positive K J A ≤ ⨆ i, b i ⊓ difference (X i) A ∈ᴮ J) :
    Γ ≤ is_function (domain κ b) (bv_powerset K) (graph κ b X) ∧
    Γ ≤ positiveValues K J (domain κ b) (graph κ b X) ∧
    Γ ≤ denseValues K J (domain κ b) (graph κ b X) ∧
    Γ ≤ injects_into (domain κ b) omegaOne :=
  ⟨le_top.trans (graph_is_function κ b X K (fun i => (hp i).trans inf_le_left)),
    le_top.trans (graph_positiveValues κ b X K J hp), (graph_denseValues_iff κ b X K J Γ).mpr hc,
    domain_injects_into_omegaOne κ b hκ⟩

end bSet.ErdosWeightedDenseBasis
