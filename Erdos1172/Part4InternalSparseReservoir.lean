/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalOmegaReservoir

@[expose] public section

/-!
Failure of neighborhood richness supplies an actual large internal reservoir
on which every neighborhood of the specified color is omega-one-small.
Fullness chooses the reservoir at the same Boolean context. Combining this
with the rich branch gives an exhaustive clique-or-sparse alternative, not
the full Dushnik--Miller relation or the requested Part 4 partition theorem.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSparseReservoir

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosGraphNeighborhood ErdosOmegaReservoir

theorem B_ext_large_neighborhood_base (color : Bool) (R x : bSet 𝔹) :
    B_ext (fun X => injects_into omegaTwo (neighborhood color R X x)) :=
  B_ext_term (ϕ := fun Y => injects_into omegaTwo Y)
    (t := fun X => neighborhood color R X x) B_ext_injects_into_right
    (neighborhood_base_congr color R x)

theorem B_ext_hasLargeNeighborhood (color : Bool) (R : bSet 𝔹) :
    B_ext (hasLargeNeighborhood color R) :=
  B_ext_iSup (h := fun x =>
    B_ext_inf B_ext_mem_right (B_ext_large_neighborhood_base color R x))

/-- The exact Boolean negation of richness is an internal existential over
large subreservoirs with no vertex having a large neighborhood. -/
theorem not_richNeighborhoods_value (color : Bool) (R S : bSet 𝔹) :
    (richNeighborhoods color R S)ᶜ =
      ⨆ X, (X ⊆ᴮ S ⊓ injects_into omegaTwo X) ⊓ (hasLargeNeighborhood color R X)ᶜ := by
  simp only [richNeighborhoods, compl_iInf, _root_.imp, compl_sup, compl_compl,
    hasLargeNeighborhood]

/-- Every internal vertex has a neighborhood of cardinality at most omega-one. -/
noncomputable def sparseNeighborhoods (color : Bool) (R X : bSet 𝔹) : 𝔹 :=
  ⨅ x, _root_.imp (x ∈ᴮ X)
    (injects_into (neighborhood color R X x) omegaOne)

theorem sparseNeighborhoods_apply {color : Bool} {R X x : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ sparseNeighborhoods color R X) (Hx : Γ ≤ x ∈ᴮ X) :
    Γ ≤ injects_into (neighborhood color R X x) omegaOne :=
  (le_inf (H.trans (iInf_le _ x)) Hx).trans bv_imp_elim

/-- The actual internal cardinal dichotomy converts absence of large
neighborhoods into smallness; no cardinal comparison is assumed. -/
theorem sparseNeighborhoods_of_not_large {color : Bool} {R X : bSet 𝔹} {Γ : 𝔹}
    (Hnot : Γ ≤ (hasLargeNeighborhood color R X)ᶜ) :
    Γ ≤ sparseNeighborhoods color R X := by
  apply le_iInf
  intro x
  rw [← deduction]
  let Δ := Γ ⊓ x ∈ᴮ X
  have HsmallSide : Δ ≤ (injects_into omegaTwo (neighborhood color R X x))ᶜ := by
    rw [← imp_bot, ← deduction]
    have Hlarge : Δ ⊓ injects_into omegaTwo (neighborhood color R X x) ≤
        hasLargeNeighborhood color R X :=
      le_iSup_of_le x (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
    exact bv_absurd _ Hlarge (inf_le_left.trans (inf_le_left.trans Hnot))
  have Hdichotomy := ErdosPartialInjection.omegaTwo_cardinal_dichotomy
    (S := neighborhood color R X x) (Γ := Δ)
  apply (le_inf Hdichotomy HsmallSide).trans
  rw [inf_sup_right]
  apply sup_le
  · exact inf_le_left
  · exact (bv_absurd _ inf_le_left inf_le_right).trans bot_le

/-- Fullness extracts the large sparse reservoir at exactly the original Γ.
The sparse branch requires neither CH nor an ordinal-domain assumption. -/
theorem exists_sparse_reservoir {color : Bool} {R S : bSet 𝔹} {Γ : 𝔹}
    (Hnot : Γ ≤ (richNeighborhoods color R S)ᶜ) :
    ∃ X : bSet 𝔹, (Γ ≤ X ⊆ᴮ S) ∧ (Γ ≤ injects_into omegaTwo X) ∧
      Γ ≤ sparseNeighborhoods color R X := by
  have Hfailure := Hnot
  rw [not_richNeighborhoods_value] at Hfailure
  have Hext : B_ext (fun X : bSet 𝔹 =>
      (X ⊆ᴮ S ⊓ injects_into omegaTwo X) ⊓ (hasLargeNeighborhood color R X)ᶜ) :=
    B_ext_inf (B_ext_inf B_ext_subset_left B_ext_injects_into_right)
      (B_ext_neg (h := B_ext_hasLargeNeighborhood color R))
  obtain ⟨X, HX⟩ := exists_convert Hfailure Hext
  exact ⟨X, HX.trans (inf_le_left.trans inf_le_left),
    HX.trans (inf_le_left.trans inf_le_right),
    sparseNeighborhoods_of_not_large (HX.trans inf_le_right)⟩

noncomputable def sparseReservoirValue (color : Bool) (R S : bSet 𝔹) : 𝔹 :=
  ⨆ X, (X ⊆ᴮ S ⊓ injects_into omegaTwo X) ⊓ sparseNeighborhoods color R X

theorem sparse_reservoir_value_of_not_rich {color : Bool} {R S : bSet 𝔹} {Γ : 𝔹}
    (Hnot : Γ ≤ (richNeighborhoods color R S)ᶜ) :
    Γ ≤ sparseReservoirValue color R S := by
  obtain ⟨X, HXS, HXlarge, HXsmall⟩ := exists_sparse_reservoir Hnot
  exact le_iSup_of_le X (le_inf (le_inf HXS HXlarge) HXsmall)

/-- Exhaustive Boolean alternative: an actual increasing internal omega
clique in the specified color, or a full-sized sparse subreservoir.
The second branch is not a homogeneous opposite-color omega-two clique. -/
theorem omega_clique_or_sparse_reservoir {color : Bool} {R S : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HS : Γ ≤ S ⊆ᴮ omegaTwo)
    (Hlarge : Γ ≤ injects_into omegaTwo S) :
    Γ ≤ (⨆ f, is_injective_function bSet.omega S f ⊓
      (increasingOn bSet.omega f ⊓ homogeneousUnion color R bSet.omega bSet.omega f f)) ⊔
      sparseReservoirValue color R S := by
  calc
    Γ = (Γ ⊓ richNeighborhoods color R S) ⊔ (Γ ⊓ (richNeighborhoods color R S)ᶜ) := by
      rw [← inf_sup_left, sup_compl_eq_top, inf_top_eq]
    _ ≤ _ := by
      apply sup_le
      · exact le_sup_of_le_left (internal_omega_clique_value
          (inf_le_left.trans HCH) (inf_le_left.trans HS)
          (inf_le_left.trans Hlarge) inf_le_right)
      · exact le_sup_of_le_right (sparse_reservoir_value_of_not_rich inf_le_right)

end bSet.ErdosSparseReservoir
