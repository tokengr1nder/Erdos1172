/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalPartitionGraph
public import Erdos1172.Part4InternalRelationGraph

@[expose] public section

/-!
Actual colored neighborhoods of arbitrary internal relation names.
Extensionality permits the maximum principle to select a vertex carrying
a large neighborhood at the original Boolean context, without shrinking it
or assuming an externally coherent sequence of vertices.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosPartition

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

theorem graphColor_ext_left (color : Bool) (R y : bSet 𝔹) :
    B_ext (fun x => graphColor color R x y) := by
  cases color with
  | false =>
      change B_ext (fun x =>
        (x ∈ᴮ y ⊓ (pair x y ∈ᴮ R)ᶜ) ⊔ (y ∈ᴮ x ⊓ (pair y x ∈ᴮ R)ᶜ))
      exact B_ext_sup
        (h₁ := B_ext_inf B_ext_mem_left (B_ext_neg (h := B_ext_pair_mem_left)))
        (h₂ := B_ext_inf B_ext_mem_right (B_ext_neg (h := B_ext_pair_mem_right)))
  | true =>
      change B_ext (fun x =>
        (x ∈ᴮ y ⊓ pair x y ∈ᴮ R) ⊔ (y ∈ᴮ x ⊓ pair y x ∈ᴮ R))
      exact B_ext_sup
        (h₁ := B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
        (h₂ := B_ext_inf B_ext_mem_right B_ext_pair_mem_right)

theorem graphColor_ext_right (color : Bool) (R x : bSet 𝔹) : B_ext (graphColor color R x) := by
  intro y₁ y₂
  rw [graphColor_symm color R x y₁, graphColor_symm color R x y₂]
  exact graphColor_ext_left color R x y₁ y₂

end bSet.ErdosPartition

namespace bSet.ErdosGraphNeighborhood

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosPartition ErdosOmegaTwo ErdosRelationGraph

def neighborhood (color : Bool) (R X x : bSet 𝔹) : bSet 𝔹 :=
  comprehend (graphColor color R x) X

theorem mem_neighborhood_iff {color : Bool} {R X x y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ y ∈ᴮ neighborhood color R X x ↔ Γ ≤ y ∈ᴮ X ∧ Γ ≤ graphColor color R x y :=
  mem_comprehend_and (graphColor_ext_right color R x)

/-- Exact Boolean membership, not only an implication at top. -/
theorem mem_neighborhood (color : Bool) (R X x y : bSet 𝔹) :
    y ∈ᴮ neighborhood color R X x = (y ∈ᴮ X) ⊓ graphColor color R x y := by
  apply le_antisymm
  · have H := mem_neighborhood_iff.mp (le_refl (y ∈ᴮ neighborhood color R X x))
    exact le_inf H.1 H.2
  · exact mem_neighborhood_iff.mpr ⟨inf_le_left, inf_le_right⟩

theorem neighborhood_subset {color : Bool} {R X x : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ neighborhood color R X x ⊆ᴮ X :=
  comprehend_subset (ϕ := graphColor color R x) X

theorem neighborhood_congr (color : Bool) (R X : bSet 𝔹) : B_congr (neighborhood color R X) := by
  intro x₁ x₂ Γ Hx
  apply mem_ext
  · apply le_iInf
    intro y
    rw [← deduction]
    have Hy := mem_neighborhood_iff.mp
      (show Γ ⊓ y ∈ᴮ neighborhood color R X x₁ ≤ y ∈ᴮ neighborhood color R X x₁ from inf_le_right)
    exact mem_neighborhood_iff.mpr ⟨Hy.1,
      bv_rw'' (ϕ := fun x => graphColor color R x y)
        (inf_le_left.trans Hx) Hy.2 (graphColor_ext_left color R y)⟩
  · apply le_iInf
    intro y
    rw [← deduction]
    have Hy := mem_neighborhood_iff.mp
      (show Γ ⊓ y ∈ᴮ neighborhood color R X x₂ ≤ y ∈ᴮ neighborhood color R X x₂ from inf_le_right)
    exact mem_neighborhood_iff.mpr ⟨Hy.1,
      bv_rw' (ϕ := fun x => graphColor color R x y)
        (inf_le_left.trans Hx) (h_congr := graphColor_ext_left color R y)
        (H_new := Hy.2)⟩

theorem neighborhood_base_congr (color : Bool) (R x : bSet 𝔹) :
    B_congr (fun X => neighborhood color R X x) :=
  B_congr_comprehend (ϕ := graphColor color R x) (H_congr := graphColor_ext_right color R x)

theorem B_ext_large_neighborhood (color : Bool) (R X : bSet 𝔹) :
    B_ext (fun x => injects_into omegaTwo (neighborhood color R X x)) :=
  B_ext_term (ϕ := fun Y => injects_into omegaTwo Y)
    (t := neighborhood color R X) B_ext_injects_into_right
    (neighborhood_congr color R X)

/-- Some vertex of X has a full omega-two-large colored neighborhood in X. -/
noncomputable def hasLargeNeighborhood (color : Bool) (R X : bSet 𝔹) : 𝔹 :=
  ⨆ x, (x ∈ᴮ X) ⊓ injects_into omegaTwo (neighborhood color R X x)

/-- Fullness chooses a single name realizing both requirements at exactly Γ. -/
theorem exists_large_neighborhood {color : Bool} {R X : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ ⨆ x, (x ∈ᴮ X) ⊓ injects_into omegaTwo (neighborhood color R X x)) :
    ∃ x : bSet 𝔹, Γ ≤ x ∈ᴮ X ∧ Γ ≤ injects_into omegaTwo (neighborhood color R X x) := by
  obtain ⟨x, Hx⟩ := exists_convert H (B_ext_inf B_ext_mem_left (B_ext_large_neighborhood color R X))
  exact ⟨x, Hx.trans inf_le_left, Hx.trans inf_le_right⟩

end bSet.ErdosGraphNeighborhood
