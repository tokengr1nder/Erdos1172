/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalPartialInjectionMaximal
public import Erdos1172.Part4InternalPartialInjectionDomain
public import Erdos1172.Part4InternalPartitionOrder
public import Erdos1172.Part4InternalRelationGraph

@[expose] public section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosIncreasingPartial

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosPartition ErdosPartialInjection

/-- The used range is an initial subset of A under membership. The source
bound stays fixed when a partial graph is extended. -/
def rangeInitial (θ A f : bSet 𝔹) : 𝔹 :=
  ⨅ x, ⨅ y, _root_.imp ((rangeMem θ f x ⊓ y ∈ᴮ A) ⊓ y ∈ᴮ x)
    (rangeMem θ f y)

def increasingPartial (θ A f : bSet 𝔹) : 𝔹 :=
  partialGraph θ A f ⊓ (increasingOn θ f ⊓ rangeInitial θ A f)

theorem rangeInitial_apply {θ A f x y : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ rangeInitial θ A f) (Hx : Γ ≤ rangeMem θ f x)
    (Hy : Γ ≤ y ∈ᴮ A) (Hyx : Γ ≤ y ∈ᴮ x) : Γ ≤ rangeMem θ f y :=
  (le_inf (H.trans ((iInf_le _ x).trans (iInf_le _ y)))
    (le_inf (le_inf Hx Hy) Hyx)).trans bv_imp_elim

theorem rangeMem_ext_graph (θ x : bSet 𝔹) : B_ext (fun f => rangeMem θ f x) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_mem_right)

theorem rangeMem_ext_value (θ f : bSet 𝔹) : B_ext (rangeMem θ f) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_pair_mem_right)

theorem increasingOn_ext_graph (θ : bSet 𝔹) : B_ext (increasingOn θ) := by
  unfold increasingOn
  exact B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_inf B_ext_const
        (B_ext_inf B_ext_mem_right B_ext_mem_right)) (h₂ := B_ext_const)))))

theorem rangeInitial_ext_graph (θ A : bSet 𝔹) : B_ext (rangeInitial θ A) :=
  B_ext_iInf (h := fun x => B_ext_iInf (h := fun y =>
    B_ext_imp (h₁ := B_ext_inf (B_ext_inf (rangeMem_ext_graph θ x) B_ext_const)
      B_ext_const) (h₂ := rangeMem_ext_graph θ y)))

def increasingMaps (θ A : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun f => increasingOn θ f ⊓ rangeInitial θ A f) (partialMaps θ A)

theorem mem_increasingMaps_iff {θ A f : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ f ∈ᴮ increasingMaps θ A ↔ Γ ≤ increasingPartial θ A f := by
  unfold increasingMaps
  rw [ErdosRelationGraph.mem_comprehend_and
    (B_ext_inf (increasingOn_ext_graph θ) (rangeInitial_ext_graph θ A))]
  constructor
  · rintro ⟨Hf, Ho⟩
    exact le_inf (mem_partialMaps_iff.mp Hf) Ho
  · intro H
    exact ⟨mem_partialMaps_iff.mpr (H.trans inf_le_left), H.trans inf_le_right⟩

theorem mem_increasingMaps (θ A f : bSet 𝔹) :
    f ∈ᴮ increasingMaps θ A = increasingPartial θ A f :=
  le_antisymm (mem_increasingMaps_iff.mp le_rfl) (mem_increasingMaps_iff.mpr le_rfl)

theorem increasingPartial_ext_graph (θ A : bSet 𝔹) : B_ext (increasingPartial θ A) := by
  intro f g
  rw [← mem_increasingMaps θ A f, ← mem_increasingMaps θ A g]
  exact B_ext_mem_left f g

theorem rangeMem_of_pair {θ f i x : bSet 𝔹} {Γ : 𝔹}
    (Hi : Γ ≤ i ∈ᴮ θ) (Hix : Γ ≤ pair i x ∈ᴮ f) : Γ ≤ rangeMem θ f x :=
  le_iSup_of_le i (le_inf Hi Hix)

theorem rangeMem_mono {θ f g x : bSet 𝔹} {Γ : 𝔹}
    (Hfg : Γ ≤ f ⊆ᴮ g) (Hx : Γ ≤ rangeMem θ f x) : Γ ≤ rangeMem θ g x := by
  obtain ⟨i, Hi⟩ := exists_convert Hx (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  exact rangeMem_of_pair (Hi.trans inf_le_left) (mem_of_mem_subset Hfg (Hi.trans inf_le_right))

theorem partial_rangeMem_iff_image {θ A f x : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ partialGraph θ A f) :
    Γ ≤ rangeMem θ f x ↔ Γ ≤ x ∈ᴮ image (graphDomain θ A f) A f := by
  have Hfunction := (partialGraph_function Hf).trans inf_le_left
  constructor
  · intro Hx
    obtain ⟨i, Hi⟩ := exists_convert Hx (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    exact mem_image (Hi.trans inf_le_right)
      (mem_domain_of_is_function (Hi.trans inf_le_right) Hfunction)
      (mem_codomain_of_is_function (Hi.trans inf_le_right) Hfunction)
  · intro Hx
    obtain ⟨i, Hi⟩ := exists_convert (mem_image_iff.mp Hx).2
      (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    exact rangeMem_of_pair (mem_of_mem_subset graphDomain_subset (Hi.trans inf_le_left))
      (Hi.trans inf_le_right)

end bSet.ErdosIncreasingPartial
