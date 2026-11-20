/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaRelativeTreeProjection
public import Erdos1172.Part4ShioyaProductTreeDomain
public import Erdos1172.Part4ShioyaProductRefinement

@[expose] public section

/-! # The relative collapse over a projected forcing

The product of the base with the collapse projects onto the given forcing.
The projection recovers the first coordinate exactly. Pullback along the two
successive projections therefore agrees on every Boolean value with pullback
along the ordinary first projection.
-/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion
universe u

namespace Erdos1172Shioya.PartialProjection

variable {κ : Cardinal.{u}} {P Q X : Type u} [PartialOrder P] [PartialOrder Q]
variable (π : PartialProjection κ Q P)

theorem exists_projected_greatest (hκ : Cardinal.aleph0 ≤ κ) (hQ : ShortInfima κ Q) :
    ∃ t : π.dom, (∀ a : π.dom, a ≤ t) ∧ ∀ p : P, p ≤ π.proj t := by
  let L := ULift.{u} (Fin 0)
  let f : L → π.dom := fun x => Fin.elim0 x.down
  have hL : Cardinal.mk L < κ := Cardinal.mk_lt_aleph0.trans_le hκ
  have hf : Antitone f := fun {x _} _ => Fin.elim0 x.down
  obtain ⟨t, ht⟩ := π.domShortInfima hQ L hL f hf
  have hp := π.proj_isGLB hQ hL f hf t ht
  refine ⟨t, fun _ => ht.2 ?_, fun _ => hp.2 ?_⟩ <;>
    rintro _ ⟨x, rfl⟩ <;> exact Fin.elim0 x.down

variable [Nonempty X] (d : X → π.dom) (hd : Function.Surjective d)
variable (hκ : κ.IsRegular) (hP : ShortInfima κ P) (hQ : ShortInfima κ Q)

def relativeCollapse : PartialProjection κ (P × Collapse.Condition κ X) Q :=
  (SynchronizedPath.relativeTree π d (π.exists_projected_greatest hκ.aleph0_le hQ).choose hQ hd
    (π.exists_projected_greatest hκ.aleph0_le hQ).choose_spec.2 hP hκ.aleph0_le).fromProductTree hκ

theorem relativeCollapse_base (z : (π.relativeCollapse d hd hκ hP hQ).dom) :
    ∃ hz : (π.relativeCollapse d hd hκ hP hQ).proj z ∈ π.dom,
      π.proj ⟨(π.relativeCollapse d hd hκ hP hQ).proj z, hz⟩ = z.val.1 := by
  let t := (π.exists_projected_greatest hκ.aleph0_le hQ).choose
  have ht : ∀ p : P, p ≤ π.proj t := (π.exists_projected_greatest hκ.aleph0_le hQ).choose_spec.2
  let τ := SynchronizedPath.relativeTree π d t hQ hd ht hP hκ.aleph0_le
  change ∃ hz : (τ.fromProductTree hκ).proj z ∈ π.dom, π.proj ⟨_, hz⟩ = _
  obtain ⟨a, hza, he⟩ := τ.fromProductTree_graph hκ z
  obtain ⟨ha, hbase⟩ := SynchronizedPath.relativeTree_base π d t hQ hd ht hP hκ.aleph0_le a
  rw [he]
  exact ⟨ha, hbase.trans (congrArg Prod.fst hza).symm⟩

include d hd hκ hP hQ in
theorem exists_relative_collapse :
    ∃ ρ : PartialProjection κ (P × Collapse.Condition κ X) Q, ∀ z : ρ.dom,
      ∃ hz : ρ.proj z ∈ π.dom, π.proj ⟨ρ.proj z, hz⟩ = z.val.1 :=
  ⟨π.relativeCollapse d hd hκ hP hQ, π.relativeCollapse_base d hd hκ hP hQ⟩

theorem booleanHom_of_first_coordinate {R : Type u} [PartialOrder R]
    (ρ : PartialProjection κ (P × R) Q)
    (hbase : ∀ z : ρ.dom, ∃ hz : ρ.proj z ∈ π.dom, π.proj ⟨ρ.proj z, hz⟩ = z.val.1)
    (r : R) : ρ.booleanHom.comp π.booleanHom =
      (productProjection (κ := κ) (OrderIso.refl (P × R)) r).booleanHom := by
  let σ := productProjection (κ := κ) (OrderIso.refl (P × R)) r
  ext b
  have hm (z : ρ.dom) : condition z.val ≤ ρ.booleanHom (π.booleanHom b) ↔ condition z.val ≤ σ.booleanHom b := by
    obtain ⟨hz, he⟩ := hbase z
    have h₁ := ρ.dom_condition z (π.booleanHom b)
    have h₂ := π.dom_condition ⟨ρ.proj z, hz⟩ b
    have h₃ := σ.dom_condition ⟨z.val, Set.mem_univ _⟩ b
    rw [he] at h₂
    exact (h₁.trans h₂).trans h₃.symm
  have hdense (p : P × R) : ∃ q ∈ ρ.dom, q ≤ p := by
    obtain ⟨q, hq⟩ := ρ.dense p
    exact ⟨q.val, q.property, hq⟩
  exact le_antisymm (le_of_dense_conditions_le ρ.dom hdense (fun z => (hm z).mp))
    (le_of_dense_conditions_le ρ.dom hdense (fun z => (hm z).mpr))

theorem relativeCollapse_booleanHom (c : Collapse.Condition κ X) :
    (π.relativeCollapse d hd hκ hP hQ).booleanHom.comp π.booleanHom =
      (productProjection (κ := κ) (OrderIso.refl (P × Collapse.Condition κ X)) c).booleanHom :=
  π.booleanHom_of_first_coordinate _ (π.relativeCollapse_base d hd hκ hP hQ) c

end Erdos1172Shioya.PartialProjection
