/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4DualShioyaForcing

@[expose] public section

/-! # Freezing the projection below a common string extension

In the strong coding form of Definition 29 of Eskew and Hayut,
*Dense ideals*, the bits of the string include the cones of a dense
family of conditions. Two candidate projections transporting this
string into the same extension therefore agree locally on all Boolean
values. Separativity gives agreement of the projections at every common
domain point below the stronger condition, as in Lemma 31.
-/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion
universe u

namespace Erdos1172Shioya

theorem separative_condition_le_iff {P : Type u} [PartialOrder P] (hs : Separative P) (p q : P) :
    condition p ≤ condition q ↔ p ≤ q := by
  refine ⟨?_, fun h => condition_mono h⟩
  intro h
  by_contra hn
  obtain ⟨r, hrp, hbad⟩ := hs p q hn
  exact hbad ((mem_condition_iff q p).mp (condition_le_iff.mp h) r hrp)

private theorem dense_cones_sup {P : Type u} [Preorder P] (D : Set P)
    (hd : ∀ p : P, ∃ d ∈ D, d ≤ p) (b : Completion P) :
    b = ⨆ q : {q : D // condition q.val ≤ b}, condition q.val.val := by
  apply le_antisymm
  · apply le_of_dense_conditions_le D hd
    intro d hdb
    exact le_iSup (fun q : {q : D // condition q.val ≤ b} => condition q.val.val) ⟨d, hdb⟩
  · exact iSup_le fun q => q.property

private theorem part_iSup {I B C : Type u} [CompleteLattice B] [CompleteBooleanAlgebra C]
    (p : C) (e : CompleteLatticeHom B C) (b : B) (a : I → B) (hb : b = ⨆ i, a i) :
    p ⊓ e b = ⨆ i, p ⊓ e (a i) := by
  rw [hb, map_iSup, inf_iSup_eq]

namespace Condition

variable {κ θ : Cardinal.{u}}

def Codes (v : Condition κ θ) : Prop :=
  ∀ q : v.Poset, ∃ i : v.length.toOrd.val.ToType, v.bits i = condition q

def CodesDense (v : Condition κ θ) : Prop :=
  ∃ D : Set v.Poset, (∀ p : v.Poset, ∃ d ∈ D, d ≤ p) ∧
    ∀ q ∈ D, ∃ i : v.length.toOrd.val.ToType, v.bits i = condition q

theorem Codes.dense {v : Condition κ θ} (hc : v.Codes) : v.CodesDense :=
  ⟨Set.univ, fun p => ⟨p, Set.mem_univ _, le_rfl⟩, fun q _ => hc q⟩

variable {w v : Condition κ θ} (π σ : PartialProjection κ w.Poset v.Poset)
variable (hπ : condition w.point ≤ extensionValue π.booleanHom v.name w.name)
variable (hσ : condition w.point ≤ extensionValue σ.booleanHom v.name w.name)

include hπ hσ in
theorem CodesDense.freeze_booleanHom (hc : v.CodesDense) (b : v.Algebra) :
    condition w.point ⊓ π.booleanHom b = condition w.point ⊓ σ.booleanHom b := by
  obtain ⟨D, hd, hc⟩ := hc
  obtain ⟨lπ, aπ⟩ := (extensionValue_iff_bits π.booleanHom v.name w.name (condition_ne_bot w.point)).mp hπ
  obtain ⟨lσ, aσ⟩ := (extensionValue_iff_bits σ.booleanHom v.name w.name (condition_ne_bot w.point)).mp hσ
  have hcone (q : D) : condition w.point ⊓ π.booleanHom (condition q.val) =
      condition w.point ⊓ σ.booleanHom (condition q.val) := by
    obtain ⟨i, hi⟩ := hc q.val q.property
    have hp := (aπ i).trans (aσ i).symm
    simp only [name, StringName.bits_ofBits] at hp
    rw [hi] at hp
    exact hp
  let I := {q : D // condition q.val ≤ b}
  let a : I → v.Algebra := fun q => condition q.val.val
  have hsup : b = ⨆ i : I, a i := dense_cones_sup D hd b
  have expand (e : CompleteLatticeHom v.Algebra w.Algebra) :
      condition w.point ⊓ e b = ⨆ i : I, condition w.point ⊓ e (a i) :=
    part_iSup (B := v.Algebra) (C := w.Algebra) (condition w.point) e b a hsup
  calc
    _ = ⨆ i : I, condition w.point ⊓ π.booleanHom (a i) := expand π.booleanHom
    _ = ⨆ i : I, condition w.point ⊓ σ.booleanHom (a i) := iSup_congr fun i => hcone i.val
    _ = _ := (expand σ.booleanHom).symm

include hπ hσ in
theorem Codes.freeze_booleanHom (hc : v.Codes) (b : v.Algebra) :
    condition w.point ⊓ π.booleanHom b = condition w.point ⊓ σ.booleanHom b :=
  hc.dense.freeze_booleanHom π σ hπ hσ b

include hπ hσ in
theorem CodesDense.freeze_proj (hc : v.CodesDense) (r : w.Poset)
    (hr : r ≤ w.point) (hrπ : r ∈ π.dom) (hrσ : r ∈ σ.dom) :
    π.proj ⟨r, hrπ⟩ = σ.proj ⟨r, hrσ⟩ := by
  have htest (b : v.Algebra) : condition r ≤ π.booleanHom b ↔ condition r ≤ σ.booleanHom b := by
    have he := hc.freeze_booleanHom π σ hπ hσ b
    exact ⟨fun h => (le_inf (condition_mono hr) h).trans (he.le.trans inf_le_right),
      fun h => (le_inf (condition_mono hr) h).trans (he.ge.trans inf_le_right)⟩
  have hcone (b : v.Algebra) : condition (π.proj ⟨r, hrπ⟩) ≤ b ↔ condition (σ.proj ⟨r, hrσ⟩) ≤ b :=
    ((π.dom_condition ⟨r, hrπ⟩ b).symm.trans (htest b)).trans (σ.dom_condition ⟨r, hrσ⟩ b)
  exact le_antisymm ((separative_condition_le_iff v.separative _ _).mp ((hcone _).mpr le_rfl))
    ((separative_condition_le_iff v.separative _ _).mp ((hcone _).mp le_rfl))

include hπ hσ in
theorem Codes.freeze_proj (hc : v.Codes) (r : w.Poset)
    (hr : r ≤ w.point) (hrπ : r ∈ π.dom) (hrσ : r ∈ σ.dom) :
    π.proj ⟨r, hrπ⟩ = σ.proj ⟨r, hrσ⟩ :=
  hc.dense.freeze_proj π σ hπ hσ r hr hrπ hrσ

end Condition
end Erdos1172Shioya
