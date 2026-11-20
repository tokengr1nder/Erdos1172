/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ClosedPartialProjection
public import Erdos1172.Part4DenseCompletionCardinality

@[expose] public section

/-! # Boolean embeddings from projections defined on dense domains -/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion Erdos1172PosetProjection
universe u

namespace Erdos1172Shioya.PartialProjection

variable {κ : Cardinal.{u}} {P Q R : Type u} [PartialOrder P] [PartialOrder Q] [PartialOrder R]
variable (π : PartialProjection κ P Q)

def inverseLower (A : LowerSet Q) : LowerSet P :=
  ⟨{p | ∀ x : π.dom, x.val ≤ p → π.proj x ∈ A},
    fun _ _ h hp x hx => hp x (hx.trans h)⟩

theorem dom_mem_inverse (A : LowerSet Q) (x : π.dom) :
    x.val ∈ inverseLower π A ↔ π.proj x ∈ A :=
  ⟨fun h => h x le_rfl, fun h _ hy => A.lower (π.proj.monotone hy) h⟩

theorem inverseLower_compl (A : LowerSet Q) : inverseLower π Aᶜ = (inverseLower π A)ᶜ := by
  apply SetLike.ext
  intro p
  rw [mem_pseudocompl_iff]
  constructor
  · intro hp r hr hm
    obtain ⟨x, hx⟩ := π.dense r
    exact (mem_pseudocompl_iff A _).mp (hp x (hx.trans hr)) _ le_rfl (hm x hx)
  · intro hp x hx
    apply (mem_pseudocompl_iff A _).mpr
    intro q hq ha
    obtain ⟨y, hy, hyq⟩ := π.lifts x q hq
    exact hp y.val ((show y.val ≤ x.val from hy).trans hx) ((dom_mem_inverse π A y).mpr (A.lower hyq ha))

def inverseRegular (b : Completion Q) : Completion P :=
  ⟨inverseLower π b.val, by
    change (inverseLower π b.val)ᶜᶜ = inverseLower π b.val
    rw [← inverseLower_compl, ← inverseLower_compl, b.prop.eq]⟩

theorem inverseRegular_compl (b : Completion Q) : inverseRegular π bᶜ = (inverseRegular π b)ᶜ :=
  Heyting.Regular.coe_injective (inverseLower_compl π b.val)

theorem inverse_sInf (S : Set (Completion Q)) :
    inverseRegular π (sInf S) = sInf (inverseRegular π '' S) := by
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro p
  rw [mem_sInf_completion]
  change (∀ x : π.dom, x.val ≤ p → π.proj x ∈ (sInf S).val) ↔ _
  simp only [mem_sInf_completion, Set.forall_mem_image]
  exact ⟨fun h _ hb x hx => h x hx _ hb, fun h x hx _ hb => h hb x hx⟩

def booleanHom : CompleteLatticeHom (Completion Q) (Completion P) where
  toFun := inverseRegular π
  map_sInf' := inverse_sInf π
  map_sSup' S := by
    apply compl_injective
    rw [← inverseRegular_compl, compl_sSup', inverse_sInf, compl_sSup', Set.image_image, Set.image_image]
    simp only [inverseRegular_compl]

theorem dom_condition (x : π.dom) (b : Completion Q) :
    condition x.val ≤ booleanHom π b ↔ condition (π.proj x) ≤ b := by
  simp only [condition_le_iff]
  exact dom_mem_inverse π b.val x

theorem booleanHom_injective : Function.Injective (booleanHom π) := by
  intro b c h
  have mono' (b c : Completion Q) (h : booleanHom π b ≤ booleanHom π c) : b ≤ c := by
    apply le_of_dense_conditions_le (Set.range π.proj) (fun q => by
      obtain ⟨x, hx⟩ := π.reaches q
      exact ⟨π.proj x, Set.mem_range_self x, hx⟩)
    rintro ⟨_, x, rfl⟩ hb
    exact (dom_condition π x c).mp (((dom_condition π x b).mpr hb).trans h)
  exact le_antisymm (mono' b c h.le) (mono' c b h.ge)

theorem booleanHom_id : booleanHom (identity (P := P) (κ := κ)) = CompleteLatticeHom.id _ := by
  ext b
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro p
  exact dom_mem_inverse (identity (κ := κ) (P := P)) b.val ⟨p, Set.mem_univ p⟩

theorem booleanHom_comp (σ : PartialProjection κ Q R) (hκ : Cardinal.aleph0 < κ) (hP : ShortInfima κ P) :
    booleanHom (comp π σ hκ hP) = (booleanHom π).comp (booleanHom σ) := by
  ext b
  let τ := comp π σ hκ hP
  have hmem (d : τ.dom) : condition d.val ≤ booleanHom τ b ↔
      condition d.val ≤ booleanHom π (booleanHom σ b) :=
    (dom_condition τ d b).trans (((dom_condition π (source π σ d) (booleanHom σ b)).trans
      (dom_condition σ (middle π σ d) b)).symm)
  have hd (p : P) : ∃ q ∈ τ.dom, q ≤ p := by
    obtain ⟨q, hq⟩ := τ.dense p
    exact ⟨q.val, q.property, hq⟩
  exact le_antisymm (le_of_dense_conditions_le τ.dom hd (fun d => (hmem d).mp))
    (le_of_dense_conditions_le τ.dom hd (fun d => (hmem d).mpr))

end Erdos1172Shioya.PartialProjection
