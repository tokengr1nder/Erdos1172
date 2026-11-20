/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingStage
public import Erdos1172.Part4LevyMatchingRelativeTree
public import Erdos1172.Part4InternalHartogsUniqueness

@[expose] public section

/-! # Matching two collapsing stages over their common old generic -/

set_option autoImplicit false
noncomputable section
universe u
open Cardinal Erdos1172PositiveBoolean Erdos1172PosetCompletion Erdos1172Collapse bSet Lattice
open scoped Flypitch
namespace Erdos1172LevyCollapse.Matching

variable {A B C : Type u} [CompleteBooleanAlgebra A] [NontrivialCompleteBooleanAlgebra B]

private theorem exists_enumeration (μ : Cardinal.{u}) (hμ : ℵ₀ < μ)
    (hb : (⊤ : B) ≤ injects_into (check (PSet.ordinalMk μ.ord)) omega) :
    ∃ f : bSet B, (⊤ : B) ≤ is_function omega (check (PSet.ordinalMk μ.ord)) f ⊓
      is_surj omega (check (PSet.ordinalMk μ.ord)) f := by
  let Z := (check (PSet.ordinalMk μ.ord) : bSet B)
  have hn : (⊤ : B) ≤ exists_mem Z := le_iSup_of_le (check (PSet.ordinalMk 0))
    (check_mem (PSet.mk_mem_mk_of_lt (Cardinal.ord_pos.mpr (Cardinal.aleph0_pos.trans hμ))))
  have h := surjects_onto_of_injects_into' hb hn
  let pred (f : bSet B) := is_function omega Z f ⊓ is_surj omega Z f
  have union : (⊤ : B) ≤ ⨆ f, pred f := by
    apply h.trans
    apply iSup_le
    intro f
    let Δ := is_func' omega Z f ⊓ is_surj omega Z f
    have weak : Δ ≤ is_func' omega Z f := inf_le_left
    exact le_iSup_of_le _ (le_inf (function_of_func'_is_function weak) (function_of_func'_surj_of_surj weak inf_le_right))
  have ext : B_ext pred := B_ext_inf B_ext_is_function_right
    (B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const)
      (h₂ := B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_mem_right))))
  obtain ⟨f,hf⟩ := maximum_principle pred ext
  exact ⟨f,union.trans_eq hf⟩

/-- The ordinary forced countability statement at a regular stage suffices
to identify its completion over the entire old algebra. -/
theorem exists_relative_stage_iso {K : Type u} (e : CompleteLatticeHom A B) (he : Function.Injective e)
    (μ : Cardinal.{u}) (hμ : ℵ₀ < μ) (reg : μ.IsRegular) (g : K → Positive A) (small : #K < μ)
    (gDense : ∀ a, ∃ k, g k ≤ a) (d : μ.ord.ToType → Positive B) (dDense : ∀ b, ∃ i, d i ≤ b)
    (hb : (⊤ : B) ≤ injects_into (check (PSet.ordinalMk μ.ord)) omega) :
    ∃ φ : B ≃o Completion (Positive A × Condition μ.ord.ToType), ∀ a, φ (e a) = oldFactor μ.ord.ToType a := by
  obtain ⟨f,hf⟩ := exists_enumeration μ hμ hb
  let Z : PSet.{u} := .mk μ.ord.ToType (fun i => PSet.ordinalMk i.toOrd.val)
  have hz : PSet.ordinalMk μ.ord = Z := PSet.ordinalMk_eq_def _
  rw [hz] at hf
  let M : CollapseMatrix μ.ord.ToType B := matrixOfSurjection Z
    (fun i j h eq => h (Ordinal.ToType.mk.symm.injective (Subtype.ext (PSet.eq_of_mk_equiv eq)))) f
    (hf.trans inf_le_left) (hf.trans inf_le_right)
  exact exists_relative_collapse_iso e he M (by simpa only [Cardinal.mk_ord_toType] using hμ)
    (by simpa only [Cardinal.mk_ord_toType] using reg) g (by simpa only [Cardinal.mk_ord_toType] using small)
    gDense d dDense

variable [NontrivialCompleteBooleanAlgebra C]

/-- Arbitrary dependent collapsing extensions of the same old Boolean
algebra can be matched without changing the old generic. -/
theorem exists_stage_amalgamation {K : Type u} (e : CompleteLatticeHom A B) (he : Function.Injective e)
    (v : CompleteLatticeHom A C) (hv : Function.Injective v) (μ : Cardinal.{u}) (hμ : ℵ₀ < μ) (reg : μ.IsRegular)
    (g : K → Positive A) (small : #K < μ) (gDense : ∀ a, ∃ k, g k ≤ a)
    (d : μ.ord.ToType → Positive B) (dDense : ∀ b, ∃ i, d i ≤ b)
    (t : μ.ord.ToType → Positive C) (tDense : ∀ c, ∃ i, t i ≤ c)
    (hb : (⊤ : B) ≤ injects_into (check (PSet.ordinalMk μ.ord)) omega)
    (hc : (⊤ : C) ≤ injects_into (check (PSet.ordinalMk μ.ord)) omega) :
    ∃ φ : B ≃o C, ∀ a, φ (e a) = v a := by
  obtain ⟨b,bi⟩ := exists_relative_stage_iso e he μ hμ reg g small gDense d dDense hb
  obtain ⟨c,ci⟩ := exists_relative_stage_iso v hv μ hμ reg g small gDense t tDense hc
  exact ⟨b.trans c.symm,fun a => c.symm_apply_eq.mpr ((bi a).trans (ci a).symm)⟩

end Erdos1172LevyCollapse.Matching
