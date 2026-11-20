/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingReasonableStages

@[expose] public section

/-! # Bounded readings from the chain condition and density of the source union -/

set_option autoImplicit false
noncomputable section
universe u
open Cardinal Erdos1172BooleanUltrapower bSet bSet.ErdosNameTransport Erdos1172CohenIteration
open scoped Flypitch
namespace Erdos1172LevyCollapse.Matching

variable {θ : Cardinal.{u}} {R : Type u} [NontrivialCompleteBooleanAlgebra R]
  {B : θ.ord.ToType → Type u} [∀ i, NontrivialCompleteBooleanAlgebra (B i)]
  (b : ∀ {i j : θ.ord.ToType}, i ≤ j → CompleteLatticeHom (B i) (B j))
  (g : ∀ i, CompleteLatticeHom (B i) R)
  (gg : ∀ {i j} (h : i ≤ j) x, g j (b h x) = g i x)

/-- The union of the stage embeddings is dense in the positive source algebra. -/
def DenseStageUnion : Prop := ∀ z : R, z ≠ ⊥ → ∃ i x, g i x ≠ ⊥ ∧ g i x ≤ z

private theorem exact_cover (hd : DenseStageUnion g) (z : R) :
    (⨆ s : {s : Σ i, B i // g s.1 s.2 ≤ z}, g s.val.1 s.val.2) = z := by
  let t := ⨆ s : {s : Σ i, B i // g s.1 s.2 ≤ z}, g s.val.1 s.val.2
  apply le_antisymm (iSup_le fun s => s.property)
  by_contra h
  have pos : z ⊓ tᶜ ≠ ⊥ := fun he => h ((le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr he)).trans_eq (compl_compl t))
  obtain ⟨i,x,hx,le⟩ := hd _ pos
  have lt : g i x ≤ t := le_iSup (fun s : {s : Σ i, B i // g s.1 s.2 ≤ z} => g s.val.1 s.val.2) ⟨⟨i,x⟩,le.trans inf_le_left⟩
  exact hx (bot_unique ((le_inf lt (le.trans inf_le_right)).trans inf_compl_eq_bot.le))

include gg in
/-- Every short array of ground Boolean coefficients is read in a single
bounded source stage, retaining every coefficient exactly. -/
theorem source_array_from_stage (hθ : θ.IsInaccessible) (cc : StrictCC R θ)
    (hd : DenseStageUnion g) {A : Type u} (ha : #A < θ) (v : A → R) :
    ∃ (i : θ.ord.ToType) (f : A → B i), ∀ a, g i (f a) = v a := by
  let Q (a : A) := {s : Σ i, B i // g s.1 s.2 ≤ v a}
  let value (a : A) (s : Q a) := g s.val.1 s.val.2
  choose T hT sums using fun a => exists_small_subfamily θ cc (value a)
  let I := Σ a : A, T a
  have hI : #I < θ := (Cardinal.mk_sigma _).trans_lt (Cardinal.sum_lt_of_isRegular hθ.isRegular ha hT)
  let rank (s : I) := s.2.val.val.1.toOrd.val
  let α := ⨆ s : I, rank s + 1
  have low : α < θ.ord := Ordinal.iSup_add_one_lt_of_lt_cof (by rw [hθ.isRegular.cof_ord]; exact hI)
    (fun s => s.2.val.val.1.toOrd.property)
  let i := Ordinal.ToType.mk (⟨α,low⟩ : Set.Iio θ.ord)
  have hi : i.toOrd.val = α := congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
  have before (a : A) (s : T a) : s.val.val.1 ≤ i := by
    apply (Ordinal.ToType.mk.symm.le_iff_le).mp
    change rank (⟨a,s⟩ : I) ≤ i.toOrd.val
    rw [hi]
    exact (Ordinal.lt_iSup_add_one rank ⟨a,s⟩).le
  refine ⟨i,fun a => ⨆ s : T a, b (before a s) s.val.val.2,fun a => ?_⟩
  rw [map_iSup]
  exact (iSup_congr (fun s : T a => gg (before a s) s.val.val.2)).trans ((sums a).trans (exact_cover g hd (v a)))

end Erdos1172LevyCollapse.Matching
