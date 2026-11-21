/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyInitialBoundedNames
public import Erdos1172.Part4BooleanUltrapowerConstants

@[expose] public section

/-! # Amalgamating coherent Boolean maps at an inaccessible collapse limit -/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion
open scoped Erdos1172LevyCollapse
universe u
namespace Erdos1172LevyCollapse.Matching

abbrev Algebra (μ : Cardinal.{u}) := Completion (BelowCondition μ)
variable {θ : Cardinal.{u}} (hθ : θ.IsInaccessible) {D : Type u} [CompleteBooleanAlgebra D]
  (f : ∀ μ : Cardinal.{u}, μ < θ → CompleteLatticeHom (Algebra μ) D)

/-- The stage maps give the same value to any Boolean condition read in two stages. -/
def AgreeOnOverlap : Prop :=
  ∀ μ ν (hm : μ < θ) (hn : ν < θ) (x : Algebra μ) (y : Algebra ν),
    initialCollapseHom hm.le x = initialCollapseHom hn.le y → f μ hm x = f ν hn y

include hθ
theorem exists_glued_value (agrees : AgreeOnOverlap f) (b : Algebra θ) :
    ∃ d : D, ∀ μ (hm : μ < θ) (x : Algebra μ), initialCollapseHom hm.le x = b → f μ hm x = d := by
  obtain ⟨ν,hn,_,v,hv⟩ := exists_initial_reading hθ (J := ULift.{u} Unit)
    (Cardinal.mk_lt_aleph0.trans hθ.aleph0_lt) (fun _ => b) hθ.aleph0_lt
  exact ⟨f ν hn (v ⟨()⟩),fun μ hm x hx => agrees μ ν hm hn x _ (hx.trans (hv ⟨()⟩).symm)⟩

def glued (agrees : AgreeOnOverlap f) (b : Algebra θ) : D :=
  Classical.choose (exists_glued_value hθ f agrees b)

variable (agrees : AgreeOnOverlap f)
include agrees
private theorem glued_stage (μ : Cardinal.{u}) (hm : μ < θ) (x : Algebra μ) :
    glued hθ f agrees (initialCollapseHom hm.le x) = f μ hm x :=
  ((exists_glued_value hθ f agrees _).choose_spec μ hm x rfl).symm

private theorem glued_monotone : Monotone (glued hθ f agrees) := by
  intro b c hbc
  let pair (i : ULift.{u} Bool) := if i.down then b else c
  obtain ⟨μ,hm,_,v,hv⟩ := exists_initial_reading hθ (Cardinal.mk_lt_aleph0.trans hθ.aleph0_lt) pair hθ.aleph0_lt
  have hb : initialCollapseHom hm.le (v ⟨true⟩) = b := hv _
  have hc : initialCollapseHom hm.le (v ⟨false⟩) = c := hv _
  have le : v ⟨true⟩ ≤ v ⟨false⟩ := by
    apply inf_eq_left.mp
    apply initialCollapseHom_injective hm.le
    change initialCollapseHom hm.le (v ⟨true⟩) ⊓ initialCollapseHom hm.le (v ⟨false⟩) =
      initialCollapseHom hm.le (v ⟨true⟩)
    rw [hb,hc]
    exact inf_eq_left.mpr hbc
  rw [← hb,← hc,glued_stage hθ f agrees μ hm,glued_stage hθ f agrees μ hm]
  exact OrderHomClass.mono (f μ hm) le

private theorem glued_iSup {J : Type u} (b : J → Algebra θ) :
    glued hθ f agrees (⨆ j, b j) = ⨆ j, glued hθ f agrees (b j) := by
  obtain ⟨S,hS,joins⟩ := Erdos1172BooleanUltrapower.exists_small_subfamily θ
    (fun a hp hd => below_completion_disjoint_family_cardinal_lt θ hθ.isRegular hθ.aleph0_lt a hp hd) b
  obtain ⟨μ,hm,_,v,hv⟩ := exists_initial_reading hθ hS (fun j : S => b j.val) hθ.aleph0_lt
  apply le_antisymm _ (iSup_le fun j => glued_monotone hθ f agrees (le_iSup b j))
  have rep : initialCollapseHom hm.le (⨆ j, v j) = ⨆ j, b j := by
    rw [map_iSup]
    exact (iSup_congr hv).trans joins
  rw [← rep,glued_stage hθ f agrees μ hm,map_iSup]
  apply iSup_le
  intro j
  rw [← glued_stage hθ f agrees μ hm, hv j]
  exact le_iSup (fun i => glued hθ f agrees (b i)) j.val

private theorem glued_compl (b : Algebra θ) : glued hθ f agrees bᶜ = (glued hθ f agrees b)ᶜ := by
  obtain ⟨μ,hm,_,v,hv⟩ := exists_initial_reading hθ (J := ULift.{u} Unit)
    (Cardinal.mk_lt_aleph0.trans hθ.aleph0_lt) (fun _ => b) hθ.aleph0_lt
  rw [← hv ⟨()⟩,← map_compl',glued_stage hθ f agrees μ hm,glued_stage hθ f agrees μ hm,map_compl']

/-- Compatible complete maps of bounded Lévy collapses extend uniquely to a
complete map of the full collapse. The range algebra has no size restriction. -/
theorem existsUnique_limit_hom :
    ∃! g : CompleteLatticeHom (Algebra θ) D,
      ∀ μ (hm : μ < θ) (x : Algebra μ), g (initialCollapseHom hm.le x) = f μ hm x := by
  let k := glued hθ f agrees
  have sup (S : Set (Algebra θ)) : k (sSup S) = sSup (k '' S) := by
    rw [sSup_image',sSup_eq_iSup']
    exact glued_iSup hθ f agrees _
  have inf (S : Set (Algebra θ)) : k (sInf S) = sInf (k '' S) := by
    apply compl_injective
    change (glued hθ f agrees (sInf S))ᶜ = _
    rw [← glued_compl,compl_sInf']
    change k (sSup (compl '' S)) = _
    rw [sup,compl_sInf',Set.image_image,Set.image_image]
    exact congrArg sSup (Set.image_congr' fun x => glued_compl hθ f agrees x)
  let g : CompleteLatticeHom (Algebra θ) D := { toFun := k, map_sSup' := sup, map_sInf' := inf }
  refine ⟨g,glued_stage hθ f agrees,?_⟩
  intro g' hg'
  ext b
  obtain ⟨μ,hm,_,v,hv⟩ := exists_initial_reading hθ (J := ULift.{u} Unit)
    (Cardinal.mk_lt_aleph0.trans hθ.aleph0_lt) (fun _ => b) hθ.aleph0_lt
  rw [← hv ⟨()⟩,hg']
  exact (glued_stage hθ f agrees μ hm _).symm

/-- For embeddings the limit is also an embedding. Every short family of
coefficients in its range is realized together in one bounded stage. -/
theorem exists_limit_embedding (injective : ∀ μ hm, Function.Injective (f μ hm)) :
    ∃ g : CompleteLatticeHom (Algebra θ) D, Function.Injective g ∧
      (∀ μ (hm : μ < θ) (x : Algebra μ), g (initialCollapseHom hm.le x) = f μ hm x) ∧
      ∀ {J : Type u}, Cardinal.mk J < θ → ∀ (b : J → Algebra θ) {start : Cardinal.{u}}, start < θ →
        ∃ (μ : Cardinal.{u}) (hm : μ < θ), start < μ ∧ ∃ x : J → Algebra μ, ∀ j, g (b j) = f μ hm (x j) := by
  obtain ⟨g,hg,_⟩ := existsUnique_limit_hom hθ f agrees
  refine ⟨g,?_,hg,?_⟩
  · intro b c he
    let pair (i : ULift.{u} Bool) := if i.down then b else c
    obtain ⟨μ,hm,_,v,hv⟩ := exists_initial_reading hθ (Cardinal.mk_lt_aleph0.trans hθ.aleph0_lt) pair hθ.aleph0_lt
    have hb : initialCollapseHom hm.le (v ⟨true⟩) = b := hv _
    have hc : initialCollapseHom hm.le (v ⟨false⟩) = c := hv _
    have eq : v ⟨true⟩ = v ⟨false⟩ := injective μ hm
      ((hg μ hm _).symm.trans ((congrArg g hb).trans (he.trans ((congrArg g hc).symm.trans (hg μ hm _)))))
    exact hb.symm.trans ((congrArg (initialCollapseHom hm.le) eq).trans hc)
  · intro J small b start hs
    obtain ⟨μ,hm,high,v,hv⟩ := exists_initial_reading hθ small b hs
    exact ⟨μ,hm,high,v,fun j => (congrArg g (hv j)).symm.trans (hg μ hm _)⟩

end Erdos1172LevyCollapse.Matching
