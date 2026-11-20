/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyPreparationDiagonal
public import Erdos1172.Part4ShioyaDenseCoverIso
public import Erdos1172.Part4BooleanUltrapowerSeedDensity
public import Erdos1172.Part4BooleanUltrapowerSeedRange

@[expose] public section

/-! # Identifying the Boolean ultrapower of the preparatory collapse with the larger collapse -/

set_option autoImplicit false
noncomputable section
open Filter Erdos1172GroundUltrapower Erdos1172PosetCompletion Erdos1172PositiveBoolean
open Erdos1172Shioya.ForcingCover Erdos1172BooleanUltrapower Erdos1172LevyCohen
open scoped Erdos1172LevyCollapse
universe u
namespace Erdos1172LevyCollapse.Preparation
variable {I : Type u} (U : Ultrafilter I)

section Conditions
variable {P : Type u} [Preorder P]
local notation "G" => Germ (U : Filter I)
local notation "T" => Positive (G (Completion P))

theorem rep {X : Type u} (p : G X) : ∃ f : I → X, Germ.ofFun f = p :=
  Germ.inductionOn p fun f => ⟨f,rfl⟩

def germCone : G P →o T where
  toFun p := ⟨Germ.map condition p,by
    obtain ⟨f,rfl⟩ := rep U p
    intro eq
    obtain ⟨i,hi⟩ := (Germ.coe_eq.mp eq).exists
    exact condition_ne_bot (f i) hi⟩
  monotone' := by
    intro p q h
    obtain ⟨f,rfl⟩ := rep U p
    obtain ⟨g,rfl⟩ := rep U q
    exact (Germ.coe_le.mp h).mono fun _ hi => condition_mono hi

private theorem representative_pos {b : I → Completion P} (h : Germ.ofFun b ≠ (⊥ : G (Completion P))) :
    ∀ᶠ i in U, b i ≠ ⊥ := U.eventually_not.mpr (fun hz => h (Germ.coe_eq.mpr hz))

theorem germCone_lifts : Lifts (germCone U (P := P)) := by
  classical
  intro p q hq
  obtain ⟨f,rfl⟩ := rep U p
  obtain ⟨q,hpos⟩ := q
  obtain ⟨b,rfl⟩ := rep U q
  have hb : ∀ᶠ i in U, b i ≤ condition (f i) := hq
  let possible (i : I) := ∃ x : P, x ≤ f i ∧ condition x ≤ b i
  have ok : ∀ᶠ i in U, possible i := by
    filter_upwards [hb,representative_pos U hpos] with i hi hp
    obtain ⟨y,hy⟩ := exists_condition_le hp
    obtain ⟨x,hxy,hxp⟩ := (mem_condition_iff (f i) y).mp (condition_le_iff.mp (hy.trans hi)) y le_rfl
    exact ⟨x,hxp,(condition_mono hxy).trans hy⟩
  let z (i : I) := if h : possible i then h.choose else f i
  refine ⟨Germ.ofFun z,ok.mono (fun i hi => ?_),ok.mono (fun i hi => ?_)⟩
  · exact (show z i = hi.choose from dif_pos hi) ▸ hi.choose_spec.1
  · change condition (z i) ≤ b i
    rw [show z i = hi.choose from dif_pos hi]
    exact hi.choose_spec.2

theorem germCone_compatible (p q : G P) (h : germCone U p ≤ germCone U q) : ∃ z ≤ p, z ≤ q := by
  classical
  obtain ⟨f,rfl⟩ := rep U p
  obtain ⟨g,rfl⟩ := rep U q
  have he : ∀ᶠ i in U, condition (f i) ≤ condition (g i) := h
  let possible (i : I) := ∃ z : P, z ≤ f i ∧ z ≤ g i
  have ok : ∀ᶠ i in U, possible i := he.mono fun i hi =>
    (mem_condition_iff (g i) (f i)).mp (condition_le_iff.mp hi) _ le_rfl
  let z (i : I) := if h : possible i then h.choose else f i
  refine ⟨Germ.ofFun z,ok.mono (fun i hi => ?_),ok.mono (fun i hi => ?_)⟩
  · exact (show z i = hi.choose from dif_pos hi) ▸ hi.choose_spec.1
  · exact (show z i = hi.choose from dif_pos hi) ▸ hi.choose_spec.2

theorem germCone_dense [Nonempty P] (q : T) : ∃ p : G P, germCone U p ≤ q := by
  classical
  obtain ⟨q,hpos⟩ := q
  obtain ⟨b,rfl⟩ := rep U q
  let f (i : I) := if h : b i ≠ ⊥ then (exists_condition_le h).choose else Classical.choice inferInstance
  exact ⟨Germ.ofFun f,(representative_pos U hpos).mono fun i hi => by
    change condition (f i) ≤ b i; simp only [f,dif_pos hi]; exact (exists_condition_le hi).choose_spec⟩
end Conditions

variable {κ θ : Cardinal.{u}} (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType]
variable (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
local notation "E" => collapseGermIso U a hk hf hn ht
local notation "B" => FirstAlgebra κ
local notation "T" => Positive (Germ (U : Filter I) B)
local notation "P" => BelowCondition θ

def targetCone : P →o T := (germCone U).comp ⟨(E).symm,(E).symm.monotone⟩
local notation "π" => targetCone U a hk hf hn ht

theorem targetLifts : Lifts π := by
  intro p q h
  obtain ⟨r,hr,hrq⟩ := germCone_lifts U ((E).symm p) q h
  refine ⟨E r,(E).le_symm_apply.mp hr,?_⟩
  change germCone U ((E).symm (E r)) ≤ q
  rwa [(E).symm_apply_apply]

theorem targetCompatible (p q : P) (h : π p ≤ π q) : ∃ z ≤ p, z ≤ q := by
  obtain ⟨r,hp,hq⟩ := germCone_compatible U ((E).symm p) ((E).symm q) h
  exact ⟨E r,(E).le_symm_apply.mp hp,(E).le_symm_apply.mp hq⟩

theorem targetDense (q : T) : ∃ p : P, π p ≤ q := by
  obtain ⟨r,hr⟩ := germCone_dense U q
  refine ⟨E r,?_⟩
  change germCone U ((E).symm (E r)) ≤ q
  rwa [(E).symm_apply_apply]

def collapseCompletionIso : Erdos1172BooleanUltrapower.Algebra U B ≃o FirstAlgebra θ :=
  completionIso π (targetLifts U a hk hf hn ht) (targetCompatible U a hk hf hn ht)
    (targetDense U a hk hf hn ht)
local notation "φ" => collapseCompletionIso U a hk hf hn ht

theorem collapseCompletionIso_value (f : I → BelowCondition κ) :
    φ (value U (fun i => condition (f i))) = condition (E (Germ.ofFun f)) := by
  have ep : π (E (Germ.ofFun f)) = germCone U (Germ.ofFun f) := by
    change germCone U ((E).symm (E (Germ.ofFun f))) = _
    rw [(E).symm_apply_apply]
  have pos := germValue_positive U (germCone U (Germ.ofFun f))
  change φ (germValue U (germCone U (Germ.ofFun f)).val) = _
  rw [pos,← ep]
  exact booleanHom_condition π (targetLifts U a hk hf hn ht) (targetCompatible U a hk hf hn ht) _

variable [CardinalInterFilter (U : Filter I) κ]

theorem collapseCompletionIso_constant (hκ : κ.IsRegular) (hu : Cardinal.aleph0 < κ) (b : B) :
    φ (firstCollapseConstantHom U κ hκ hu b) = initialCollapseHom hk b := by
  let X := {p : BelowCondition κ // condition p ≤ b}
  have cover : b = ⨆ p : X, condition p.val := le_antisymm (fun x hx =>
    condition_le_iff.mp (le_iSup (fun p : X => condition p.val) ⟨x,condition_le_iff.mpr hx⟩))
    (iSup_le fun p => p.property)
  rw [cover,_root_.map_iSup,_root_.map_iSup,_root_.map_iSup]
  apply iSup_congr
  intro p
  rw [firstCollapseConstantHom_apply,collapseCompletionIso_value U a hk hf hn ht (fun _ => p.val),
    initialCollapseHom_condition]
  exact congrArg condition (collapseGermIso_const U a hk hf hn ht p.val)

end Erdos1172LevyCollapse.Preparation
