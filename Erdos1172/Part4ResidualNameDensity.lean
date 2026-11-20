/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4RelativeValuationPartition
public import Erdos1172.Part4BooleanIterationDensePresentation
public import Erdos1172.Part4ShioyaDenseCoverIso
public import Erdos1172.Part4PosetGenericFilter

@[expose] public section

/-! # Relative density of a residual forcing presented by names -/

set_option autoImplicit false
noncomputable section
open bSet Erdos1172PosetCompletion Erdos1172SeedQuotient Lattice
open scoped Flypitch
universe u
namespace Erdos1172BooleanNameIteration
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B] (Q : bSet B)

def sourceHom : CompleteLatticeHom B (Algebra Q) :=
  (firstStageHom Q).comp Erdos1172PositiveBoolean.completionHom

theorem condition_le_source (p : Condition Q) (b : B) :
    condition p ≤ sourceHom Q b ↔ p.value ≤ b := by
  rw [sourceHom,CompleteLatticeHom.comp_apply,condition_le_firstStageHom_iff,condition_le_iff]
  rfl

theorem sourceHom_injective {q : bSet B} (hq : (⊤ : B) ≤ q ∈ᴮ Q) : Function.Injective (sourceHom Q) := by
  have lifts : Erdos1172Shioya.ForcingCover.Lifts (projection Q) := by
    intro p a ha
    obtain ⟨r,hr,eq⟩ := projection_exactLifts Q p a ha
    exact ⟨r,hr,eq.le⟩
  exact (Erdos1172Shioya.ForcingCover.booleanHom_injective (projection Q) lifts
    (projection_dense_of_mem hq)).comp Erdos1172PositiveBoolean.completionHom_injective

/-- The Boolean cone of a mixed residual name, allowing a different canonical
label on each piece of the source forcing. -/
def nameCone (q : bSet B) : Algebra Q :=
  ⨆ p : {r : Condition Q // r.value ≤ q =ᴮ name r}, condition p.val

private theorem cone_meet_source_le (r p : Condition Q) (b : B)
    (base : r.value ⊓ b ≤ p.value) (extendsName : r.value ⊓ b ≤ name p ⊆ᴮ name r) :
    condition r ⊓ sourceHom Q b ≤ condition p := by
  intro t ht
  change t ∈ (condition r).val ∧ t ∈ (sourceHom Q b).val at ht
  have tb := (condition_le_source Q t b).mp (condition_le_iff.mpr ht.2)
  apply (mem_condition_iff p t).mpr
  intro v hv
  obtain ⟨z,hz,hr⟩ := (mem_condition_iff r t).mp ht.1 v hv
  have hb := le_inf hr.1 ((hz.trans hv).1.trans tb)
  exact ⟨z,hz,hb.trans base,subset_trans' (hb.trans extendsName) hr.2⟩

theorem nameCone_local {q : bSet B} (p : Condition Q) (h : p.value ≤ q =ᴮ name p) :
    nameCone Q q ⊓ sourceHom Q p.value = condition p := by
  apply le_antisymm
  · unfold nameCone
    apply (iSup_inf_eq _ _).le.trans
    apply iSup_le
    intro r
    apply cone_meet_source_le Q r.val p _ inf_le_right
    exact subset_of_eq (bv_trans (bv_symm (inf_le_right.trans h)) (inf_le_left.trans r.property))
  · exact le_inf (le_iSup (fun r : {r : Condition Q // r.value ≤ q =ᴮ name r} => condition r.val) ⟨p,h⟩)
      ((condition_le_source Q p _).mpr le_rfl)

local instance [Nonempty (Condition Q)] : NontrivialCompleteBooleanAlgebra (Algebra Q) where
  toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra
  bot_lt_top := bot_lt_top

/-- An internally dense sequence of named residual conditions supplies that
same number of Boolean values dense over the source, irrespective of its size. -/
theorem denseOver_nameCone [Nonempty (Condition Q)] {I : Type u} (q : I → bSet B)
    (cover : ∀ p : Condition Q, p.value ≤ ⨆ i, (q i ∈ᴮ Q) ⊓ (name p ⊆ᴮ q i)) :
    denseOver (sourceHom Q) (fun i => nameCone Q (q i)) := by
  intro c hc
  obtain ⟨p,hp⟩ := exists_condition_le hc
  have nz : ∃ i, p.value ⊓ ((q i ∈ᴮ Q) ⊓ (name p ⊆ᴮ q i)) ≠ ⊥ := by
    by_contra! bad
    exact p.nonzero ((inf_eq_left.mpr (cover p)).symm.trans
      ((inf_iSup_eq _ _).trans (iSup_eq_bot.mpr bad)))
  obtain ⟨i,hi⟩ := nz
  obtain ⟨r,hr,_,rep⟩ := exists_extension_refinement p hi inf_le_left
    (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)
  refine ⟨i,r.value,?_,?_⟩
  · exact fun hz => condition_ne_bot r ((nameCone_local Q r rep).symm.trans hz)
  · exact (nameCone_local Q r rep).le.trans ((condition_mono hr).trans hp)

theorem canonicalLabels_denseOver [Nonempty (Condition Q)] :
    denseOver (sourceHom Q) (fun i : Q.type => nameCone Q (Q.func i)) := by
  apply denseOver_nameCone
  intro p
  exact le_iSup_of_le p.index (le_inf (name_mem p) subset_self)

/-- A checked enumeration of the residual forcing gives relative density
bounded by the number of indices, even over an arbitrarily large base. -/
theorem exists_denseOver_of_surjection [Nonempty (Condition Q)] {T : PSet.{u}} {f : bSet B}
    (func : (⊤ : B) ≤ is_function (check T) Q f) (surj : (⊤ : B) ≤ is_surj (check T) Q f) :
    ∃ d : T.Type → Algebra Q, denseOver (sourceHom Q) d := by
  rcases T with ⟨I,a⟩
  let q (i : I) := function_eval func (check (a i)) (check_mem (PSet.func_mem (PSet.mk I a) i))
  refine ⟨fun i => nameCone Q (q i),denseOver_nameCone Q q ?_⟩
  intro p
  apply (checked_surjection_preimages surj p).trans
  apply iSup_mono
  intro i
  have member : (⊤ : B) ≤ q i ∈ᴮ Q := function_eval_mem_codomain
  have pairmem : (⊤ : B) ≤ pair (check (a i)) (q i) ∈ᴮ f := function_eval_pair_mem
  exact le_inf (le_top.trans member) (subset_of_eq (eq_of_is_func_of_eq
    (le_top.trans (func.trans (inf_le_left.trans inf_le_left))) bv_refl le_rfl (le_top.trans pairmem)))

theorem exists_mem_of_checked_function {T : PSet.{u}} (inhabited : Nonempty T.Type) {f : bSet B}
    (func : (⊤ : B) ≤ is_function (check T) Q f) : ∃ q : bSet B, (⊤ : B) ≤ q ∈ᴮ Q := by
  let i := Classical.choice inhabited
  have hi : (⊤ : B) ≤ check (T.Func i) ∈ᴮ check T := check_mem (PSet.func_mem T i)
  exact ⟨function_eval func _ hi,function_eval_mem_codomain⟩

end Erdos1172BooleanNameIteration
