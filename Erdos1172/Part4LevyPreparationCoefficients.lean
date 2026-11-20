/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyPreparationBooleanLift

@[expose] public section

/-! # Every Boolean coefficient of the upper collapse has a representative -/

set_option autoImplicit false
noncomputable section
open Filter Erdos1172GroundUltrapower Erdos1172BooleanUltrapower Erdos1172PosetCompletion Erdos1172LevyCohen
universe u
namespace Erdos1172LevyCollapse.Preparation
variable {I J D : Type u} {κ θ : Cardinal.{u}} (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
variable [Nonempty θ.ord.ToType] (hf : FineOn U a) (hn : NormalOn U a)

include hf hn in
/-- The varying subfamilies on the fine fibers compute the entire join.
Normality makes every large selection equal to a single ground index. -/
theorem value_fine_iSup [CompleteBooleanAlgebra D] (idx : J ↪ θ.ord.ToType) (b : J → I → D) :
    value U (fun i => ⨆ j : {j : J // idx j ∈ a i}, b j.val i) = ⨆ j, value U (b j) := by
  classical
  apply le_antisymm
  · rw [value_iSup]
    apply iSup_le
    intro s
    let f (i : I) := if h : i ∈ s.carrier then idx (s.pick ⟨i,h⟩).val else Classical.choice inferInstance
    have on (i : I) (hi : i ∈ s.carrier) : f i = idx (s.pick ⟨i,hi⟩).val := dif_pos hi
    obtain ⟨x,hx⟩ := hn f ((show ∀ᶠ i in U, i ∈ s.carrier from s.large).mono fun i hi => by
      rw [on i hi]; exact (s.pick ⟨i,hi⟩).property)
    obtain ⟨i₀,hi₀,he₀⟩ := ((show ∀ᶠ i in U, i ∈ s.carrier from s.large).and hx).exists
    let k := (s.pick ⟨i₀,hi₀⟩).val
    have fix : idx k = x := (on i₀ hi₀).symm.trans he₀
    apply le_iSup_of_le k
    apply (value_le_value_iff U).mpr
    filter_upwards [s.large,hx] with i hi he
    have eq := idx.injective ((on i hi).symm.trans (he.trans fix.symm))
    simp only [selected,dif_pos hi,eq,le_refl]
  · apply iSup_le
    intro j
    apply (value_le_value_iff U).mpr
    exact (hf (idx j)).mono fun i hi => le_iSup (fun k : {k : J // idx k ∈ a i} => b k.val i) ⟨j,hi⟩

variable [CountableInterFilter (U : Filter I)]
variable (hk : κ ≤ θ) (ht : FiberOrderType U κ θ a)
local notation "A" => FirstAlgebra κ
local notation "B" => FirstAlgebra θ
local notation "φ" => collapseCompletionIso U a hk hf hn ht
local notation "E" => collapseGermIso U a hk hf hn ht

/-- The complete Boolean ultrapower has no additional coefficient at the
upper collapse. This includes joins of antichains of arbitrary ground size. -/
theorem exists_prepared_coefficient (hu : Cardinal.aleph0 < θ) (c : B) :
    ∃ f : I → A, φ (value U f) = c := by
  classical
  let Q := {q : BelowCondition θ // condition q ≤ c}
  have small : Cardinal.mk Q ≤ Cardinal.mk θ.ord.ToType := by
    rw [Cardinal.mk_ord_toType]
    exact (Cardinal.mk_subtype_le _).trans (belowCondition_cardinal_le θ hu)
  let idx := Classical.choice small
  choose f he using fun q : Q => (show ∃ f : I → BelowCondition κ, E (Germ.ofFun f) = q.val from by
    obtain ⟨g,hg⟩ := (E).surjective q.val
    induction g using Germ.inductionOn with
    | _ f => exact ⟨f,hg⟩)
  let b (q : Q) (i : I) := condition (f q i)
  refine ⟨fun i => ⨆ q : {q : Q // idx q ∈ a i}, b q.val i,?_⟩
  rw [value_fine_iSup U a hf hn idx b,_root_.map_iSup]
  have val (q : Q) : φ (value U (b q)) = condition q.val :=
    (collapseCompletionIso_value U a hk hf hn ht (f q)).trans (congrArg condition (he q))
  simp_rw [val]
  exact le_antisymm (iSup_le fun q : Q => q.property) (fun x hx =>
    condition_le_iff.mp (le_iSup (fun q : Q => condition q.val) ⟨x,condition_le_iff.mpr hx⟩))

end Erdos1172LevyCollapse.Preparation
