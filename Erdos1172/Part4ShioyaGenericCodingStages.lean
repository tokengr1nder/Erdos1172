/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaSynchronizedStages
public import Erdos1172.Part4ShioyaGreatestStageLift
public import Erdos1172.Part4ShioyaRecoveredFilter
public import Erdos1172.Part4PosetGenericFilter

@[expose] public section

/-! # Coding stages and their recovered generics below a Shioya condition -/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
open bSet Erdos1172PosetCompletion Erdos1172PosetGeneric

universe u
namespace Erdos1172Shioya.LevyProduct

variable {κ θ : Cardinal.{u}} [Fact (Cardinal.aleph0 < κ)]
variable (hκ : κ.IsRegular) (hκθ : κ < θ) (hθ : θ.IsInaccessible)
local notation "T" => stageSystem hκ hκθ hθ

/-- A stage word presented at its greatest point. -/
def topPresentation (a : (T).Entry) : Condition κ θ :=
  (a.forget T).withPoint ((T).base a.stage).point

omit [Fact (Cardinal.aleph0 < κ)] in
theorem topPresentation_greatest (a : (T).Entry) (x : (topPresentation hκ hκθ hθ a).Poset) :
    x ≤ (topPresentation hκ hκθ hθ a).point :=
  stageBase_greatest hκ hκθ hθ a.stage x

/-- Arbitrarily late synchronized coding words occur below a given condition
when pointed at a member of their recovered generic. -/
theorem exists_pointed_coding_stage (p : Condition κ θ) (late : Index θ) :
    ∃ a : (T).Entry, late ≤ a.stage ∧ a.length = a.stage ∧ (topPresentation hκ hκθ hθ a).Codes ∧
      (topPresentation hκ hκθ hθ a).withPoint a.point ≤ p := by
  let _ : Nonempty (Index θ) := ⟨late⟩
  obtain ⟨b,hb⟩ := (T).forget_reaches (stageSystem_hasCollapseFactors hκ hκθ hθ) hκ p
  obtain ⟨a,hab,hl,hs,hc⟩ := exists_synchronized_coding hκ hκθ hθ b late
  exact ⟨a,hl,hs,hc,((T).forgetMap.monotone hab).trans hb⟩

variable [Nonempty (Condition κ θ)]

/-- Conditional on membership of a ground Shioya condition in the generic,
there is a late coding top in the generic with a recovered point witnessing
refinement of that very condition. -/
theorem generic_contains_coding_stage_below (p : Condition κ θ) (late : Index θ) :
    (check (genericLabel (positiveCondition p)) ∈ᴮ genericFilterName (Algebra κ θ)) ≤
      ⨆ a : {a : (T).Entry // late ≤ a.stage ∧ a.length = a.stage ∧
        (topPresentation hκ hκθ hθ a).Codes ∧ (topPresentation hκ hκθ hθ a).withPoint a.point ≤ p},
        (check (genericLabel (positiveCondition (topPresentation hκ hκθ hθ a.val))) ∈ᴮ
          genericFilterName (Algebra κ θ)) ⊓
        (StringName.label (γ := ((T).base a.val.stage).presentation.index.toOrd.val) a.val.point ∈ᴮ
          recoveredFilter (topPresentation hκ hκθ hθ a.val)) := by
  rw [genericFilterName_mem]
  apply cone_le_of_refinements
  intro r hr
  obtain ⟨a,hl,hs,hc,ha⟩ := exists_pointed_coding_stage hκ hκθ hθ r late
  refine ⟨(topPresentation hκ hκθ hθ a).withPoint a.point,ha,?_⟩
  apply le_iSup_of_le ⟨a,hl,hs,hc,ha.trans hr⟩
  apply le_inf
  · rw [genericFilterName_mem]
    exact condition_mono ((topPresentation hκ hκθ hθ a).withPoint_le
      (topPresentation_greatest hκ hκθ hθ a a.point))
  · exact (recoveredFilter_mem (topPresentation hκ hκθ hθ a) a.point).ge

end Erdos1172Shioya.LevyProduct
