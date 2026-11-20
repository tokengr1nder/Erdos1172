/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaRecoveredMasterThread

@[expose] public section

/-! # Ground word decisions in the realized stage filters -/

set_option autoImplicit false
noncomputable section
universe u
open Erdos1172PosetCompletion
namespace Erdos1172Shioya.RecoveredMaster

variable {κ θ : Cardinal.{u}} [Fact (Cardinal.aleph0 < κ)] {J : Type u} [Preorder J]
variable (D : Uniformization.Diagram κ θ J)

def decidingPoints (q : Condition κ θ) (α : θ.ord.ToType) : Set q.Poset :=
  {x | ∃ n : Bool, (q.withPoint x).Decides α n}

def decisionCone (α : θ.ord.ToType) (c : Σ j, decidingPoints (D.stage j) α) :
    Algebra κ θ := condition ((D.stage c.1).withPoint c.2.val)

/-- One ground test for a coordinate, allowing a decision at any stage of the diagram. -/
def wordTest (α : θ.ord.ToType) : Set (Algebra κ θ) := decisionSet (decisionCone D α)

theorem wordTest_dense (α : θ.ord.ToType) (b : Algebra κ θ) (hb : b ≠ ⊥) :
    ∃ c ∈ wordTest D α, c ≤ b := decisionSet_dense _ b hb

private theorem stage_le_decision_cones (j : J) (α : θ.ord.ToType)
    (hα : α.toOrd.val < (D.stage j).length.toOrd.val) :
    condition (D.stage j) ≤ ⨆ c, decisionCone D α c := by
  let q := D.stage j
  let i := Ordinal.ToType.mk (⟨α.toOrd.val,hα⟩ : Set.Iio q.length.toOrd.val)
  have hi : i.toOrd.val = α.toOrd.val := congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
  apply (q.withPoint_predense (decidingPoints q α) ?_).trans
  · exact iSup_le fun x => le_iSup (decisionCone D α) ⟨j,x⟩
  intro p _
  by_cases h : condition p ⊓ q.bits i = ⊥
  · exact ⟨p,⟨false,i,hi,le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr h)⟩,le_rfl⟩
  · obtain ⟨t,ht⟩ := exists_condition_le h
    obtain ⟨x,hxt,hxp⟩ := (mem_condition_iff p t).mp (condition_le_iff.mp (ht.trans inf_le_left)) t le_rfl
    exact ⟨x,⟨true,i,hi,(condition_mono hxt).trans (ht.trans inf_le_right)⟩,hxp⟩

/-- The realized point's decision has the same sign as the ground generic word. -/
theorem exists_realized_decision (F : Order.PFilter (Algebra κ θ)) (proper : ⊥ ∉ F)
    (meets : ∀ α, ∃ b ∈ wordTest D α, b ∈ F) (req : ∀ p ∈ D.requirements, condition p ∈ F)
    (covers : ∀ α : θ.ord.ToType, ∃ j, α.toOrd.val < (D.stage j).length.toOrd.val) (α : θ.ord.ToType) :
    ∃ (j : J) (x : D.poset j) (n : Bool), x ∈ realized D F j ∧
      ((D.stage j).withPoint x).Decides α n ∧ decisionValue κ θ α n ∈ F := by
  obtain ⟨j,hj⟩ := covers α
  have hq : condition (D.stage j) ∈ F := req _ (Or.inl ⟨j,rfl⟩)
  obtain ⟨⟨k,x⟩,hx⟩ := readsJoin_of_decisionSet F proper (decisionCone D α) (meets α)
    (Order.PFilter.mem_of_le (stage_le_decision_cones D j α hj) hq)
  obtain ⟨n,hn⟩ := x.property
  exact ⟨k,x.val,n,hx,hn,Order.PFilter.mem_of_le (condition_le_decisionValue κ θ hn) hx⟩

omit [Fact (Cardinal.aleph0 < κ)] in
theorem word_covers_of_cofinal [Nonempty J] (hθ : Cardinal.aleph0 ≤ θ)
    (cofinal : ∀ (j : J) (b : Ordinal.{u}), b < θ.ord → ∃ k : J, j < k ∧ b ≤ (D.stage k).length.toOrd.val)
    (α : θ.ord.ToType) : ∃ j, α.toOrd.val < (D.stage j).length.toOrd.val := by
  obtain ⟨j,_,hj⟩ := cofinal (Classical.arbitrary J) (Order.succ α.toOrd.val)
    ((Cardinal.isSuccLimit_ord hθ).succ_lt α.toOrd.property)
  exact ⟨j,(Order.lt_succ _).trans_le hj⟩

end Erdos1172Shioya.RecoveredMaster
