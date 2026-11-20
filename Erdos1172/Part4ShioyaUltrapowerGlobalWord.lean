/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaUltrapowerMasterRun
public import Erdos1172.Part4ShioyaUltrapowerBitSchedule

@[expose] public section

/-! # One recovered master run deciding the entire elementary-image word -/

set_option autoImplicit false
noncomputable section
open Filter Erdos1172GroundUltrapower Erdos1172PosetCompletion
universe u
namespace Erdos1172Shioya.UltrapowerStage
variable {I : Type u} (U : Ultrafilter I) {κ θ : Cardinal.{u}} (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [Fact (Cardinal.aleph0 < κ)]
variable (hθ : θ.IsInaccessible) (fine : FineOn U a) (normal : NormalOn U a) (ht : FiberOrderType U κ θ a)
local notation "L" => liftCondition U a hθ fine normal ht
local notation "jᵇ" => boundedGroundEmbedding U θ a

/-- One θ-long descending sequence extends all realized stage filters.
Its signed word stabilizes at every position below the actual j(θ).
The codes of all its terms and strict comparisons belong to j(W) and its order. -/
theorem exists_recovered_global_word (hκθ : κ < θ) (D : Uniformization.Diagram κ θ θ.ord.ToType)
    (hl : D.localLifts) (F : Order.PFilter (Algebra κ θ)) (proper : ⊥ ∉ F)
    (meets : ∀ S, RecoveredMaster.edgeTests D S → ∃ b ∈ S, b ∈ F)
    (coding : ∀ j, (D.stage j).CodesDense) (req : ∀ p ∈ D.requirements, condition p ∈ F)
    (count : ∀ j, (RecoveredMaster.realized D F j).Countable)
    (cofinal : ∀ (j : θ.ord.ToType) (b : Ordinal.{u}), b < θ.ord →
      ∃ k : θ.ord.ToType, j < k ∧ b ≤ (D.stage k).length.toOrd.val) :
    ∃ (q : ∀ j, Point U a (D.poset j))
      (word : {α : (Order.succ θ).ord.ToType // α.toOrd.val < ordinalImage U a θ.ord} → Bool),
      (∀ j x, x ∈ RecoveredMaster.realized D F j → q j ≤ diagonal U a x) ∧
      (∀ j, repointedCode U a hθ fine normal ht (D.stage j) (q j) ∈
        (jᵇ (ZFSet.range (conditionCode (κ := κ) (θ := θ)))).val) ∧
      (∀ i j : θ.ord.ToType, i < j →
        ((L (D.stage j)).withPoint ((presentationIso U a hθ (D.stage j)).symm (q j))).Refines
          ((L (D.stage i)).withPoint ((presentationIso U a hθ (D.stage i)).symm (q i))) ∧
        ZFSet.pair (repointedCode U a hθ fine normal ht (D.stage j) (q j))
          (repointedCode U a hθ fine normal ht (D.stage i) (q i)) ∈ (jᵇ (forcingOrder κ θ)).val) ∧
      ∀ α, ∃ j, ∀ k ≥ j, ((L (D.stage k)).withPoint
        ((presentationIso U a hθ (D.stage k)).symm (q k))).Decides α.val (word α) := by
  classical
  let : Fact (Cardinal.aleph0 < θ) := ⟨hθ.aleph0_lt⟩
  have small (j : θ.ord.ToType) : Cardinal.mk (Set.Iic j) < θ := by
    simpa using Cardinal.mk_Iic_lt j (by simp) (by simpa using hθ.isRegular.aleph0_le)
  let K := wordTask U a hθ fine normal ht D
  obtain ⟨q,hit,hm,member,chain⟩ := exists_recovered_task_run U a fine normal ht D hθ hκθ small hl F proper meets
    coding req count K (wordTask_lower U a hθ fine normal ht D) (wordTask_dense U a hθ fine normal ht D)
  let A := {α : (Order.succ θ).ord.ToType // α.toOrd.val < ordinalImage U a θ.ord}
  let Q (j : θ.ord.ToType) := (L (D.stage j)).withPoint ((presentationIso U a hθ (D.stage j)).symm (q j))
  have decided (α : A) : ∃ j, ∃ b : Bool, (Q j).Decides α.val b := by
    obtain ⟨j,hj⟩ := wordTask_covers U a hθ fine normal ht D cofinal α.val α.property
    exact ⟨j,hj _ (hit j)⟩
  choose start bit first using decided
  refine ⟨q,bit,hm,member,chain,fun α => ⟨start α,?_⟩⟩
  intro k hk
  rcases hk.lt_or_eq with h | rfl
  · exact Condition.decides_mono (chain _ _ h).1 (first α)
  · exact first α

end Erdos1172Shioya.UltrapowerStage
