/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaPreparationCommutation
public import Erdos1172.Part4LevyAnonymousSmallAuxiliary

@[expose] public section

/-! # The prepared Shioya forcing and the collapse–Cohen auxiliary forcing -/

set_option autoImplicit false
noncomputable section
universe u
open bSet ErdosNameTransport Erdos1172PosetCompletion Erdos1172Shioya.ForcingCover
open scoped Flypitch
namespace Erdos1172BooleanNameIteration.Joint
variable {A B C : Type u} [NontrivialCompleteBooleanAlgebra A]
  [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]
variable (e : CompleteLatticeHom A B) (f : CompleteLatticeHom A C) (φ : B ≃o C)
  (over : ∀ a, φ (e a) = f a)

def push : (U : bSet A) → Condition (mapNames e U) → Condition (mapNames f U)
  | .mk _ _ w, p => ⟨φ p.value,(φ.map_bot ▸ (φ.injective.ne p.nonzero)),p.index,
      (φ.monotone p.valid).trans_eq (over (w p.index))⟩

theorem push_le_iff (U : bSet A) (p q : Condition (mapNames e U)) :
    push e f φ over U p ≤ push e f φ over U q ↔ p ≤ q := by
  cases U with
  | mk I X w =>
    change (φ p.value ≤ φ q.value ∧ φ p.value ≤ mapNames f (X q.index) ⊆ᴮ mapNames f (X p.index)) ↔
      (p.value ≤ q.value ∧ p.value ≤ mapNames e (X q.index) ⊆ᴮ mapNames e (X p.index))
    rw [← map_subset,← map_subset,← over,φ.le_iff_le,φ.le_iff_le]

def changeConditions (U : bSet A) : Condition (mapNames e U) ≃o Condition (mapNames f U) where
  toFun := push e f φ over U
  invFun := push f e φ.symm (fun a => φ.symm_apply_eq.mpr (over a).symm) U
  left_inv p := by cases U; cases p; simp only [push,OrderIso.symm_apply_apply]
  right_inv p := by cases U; cases p; simp only [push,OrderIso.apply_symm_apply]
  map_rel_iff' := push_le_iff e f φ over U _ _

def changeCompletion (U : bSet A) : Algebra (mapNames e U) ≃o Algebra (mapNames f U) :=
  let g := changeConditions e f φ over U
  let h : Condition (mapNames f U) →o Condition (mapNames e U) := ⟨g.symm,g.symm.monotone⟩
  completionIso h (fun p q le => ⟨g q,(g.le_symm_apply.mp le),by simp [h]⟩)
    (fun a _ le => ⟨a,le_rfl,g.symm.le_iff_le.mp le⟩) (fun t => ⟨g t,by simp [h]⟩)

include over in
private theorem lower_change (c : C) :
    Erdos1172BooleanFactor.lowerProjection e (φ.symm c) = Erdos1172BooleanFactor.lowerProjection f c := by
  apply le_antisymm
  · apply Erdos1172BooleanFactor.lowerProjection_le e
    exact φ.symm_apply_le.mpr ((Erdos1172BooleanFactor.le_image_lowerProjection f c).trans_eq (over _).symm)
  · apply Erdos1172BooleanFactor.lowerProjection_le f
    exact (φ.symm_apply_le.mp (Erdos1172BooleanFactor.le_image_lowerProjection e (φ.symm c))).trans_eq (over _)

theorem changeCompletion_factor (U : bSet A) (b : Algebra U) :
    changeCompletion e f φ over U (BaseChange.hom e U b) = BaseChange.hom f U b := by
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro p
  change (changeConditions e f φ over U).symm p ∈ (BaseChange.hom e U b).val ↔ p ∈ (BaseChange.hom f U b).val
  rw [← condition_le_iff,← condition_le_iff,BaseChange.cone_le_hom,BaseChange.cone_le_hom]
  suffices BaseChange.lower e U ((changeConditions e f φ over U).symm p) = BaseChange.lower f U p by rw [this]
  cases U with
  | mk I X w =>
    rcases p with ⟨c,hc,i,hi⟩
    change (⟨Erdos1172BooleanFactor.lowerProjection e (φ.symm c),_,i,_⟩ : Condition (.mk I X w)) =
      ⟨Erdos1172BooleanFactor.lowerProjection f c,_,i,_⟩
    congr 1
    exact lower_change e f φ over c

end Erdos1172BooleanNameIteration.Joint

namespace bSet.ErdosShioyaInternal
open Erdos1172BooleanNameIteration Erdos1172LevyCohen
variable {κ θ : Cardinal.{u}}
local notation "A" => anonymousAlgebra κ

theorem auxiliary_member {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    {e : CompleteLatticeHom (A) B} (S : SmallAuxiliary κ e) (hκ : κ.IsInaccessible) :
    ∃ q : bSet A, (⊤ : A) ≤ q ∈ᴮ S.forcing := by
  have hm := check_mem (𝔹 := A) (Γ := (⊤ : A)) (PSet.mk_mem_mk_of_lt
    (show (0 : Ordinal.{u}) < κ.ord from bot_lt_iff_ne_bot.mpr (by simpa using hκ.pos.ne')))
  let y := function_eval (S.enumerates.trans inf_le_left) _ hm
  exact ⟨y,function_eval_mem_codomain⟩

end bSet.ErdosShioyaInternal
