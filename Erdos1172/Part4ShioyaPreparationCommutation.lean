/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4SideForcingBaseChange
public import Erdos1172.Part4ShioyaDenseCoverIso

@[expose] public section

/-! # Commuting two independently named forcing orders over one Boolean algebra -/

set_option autoImplicit false
noncomputable section
universe u
open bSet ErdosNameTransport Erdos1172PosetCompletion Erdos1172Shioya.ForcingCover
open scoped Flypitch
namespace Erdos1172BooleanNameIteration.Joint
variable {A : Type u} [NontrivialCompleteBooleanAlgebra A]

/-- Both labels are supported by the same positive first-stage value. -/
structure PairCondition (U V : bSet A) where
  first : Condition U
  second : Condition V
  common : first.value = second.value

instance (U V : bSet A) : Preorder (PairCondition U V) :=
  Preorder.lift (fun p => (p.first,p.second))

def swap (U V : bSet A) : PairCondition U V ≃o PairCondition V U where
  toFun p := ⟨p.second,p.first,p.common.symm⟩
  invFun p := ⟨p.second,p.first,p.common.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := and_comm

local instance stageNCBA (U : bSet A) [Nonempty (Condition U)] : NontrivialCompleteBooleanAlgebra (Algebra U) where
  toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra
  bot_lt_top := bot_lt_top

variable (U : bSet A) [Nonempty (Condition U)]
local notation "j" => sourceHom U
local notation "m" => mapNames (j)

def stack : (V : bSet A) → PairCondition U V → Condition (m V)
  | .mk _ _ _, p => ⟨condition p.first,condition_ne_bot _,p.second.index,
      (condition_le_source U _ _).mpr (p.common.le.trans p.second.valid)⟩

theorem stack_value (V : bSet A) (p : PairCondition U V) : (stack U V p).value = condition p.first := by
  cases V
  rfl

theorem stack_name (V : bSet A) (p : PairCondition U V) : name (stack U V p) = m (name p.second) := by
  cases V
  rfl

def stackHom (V : bSet A) : PairCondition U V →o Condition (m V) where
  toFun := stack U V
  monotone' := by
    intro a b h
    rw [le_iff,stack_value,stack_value,stack_name,stack_name,← map_subset,condition_le_source]
    exact ⟨condition_mono h.1,a.common.le.trans h.2.2⟩

def unstack : (V : bSet A) → (t : Condition (m V)) → (p : Condition U) →
    condition p ≤ t.value → PairCondition U V
  | .mk _ _ _, t, p, hp => ⟨p,⟨p.value,p.nonzero,t.index,(condition_le_source U p _).mp (hp.trans t.valid)⟩,rfl⟩

private theorem unstack_first (V : bSet A) (t : Condition (m V)) (p : Condition U) (hp : condition p ≤ t.value) :
    (unstack U V t p hp).first = p := by cases V; rfl

private theorem unstack_name (V : bSet A) (t : Condition (m V)) (p : Condition U) (hp : condition p ≤ t.value) :
    m (name (unstack U V t p hp).second) = name t := by cases V; rfl

private theorem stack_unstack_le (V : bSet A) (t : Condition (m V)) (p : Condition U) (hp : condition p ≤ t.value) :
    stackHom U V (unstack U V t p hp) ≤ t := by
  change stack U V _ ≤ t
  rw [le_iff,stack_value,unstack_first,stack_name,unstack_name]
  exact ⟨hp,subset_self⟩

private theorem unstack_le (V : bSet A) (t : Condition (m V)) (p : Condition U) (hp : condition p ≤ t.value)
    (a : PairCondition U V) (first : p ≤ a.first) (ht : t ≤ stackHom U V a) :
    unstack U V t p hp ≤ a := by
  let z := unstack U V t p hp
  have f : z.first = p := unstack_first U V t p hp
  have value : z.second.value = p.value := z.common.symm.trans (congrArg Condition.value f)
  change z.first ≤ a.first ∧ z.second ≤ a.second
  refine ⟨f.le.trans first, value.le.trans (first.1.trans a.common.le),?_⟩
  rw [value,← condition_le_source U p, map_subset,unstack_name]
  exact hp.trans ((stack_name U V a) ▸ ht.2)

theorem stack_dense (V : bSet A) (t : Condition (m V)) : ∃ z, stackHom U V z ≤ t := by
  obtain ⟨p,hp⟩ := exists_condition_le t.nonzero
  exact ⟨_,stack_unstack_le U V t p hp⟩

theorem stack_lifts (V : bSet A) : Lifts (stackHom U V) := by
  intro a t ht
  obtain ⟨p,hp⟩ := exists_condition_le t.nonzero
  have leCone : condition p ≤ condition a.first := (hp.trans ht.1).trans_eq (stack_value U V a)
  obtain ⟨q,hq,ha⟩ := (mem_condition_iff a.first p).mp (condition_le_iff.mp leCone) p le_rfl
  have hq' := (condition_mono hq).trans hp
  exact ⟨_,unstack_le U V t q hq' a ha ht,stack_unstack_le U V t q hq'⟩

theorem stack_compatible (V : bSet A) (a b : PairCondition U V) (h : stackHom U V a ≤ stackHom U V b) :
    ∃ z ≤ a, z ≤ b := by
  have first : condition a.first ≤ condition b.first := (stack_value U V a).ge.trans (h.1.trans_eq (stack_value U V b))
  obtain ⟨p,ha,hb⟩ := (mem_condition_iff b.first a.first).mp (condition_le_iff.mp first) a.first le_rfl
  have hp : condition p ≤ (stackHom U V a).value := (condition_mono ha).trans_eq (stack_value U V a).symm
  exact ⟨_,unstack_le U V _ p hp a ha le_rfl,unstack_le U V _ p hp b hb h⟩

def stackIso (V : bSet A) : Algebra (m V) ≃o Completion (PairCondition U V) :=
  completionIso (stackHom U V) (stack_lifts U V) (stack_compatible U V) (stack_dense U V)

omit [Nonempty (Condition U)] in
theorem lowerProjection_condition (p : Condition U) :
    Erdos1172BooleanFactor.lowerProjection (j) (condition p) = p.value := by
  apply le_antisymm
  · exact Erdos1172BooleanFactor.lowerProjection_le (j) ((condition_le_source U p _).mpr le_rfl)
  · exact (condition_le_source U p _).mp (Erdos1172BooleanFactor.le_image_lowerProjection (j) _)

theorem stack_lower (V : bSet A) (p : PairCondition U V) :
    BaseChange.lower (j) V (stack U V p) = p.second := by
  cases V with
  | mk I f w =>
    rcases p with ⟨a,⟨v,hv,i,hi⟩,eq⟩
    change (⟨Erdos1172BooleanFactor.lowerProjection (j) (condition a),_,i,_⟩ : Condition _) = ⟨v,hv,i,hi⟩
    congr 1
    exact (lowerProjection_condition U a).trans eq

variable (V : bSet A) [Nonempty (Condition V)]

def swapHom : PairCondition V U →o PairCondition U V :=
  ⟨swap V U,(swap V U).monotone⟩

def swapIso : Completion (PairCondition U V) ≃o Completion (PairCondition V U) :=
  completionIso (swapHom U V)
    (fun _ q h => ⟨swap U V q,(swap U V).monotone h,le_rfl⟩)
    (fun a _ h => ⟨a,le_rfl,(swap V U).le_iff_le.mp h⟩)
    (fun t => ⟨swap U V t,le_rfl⟩)

/-- The named factors may be forced in either order, provided the second
factor in each ordering is the transported first-stage name. -/
def commutation : Algebra (m V) ≃o Algebra (mapNames (sourceHom V) U) :=
  ((stackIso U V).trans (swapIso U V)).trans (stackIso V U).symm

/-- The isomorphism takes the whole first factor to its canonical copy
in the opposite ordering, over the same initial Boolean algebra. -/
theorem commutation_left (c : Algebra U) :
    commutation U V (sourceHom (m V) c) = BaseChange.hom (sourceHom V) U c := by
  apply (stackIso V U).injective
  change stackIso V U ((stackIso V U).symm _) = _
  rw [OrderIso.apply_symm_apply]
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro t
  change stack U V (swap V U t) ∈ (sourceHom (m V) c).val ↔ stack V U t ∈ (BaseChange.hom (sourceHom V) U c).val
  rw [← condition_le_iff,← condition_le_iff,condition_le_source,BaseChange.cone_le_hom,stack_lower,stack_value]
  rfl

theorem commutation_right (c : Algebra V) :
    commutation U V (BaseChange.hom (j) V c) = sourceHom (mapNames (sourceHom V) U) c := by
  apply (stackIso V U).injective
  change stackIso V U ((stackIso V U).symm _) = _
  rw [OrderIso.apply_symm_apply]
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro t
  change stack U V (swap V U t) ∈ (BaseChange.hom (j) V c).val ↔ stack V U t ∈ (sourceHom _ c).val
  rw [← condition_le_iff,← condition_le_iff,condition_le_source,BaseChange.cone_le_hom,stack_lower,stack_value]
  rfl

end Erdos1172BooleanNameIteration.Joint
