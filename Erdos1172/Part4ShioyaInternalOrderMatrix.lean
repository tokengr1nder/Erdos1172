/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalOrder

@[expose] public section

/-! # Exact incidence matrices for arbitrary named ordinal orders -/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
universe u
namespace bSet.ErdosShioyaInternal
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

def ordinalCarrier (α : Ordinal.{u}) : N := check (PSet.ordinalMk α)
def ordinalLabel {α : Ordinal.{u}} (i : α.ToType) : N := check (PSet.ordinalMk i.toOrd.val)
theorem someIn_checked (α : Ordinal.{u}) (f : N → B) (h : B_ext f) :
    someIn (ordinalCarrier α) f = ⨆ i : α.ToType, f (ordinalLabel i) := by
  unfold someIn ordinalCarrier
  rw [PSet.ordinalMk_eq_def α,check_unfold,← bounded_exists (h_congr := h)]
  exact iSup_congr fun _ => top_inf_eq _

theorem ordinalLabel_eq {α : Ordinal.{u}} (i j : α.ToType) :
    (ordinalLabel i =ᴮ (ordinalLabel j : N)) = if i = j then ⊤ else ⊥ := by
  by_cases he : i = j
  · subst j
    rw [if_pos rfl]
    exact top_unique bv_refl
  · rw [if_neg he]
    exact check_bv_eq_bot_of_not_equiv (fun h => he (Ordinal.ToType.mk.symm.injective (Subtype.ext (PSet.eq_of_mk_equiv h))))

end bSet.ErdosShioyaInternal
