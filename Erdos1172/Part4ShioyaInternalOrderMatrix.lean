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
def checkedEdge {α β : Ordinal.{u}} (R : N) (i : α.ToType) (j : β.ToType) : B := edge R (ordinalLabel i) (ordinalLabel j)

theorem allIn_checked (α : Ordinal.{u}) (f : N → B) (h : B_ext f) :
    allIn (ordinalCarrier α) f = ⨅ i : α.ToType, f (ordinalLabel i) := by
  unfold allIn ordinalCarrier
  rw [PSet.ordinalMk_eq_def α,check_unfold,← bounded_forall (h_congr := h)]
  apply iInf_congr
  intro i
  change ((⊤ : B) ⟹ f (ordinalLabel i)) = _
  simp [_root_.imp]

theorem someIn_checked (α : Ordinal.{u}) (f : N → B) (h : B_ext f) :
    someIn (ordinalCarrier α) f = ⨆ i : α.ToType, f (ordinalLabel i) := by
  unfold someIn ordinalCarrier
  rw [PSet.ordinalMk_eq_def α,check_unfold,← bounded_exists (h_congr := h)]
  exact iSup_congr fun _ => top_inf_eq _

theorem allIn_checked₂ (α : Ordinal.{u}) (f : N → N → B)
    (hx : ∀ y, B_ext (fun x => f x y)) (hy : ∀ x, B_ext (f x)) :
    allIn (ordinalCarrier α) (fun x => allIn (ordinalCarrier α) (f x)) =
      ⨅ i : α.ToType, ⨅ j : α.ToType, f (ordinalLabel i) (ordinalLabel j) :=
  (allIn_checked α _ (allIn_ext (const_congr _) hx)).trans
    (iInf_congr fun i => allIn_checked α _ (hy (ordinalLabel i)))

theorem allIn_checked₃ (α : Ordinal.{u}) (f : N → N → N → B)
    (hx : ∀ y z, B_ext (fun x => f x y z)) (hy : ∀ x z, B_ext (fun y => f x y z))
    (hz : ∀ x y, B_ext (f x y)) :
    allIn (ordinalCarrier α) (fun x => allIn (ordinalCarrier α) (fun y => allIn (ordinalCarrier α) (f x y))) =
      ⨅ i : α.ToType, ⨅ j : α.ToType, ⨅ k : α.ToType, f (ordinalLabel i) (ordinalLabel j) (ordinalLabel k) :=
  (allIn_checked₂ α _ (fun y => allIn_ext (const_congr _) (hx y)) (fun x => allIn_ext (const_congr _) (hy x))).trans
    (iInf_congr fun i => iInf_congr fun j => allIn_checked α _ (hz (ordinalLabel i) (ordinalLabel j)))

theorem ordinalLabel_eq {α : Ordinal.{u}} (i j : α.ToType) :
    (ordinalLabel i =ᴮ (ordinalLabel j : N)) = if i = j then ⊤ else ⊥ := by
  by_cases he : i = j
  · subst j
    rw [if_pos rfl]
    exact top_unique bv_refl
  · rw [if_neg he]
    exact check_bv_eq_bot_of_not_equiv (fun h => he (Ordinal.ToType.mk.symm.injective (Subtype.ext (PSet.eq_of_mk_equiv h))))

def matrixOrder {V : Type u} [DecidableEq V] (r : V → V → B) : B :=
  (⨅ i, r i i) ⊓ ((⨅ i, ⨅ j, (r i j ⊓ r j i) ⟹ (if i = j then ⊤ else ⊥)) ⊓
    ⨅ i, ⨅ j, ⨅ k, (r i j ⊓ r j k) ⟹ r i k)

def matrixCompatible {V : Type u} (r : V → V → B) (i j : V) : B := ⨆ k, r k i ⊓ r k j
def matrixSeparative {V : Type u} (r : V → V → B) : B :=
  ⨅ i, ⨅ j, (r i j)ᶜ ⟹ ⨆ k, r k i ⊓ (matrixCompatible r k j)ᶜ

theorem partialOrderValue_checked (α : Ordinal.{u}) (R : N) :
    partialOrderValue (ordinalCarrier α) R =
      (R ⊆ᴮ prod (ordinalCarrier α) (ordinalCarrier α)) ⊓ matrixOrder (checkedEdge (α := α) (β := α) R) := by
  unfold partialOrderValue matrixOrder
  apply congrArg (_ ⊓ ·)
  apply congrArg₂ (· ⊓ ·)
  · exact allIn_checked α _ (edge_ext (const_congr R) id_congr id_congr)
  apply congrArg₂ (· ⊓ ·)
  · apply (allIn_checked₂ α (fun p q => (edge R p q ⊓ edge R q p) ⟹ (p =ᴮ q))
      (fun _ => B_ext_imp (h₁ := B_ext_inf B_ext_pair_mem_left B_ext_pair_mem_right) (h₂ := B_ext_bv_eq_left))
      (fun _ => B_ext_imp (h₁ := B_ext_inf B_ext_pair_mem_right B_ext_pair_mem_left) (h₂ := B_ext_bv_eq_right))).trans
    exact iInf_congr fun i => iInf_congr fun j => congrArg (imp _) (ordinalLabel_eq i j)
  · exact allIn_checked₃ α (fun p q t => (edge R p q ⊓ edge R q t) ⟹ edge R p t)
      (fun _ _ => B_ext_imp (h₁ := B_ext_inf B_ext_pair_mem_left B_ext_const) (h₂ := B_ext_pair_mem_left))
      (fun _ _ => B_ext_imp (h₁ := B_ext_inf B_ext_pair_mem_right B_ext_pair_mem_left) (h₂ := B_ext_const))
      (fun _ _ => B_ext_imp (h₁ := B_ext_inf B_ext_const B_ext_pair_mem_right) (h₂ := B_ext_pair_mem_right))

theorem compatibleValue_checked (α : Ordinal.{u}) (R : N) (i j : α.ToType) :
    compatibleValue (ordinalCarrier α) R (ordinalLabel i) (ordinalLabel j) = matrixCompatible (checkedEdge R) i j :=
  someIn_checked α _ (B_ext_inf B_ext_pair_mem_left B_ext_pair_mem_left)

theorem separativeValue_checked (α : Ordinal.{u}) (R : N) :
    separativeValue (ordinalCarrier α) R = matrixSeparative (checkedEdge (α := α) (β := α) R) := by
  let P : N := ordinalCarrier α
  apply (allIn_checked₂ α (fun p q => (edge R p q)ᶜ ⟹ separatesValue P R p q)
    (fun q => B_ext_imp (h₁ := B_ext_neg (h := B_ext_pair_mem_left))
      (h₂ := separatesValue_ext (const_congr P) (const_congr R) id_congr (const_congr q)))
    (fun p => B_ext_imp (h₁ := B_ext_neg (h := B_ext_pair_mem_right))
      (h₂ := separatesValue_ext (const_congr P) (const_congr R) (const_congr p) id_congr))).trans
  apply iInf_congr
  intro i
  apply iInf_congr
  intro j
  apply congrArg (imp _)
  apply (someIn_checked α (fun t => edge R t (ordinalLabel i) ⊓ (compatibleValue P R t (ordinalLabel j))ᶜ)
    (B_ext_inf B_ext_pair_mem_left (B_ext_neg (h := compatibleValue_ext (const_congr P) (const_congr R) id_congr (const_congr _))))).trans
  exact iSup_congr fun k => congrArg (_ ⊓ ·) (congrArg compl (compatibleValue_checked α R k j))

end bSet.ErdosShioyaInternal
