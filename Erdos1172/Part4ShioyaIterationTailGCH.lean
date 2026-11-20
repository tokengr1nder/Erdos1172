/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalGCHCardinalTransport
public import Erdos1172.Part4ShioyaCoverPreservation

@[expose] public section

/-! # The high-cardinal GCH tail of the combined iteration -/

set_option autoImplicit false
noncomputable section
universe u
open scoped Flypitch
open bSet Erdos1172PosetCompletion Lattice
namespace Erdos1172Shioya

namespace DenseCompletion

variable {P : Type u} [Preorder P] [Nonempty P]
local instance : NontrivialCompleteBooleanAlgebra (Completion P) where
  toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra
  bot_lt_top := bot_lt_top

variable (D : Set P) (dense : ∀ p, ∃ d ∈ D, d ≤ p)

include dense in
theorem successor_hartogs (μ : Cardinal.{u}) (inf : Cardinal.aleph0 ≤ μ) (size : Cardinal.mk D ≤ μ) :
    (⊤ : Completion P) ≤ ErdosHartogs.hartogsProperty (check (PSet.ordinalMk μ.ord))
      (check (PSet.ordinalMk (Order.succ μ).ord)) := by
  refine le_inf (check_Ord (PSet.Ord_mk _)) (le_inf ?_ ?_)
  · rw [successor_gap_of_dense_cover μ inf D dense size,compl_bot]
  · rw [PSet.ordinalMk_eq_def (Order.succ μ).ord,check_unfold,← bounded_forall (h_congr := B_ext_injects_into_left)]
    change (⊤ : Completion P) ≤ ⨅ i : (Order.succ μ).ord.ToType, _root_.imp ⊤
      (injects_into (check (PSet.ordinalMk i.toOrd.val)) (check (PSet.ordinalMk μ.ord)))
    apply le_iInf
    intro i
    rw [top_imp]
    apply ErdosGroundIndexNameBound.injects_checked_cardinal_of_index_cardinal_le
    simpa only [check_type',PSet.ordinalMk_card] using (Cardinal.card_le_iff.mpr i.toOrd.property)

include dense in
theorem checked_gchAt (μ : Cardinal.{u}) (inf : Cardinal.aleph0 ≤ μ) (size : Cardinal.mk D ≤ μ)
    (ground : (2 : Cardinal.{u}) ^ μ = Order.succ μ) :
    (⊤ : Completion P) ≤ ErdosFullGCH.gchAt (check (PSet.ordinalMk μ.ord)) := by
  have hB : Cardinal.mk (Completion P) ≤ 2 ^ μ := (completion_cardinal_le_two_pow_dense D dense).trans
    (Cardinal.power_le_power_left two_ne_zero size)
  apply ErdosFullGCH.gchAt_of_witness (successor_hartogs D dense μ inf size)
  apply ErdosGroundIndexNameBound.powerset_injects_checked_cardinal_of_index_cardinal_le
  rw [← Cardinal.power_def,check_type',PSet.ordinalMk_type,Cardinal.mk_ord_toType]
  calc
    Cardinal.mk (Completion P) ^ μ ≤ ((2 : Cardinal.{u}) ^ μ) ^ μ := Cardinal.power_le_power_right hB
    _ = 2 ^ (μ * μ) := Cardinal.power_mul.symm
    _ = Order.succ μ := by rw [Cardinal.mul_eq_self inf,ground]

include dense in
/-- Every name is mutually injectable with some checked ordinal on a Boolean
cover, without a ground continuum hypothesis or a fixed forcing-size bound. -/
theorem name_mutual_checked_ordinal (S : bSet (Completion P)) :
    (⊤ : Completion P) ≤ ⨆ η : Ordinal.{u}, injects_into S (check (PSet.ordinalMk η)) ⊓
      injects_into (check (PSet.ordinalMk η)) S := by
  let μ := max (max Cardinal.aleph0 (Cardinal.mk D)) (Cardinal.mk S.type)
  have inf : Cardinal.aleph0 ≤ μ := (le_max_left _ _).trans (le_max_left _ _)
  have size : Cardinal.mk D ≤ μ := (le_max_right _ _).trans (le_max_left _ _)
  have below : (⊤ : Completion P) ≤ injects_into S (check (PSet.ordinalMk μ.ord)) :=
    ErdosGroundIndexNameBound.injects_checked_cardinal_of_index_cardinal_le μ S (le_max_right _ _)
  have gap : (injects_into (check (PSet.ordinalMk (Order.succ μ).ord)) S : Completion P) = ⊥ :=
    bot_unique ((injects_into_trans le_rfl (le_top.trans below)).trans_eq
      (successor_gap_of_dense_cover μ inf D dense size))
  have disj := ErdosPartialInjection.ordinal_mutual_cardinal_dichotomy
    (S := S) (Γ := (⊤ : Completion P)) (check_Ord (PSet.Ord_mk (Order.succ μ).ord))
  rw [gap,bot_sup_eq] at disj
  have ext : B_ext (fun X : bSet (Completion P) => injects_into S X ⊓ injects_into X S) :=
    B_ext_inf B_ext_injects_into_right B_ext_injects_into_left
  have cover := disj.trans_eq (bounded_exists (v := check (PSet.ordinalMk (Order.succ μ).ord)) (h_congr := ext)).symm
  rw [PSet.ordinalMk_eq_def,check_unfold] at cover
  change (⊤ : Completion P) ≤ ⨆ i : (Order.succ μ).ord.ToType,
    ⊤ ⊓ (injects_into S (check (PSet.ordinalMk i.toOrd.val)) ⊓
      injects_into (check (PSet.ordinalMk i.toOrd.val)) S) at cover
  exact cover.trans (iSup_le fun i => le_iSup_of_le i.toOrd.val inf_le_right)

end DenseCompletion
