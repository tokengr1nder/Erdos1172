/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaCardinalPreservation
public import Erdos1172.Part4CheckedOrdinalCardinality
public import Erdos1172.Part4InternalGCHCardinalTransport
public import Erdos1172.Part4InternalMutualCardinalDichotomy

@[expose] public section

/-! # GCH at and above the upper parameter of the dual Shioya collapse -/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
open Lattice bSet Erdos1172PosetCompletion
universe u

namespace Erdos1172Shioya

variable (κ θ : Cardinal.{u}) [Fact (Cardinal.aleph0 < κ)] (hθ : θ.IsInaccessible)
include hθ

theorem coefficients_cardinal_le_two_power (μ : Cardinal.{u}) (hμ : θ ≤ μ)
    {I : Type u} (hI : Cardinal.mk I ≤ μ) : Cardinal.mk (I → Algebra κ θ) ≤ 2 ^ μ := by
  have h := completion_cardinal_le_two_pow_dense (Set.univ : Set (Condition κ θ))
    (fun p => ⟨p, Set.mem_univ _, le_rfl⟩)
  rw [Cardinal.mk_univ] at h
  have hc : Cardinal.mk (Algebra κ θ) ≤ 2 ^ θ := h.trans
    (Cardinal.power_le_power_left two_ne_zero (Condition.cardinal_le hθ))
  calc
    Cardinal.mk (I → Algebra κ θ) = Cardinal.mk (Algebra κ θ) ^ Cardinal.mk I :=
      (Cardinal.power_def _ _).symm
    _ ≤ ((2 : Cardinal.{u}) ^ θ) ^ Cardinal.mk I := Cardinal.power_le_power_right hc
    _ ≤ (2 ^ θ) ^ μ := Cardinal.power_le_power_left (ne_of_gt (bot_le.trans_lt (Cardinal.cantor θ))) hI
    _ = 2 ^ (θ * μ) := Cardinal.power_mul.symm
    _ = 2 ^ μ := by rw [Cardinal.mul_eq_right (hθ.aleph0_lt.le.trans hμ) hμ hθ.ne_zero]

variable [Nonempty (Condition κ θ)]

theorem checked_powerset_indices_cardinal_le (μ : Cardinal.{u}) (hμ : θ ≤ μ)
    (hg : (2 : Cardinal.{u}) ^ μ = Order.succ μ) :
    Cardinal.mk ((check (PSet.ordinalMk μ.ord) : bSet (Algebra κ θ)).type → Algebra κ θ) ≤
      Order.succ μ := by
  apply (coefficients_cardinal_le_two_power κ θ hθ μ hμ ?_).trans_eq hg
  rw [check_type', PSet.ordinalMk_type, Cardinal.mk_ord_toType]

theorem checked_powerset_injects_successor (μ : Cardinal.{u}) (hμ : θ ≤ μ)
    (hg : (2 : Cardinal.{u}) ^ μ = Order.succ μ) :
    (⊤ : Algebra κ θ) ≤ injects_into (bv_powerset (check (PSet.ordinalMk μ.ord)))
      (check (PSet.ordinalMk (Order.succ μ).ord)) :=
  ErdosGroundIndexNameBound.powerset_injects_checked_cardinal_of_index_cardinal_le
    (Order.succ μ) _ (checked_powerset_indices_cardinal_le κ θ hθ μ hμ hg)

theorem checked_successor_hartogsProperty (μ : Cardinal.{u}) (hμ : θ ≤ μ) :
    (⊤ : Algebra κ θ) ≤ ErdosHartogs.hartogsProperty (check (PSet.ordinalMk μ.ord))
      (check (PSet.ordinalMk (Order.succ μ).ord)) := by
  refine le_inf (check_Ord (PSet.Ord_mk _)) (le_inf ?_ ?_)
  · apply ErdosHartogs.not_injects_of_initialOrdinal
      (checked_initialOrdinal κ θ hθ (Order.succ μ) (hμ.trans_lt (Order.lt_succ μ)))
    exact check_mem (PSet.mk_mem_mk_of_lt (Cardinal.ord_lt_ord.mpr (Order.lt_succ μ)))
  · rw [PSet.ordinalMk_eq_def (Order.succ μ).ord, check_unfold,
      ← bounded_forall (h_congr := B_ext_injects_into_left)]
    change (⊤ : Algebra κ θ) ≤ ⨅ i : (Order.succ μ).ord.ToType, _root_.imp ⊤
      (injects_into (check (PSet.ordinalMk i.toOrd.val)) (check (PSet.ordinalMk μ.ord)))
    apply le_iInf
    intro i
    rw [top_imp]
    apply ErdosGroundIndexNameBound.injects_checked_cardinal_of_index_cardinal_le
    simpa only [check_type', PSet.ordinalMk_card] using (Cardinal.card_le_iff.mpr i.toOrd.property)

theorem checked_gchAt (μ : Cardinal.{u}) (hμ : θ ≤ μ) (hg : (2 : Cardinal.{u}) ^ μ = Order.succ μ) :
    (⊤ : Algebra κ θ) ≤ ErdosFullGCH.gchAt (check (PSet.ordinalMk μ.ord)) :=
  ErdosFullGCH.gchAt_of_witness (checked_successor_hartogsProperty κ θ hθ μ hμ)
    (checked_powerset_injects_successor κ θ hθ μ hμ hg)

theorem name_mutual_checked_ordinal (S : bSet (Algebra κ θ)) :
    (⊤ : Algebra κ θ) ≤ ⨆ η : Ordinal.{u}, injects_into S (check (PSet.ordinalMk η)) ⊓
      injects_into (check (PSet.ordinalMk η)) S := by
  let μ := max θ (Cardinal.mk S.type)
  have hs : (⊤ : Algebra κ θ) ≤ injects_into S (check (PSet.ordinalMk μ.ord)) :=
    ErdosGroundIndexNameBound.injects_checked_cardinal_of_index_cardinal_le μ S (le_max_right _ _)
  have hn : (injects_into (check (PSet.ordinalMk (Order.succ μ).ord)) S : Algebra κ θ) = ⊥ := by
    apply bot_unique
    exact (injects_into_trans le_rfl (le_top.trans hs)).trans_eq
      (checked_injects_predecessor_eq_bot κ θ hθ _ ((le_max_left _ _).trans_lt (Order.lt_succ μ))
        _ (Cardinal.ord_lt_ord.mpr (Order.lt_succ μ)))
  have hc := ErdosPartialInjection.ordinal_mutual_cardinal_dichotomy
    (S := S) (Γ := (⊤ : Algebra κ θ)) (check_Ord (PSet.Ord_mk (Order.succ μ).ord))
  rw [hn, bot_sup_eq] at hc
  have he : B_ext (fun A : bSet (Algebra κ θ) => injects_into S A ⊓ injects_into A S) :=
    B_ext_inf B_ext_injects_into_right B_ext_injects_into_left
  have hb := hc.trans_eq (bounded_exists (v := check (PSet.ordinalMk (Order.succ μ).ord))
    (h_congr := he)).symm
  rw [PSet.ordinalMk_eq_def, check_unfold] at hb
  change (⊤ : Algebra κ θ) ≤ ⨆ i : (Order.succ μ).ord.ToType,
    ⊤ ⊓ (injects_into S (check (PSet.ordinalMk i.toOrd.val)) ⊓
      injects_into (check (PSet.ordinalMk i.toOrd.val)) S) at hb
  exact hb.trans (iSup_le fun i => le_iSup_of_le i.toOrd.val inf_le_right)

/-- Tail GCH holds for any internal name into which the checked upper parameter injects,
on the full Boolean part where this injection exists. -/
theorem gchAt_of_checked_upper_injects
    (hg : ∀ μ : Cardinal.{u}, θ ≤ μ → (2 : Cardinal.{u}) ^ μ = Order.succ μ)
    (S : bSet (Algebra κ θ)) : injects_into (check (PSet.ordinalMk θ.ord)) S ≤ ErdosFullGCH.gchAt S := by
  apply (le_inf le_rfl (le_top.trans (name_mutual_checked_ordinal κ θ hθ S))).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro η
  let Γ : Algebra κ θ := injects_into (check (PSet.ordinalMk θ.ord)) S ⊓
    (injects_into S (check (PSet.ordinalMk η)) ⊓ injects_into (check (PSet.ordinalMk η)) S)
  have hs : Γ ≤ injects_into S (check (PSet.ordinalMk η)) := inf_le_right.trans inf_le_left
  have hη : Γ ≤ injects_into (check (PSet.ordinalMk η)) S := inf_le_right.trans inf_le_right
  by_cases h : θ ≤ η.card
  · apply ErdosFullGCH.gchAt_of_mutual_injections hη hs
    exact ErdosFullGCH.gchAt_of_mutual_injections
      (le_top.trans (ErdosCheckedOrdinalCardinality.checked_cardinal_injects_ordinal η))
      (le_top.trans (ErdosCheckedOrdinalCardinality.checked_ordinal_injects_cardinal η))
      (le_top.trans (checked_gchAt κ θ hθ η.card h (hg _ h)))
  · have hi : (⊤ : Algebra κ θ) ≤ injects_into (check (PSet.ordinalMk η)) (check (PSet.ordinalMk θ.ord)) := by
      apply ErdosGroundIndexNameBound.injects_checked_cardinal_of_index_cardinal_le
      simpa only [check_type', PSet.ordinalMk_card] using (le_of_not_ge h)
    exact ErdosFullGCH.gchAt_of_mutual_injections (show Γ ≤ injects_into (check (PSet.ordinalMk θ.ord)) S from
      inf_le_left) (injects_into_trans hs (le_top.trans hi)) (le_top.trans (checked_gchAt κ θ hθ θ le_rfl (hg _ le_rfl)))

end Erdos1172Shioya
