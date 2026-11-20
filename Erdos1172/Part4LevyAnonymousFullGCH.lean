/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyAnonymousCH
public import Erdos1172.Part4LevyCohenFullGCH

@[expose] public section

/-! # Full GCH in the anonymous collapse

An injection between two checked ordinals transports to the ambient
Levy–Cohen algebra. This preserves the strict successor gaps above κ.
The bound on the full anonymous powerset descends using the ambient
powerset bound and the next successor gap. Below κ, recovery of
countable enumerations gives countability. The internal ordinal
dichotomy supplies local representatives for arbitrary mixed names.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172LevyCohen

open bSet ErdosNameTransport Erdos1172CompleteSubalgebra
open ErdosFullGCH ErdosCheckedOrdinalCardinality

theorem anonymous_checked_successor_injects_base_eq_bot (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) (μ : Cardinal.{u}) (Hκμ : κ ≤ μ) :
    (injects_into (check (PSet.ordinalMk (Order.succ μ).ord))
      (check (PSet.ordinalMk μ.ord)) : anonymousAlgebra κ) = ⊥ := by
  let e := inclusion (anonymousAlgebra κ)
  let c : anonymousAlgebra κ := injects_into (check (PSet.ordinalMk (Order.succ μ).ord))
    (check (PSet.ordinalMk μ.ord))
  have Hord : e c ≤ Ord (mapNames e (check (PSet.ordinalMk μ.ord))) := by
    rw [map_check]
    exact check_Ord (PSet.Ord_mk μ.ord)
  have Hmap := map_injects_into_of_ordinal e (show c ≤
    injects_into (check (PSet.ordinalMk (Order.succ μ).ord)) (check (PSet.ordinalMk μ.ord))
    from le_rfl) Hord
  simp only [map_check] at Hmap
  apply inclusion_injective (anonymousAlgebra κ)
  exact (bot_unique (Hmap.trans_eq (checked_successor_injects_base_eq_bot κ Hκ μ Hκμ))).trans
    (map_bot e).symm

theorem anonymous_checked_successor_hartogsProperty (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) (μ : Cardinal.{u}) (Hκμ : κ ≤ μ) :
    (⊤ : anonymousAlgebra κ) ≤ ErdosHartogs.hartogsProperty (check (PSet.ordinalMk μ.ord))
      (check (PSet.ordinalMk (Order.succ μ).ord)) := by
  refine le_inf (check_Ord (PSet.Ord_mk (Order.succ μ).ord)) (le_inf ?_ ?_)
  · rw [anonymous_checked_successor_injects_base_eq_bot κ Hκ μ Hκμ, compl_bot]
  · rw [PSet.ordinalMk_eq_def (Order.succ μ).ord, check_unfold]
    rw [← bounded_forall (h_congr := B_ext_injects_into_left)]
    change (⊤ : anonymousAlgebra κ) ≤ ⨅ i : (Order.succ μ).ord.ToType, _root_.imp ⊤
      (injects_into (check (PSet.ordinalMk i.toOrd.val)) (check (PSet.ordinalMk μ.ord)))
    apply le_iInf
    intro i
    rw [top_imp]
    apply ErdosGroundIndexNameBound.injects_checked_cardinal_of_index_cardinal_le
    simpa only [check_type', PSet.ordinalMk_card] using (Cardinal.card_le_iff.mpr i.toOrd.property)

theorem anonymous_checked_gchAt (κ μ : Cardinal.{u}) (Hκ : κ.IsInaccessible) (Hκμ : κ ≤ μ)
    (HGCHμ : (2 : Cardinal.{u}) ^ μ = Order.succ μ) :
    (⊤ : anonymousAlgebra κ) ≤ gchAt (check (PSet.ordinalMk μ.ord)) := by
  apply gchAt_of_witness (anonymous_checked_successor_hartogsProperty κ Hκ μ Hκμ)
  apply anonymous_injects_checked_of_ambient κ Hκ (Order.succ μ) (Hκμ.trans (Order.le_succ _))
  have Hsub := map_powerset_subset (inclusion (anonymousAlgebra κ))
    (check (PSet.ordinalMk μ.ord) : bSet (anonymousAlgebra κ))
  rw [map_check] at Hsub
  exact injects_into_trans (injects_into_of_subset Hsub)
    (checked_powerset_injects_successor κ μ Hκ Hκμ HGCHμ)

theorem anonymous_name_mutual_checked_ordinal (κ : Cardinal.{u}) (Hκ : κ.IsInaccessible)
    (S : bSet (anonymousAlgebra κ)) :
    (⊤ : anonymousAlgebra κ) ≤ ⨆ η : Ordinal.{u},
      injects_into S (check (PSet.ordinalMk η)) ⊓ injects_into (check (PSet.ordinalMk η)) S := by
  let μ := max κ (Cardinal.mk S.type)
  have HS : (⊤ : anonymousAlgebra κ) ≤ injects_into S (check (PSet.ordinalMk μ.ord)) :=
    ErdosGroundIndexNameBound.injects_checked_cardinal_of_index_cardinal_le μ S (le_max_right _ _)
  have Hnot : (injects_into (check (PSet.ordinalMk (Order.succ μ).ord)) S :
      anonymousAlgebra κ) = ⊥ := by
    apply bot_unique
    exact (injects_into_trans le_rfl (le_top.trans HS)).trans_eq
      (anonymous_checked_successor_injects_base_eq_bot κ Hκ μ (le_max_left _ _))
  have Hcase := ErdosPartialInjection.ordinal_mutual_cardinal_dichotomy
    (S := S) (Γ := (⊤ : anonymousAlgebra κ)) (check_Ord (PSet.Ord_mk (Order.succ μ).ord))
  rw [Hnot, bot_sup_eq] at Hcase
  have Hext : B_ext (fun A : bSet (anonymousAlgebra κ) => injects_into S A ⊓ injects_into A S) :=
    B_ext_inf B_ext_injects_into_right B_ext_injects_into_left
  have Hbounded := Hcase.trans_eq
    (bounded_exists (v := check (PSet.ordinalMk (Order.succ μ).ord)) (h_congr := Hext)).symm
  rw [PSet.ordinalMk_eq_def, check_unfold] at Hbounded
  change (⊤ : anonymousAlgebra κ) ≤ ⨆ i : (Order.succ μ).ord.ToType,
    ⊤ ⊓ (injects_into S (check (PSet.ordinalMk i.toOrd.val)) ⊓
      injects_into (check (PSet.ordinalMk i.toOrd.val)) S) at Hbounded
  exact Hbounded.trans (iSup_le fun i => le_iSup_of_le i.toOrd.val inf_le_right)

theorem anonymous_gchAt_checked_ordinal (κ : Cardinal.{u}) (Hκ : κ.IsInaccessible)
    (HGCH : ∀ μ : Cardinal.{u}, κ ≤ μ → (2 : Cardinal.{u}) ^ μ = Order.succ μ)
    (η : Ordinal.{u}) {Γ : anonymousAlgebra κ}
    (Hinf : Γ ≤ injects_into omega (check (PSet.ordinalMk η))) :
    Γ ≤ gchAt (check (PSet.ordinalMk η)) := by
  by_cases Hsmall : η.card < κ
  · have Hcnt := anonymous_checked_countable_of_ambient κ Hκ.isRegular Hκ.aleph0_lt
      (PSet.ordinalMk η) (PSet.ordinalMk_inj η)
      (checked_ordinal_countable_of_cardinal_lt κ η Hsmall)
    apply gchAt_of_mutual_injections Hinf (le_top.trans Hcnt)
    rw [gchAt_omega_eq_CH]
    exact le_top.trans (anonymous_forces_CH κ Hκ)
  · have Hlarge : κ ≤ η.card := le_of_not_gt Hsmall
    exact gchAt_of_mutual_injections
      (le_top.trans (checked_cardinal_injects_ordinal η))
      (le_top.trans (checked_ordinal_injects_cardinal η))
      (le_top.trans (anonymous_checked_gchAt κ η.card Hκ Hlarge (HGCH η.card Hlarge)))

/-- Full GCH, quantified over every internally infinite anonymous name. -/
theorem anonymous_forces_fullGCH (κ : Cardinal.{u}) (Hκ : κ.IsInaccessible)
    (HGCH : ∀ μ : Cardinal.{u}, κ ≤ μ → (2 : Cardinal.{u}) ^ μ = Order.succ μ) :
    (⊤ : anonymousAlgebra κ) ≤ fullGCHValue := by
  apply le_iInf
  intro S
  rw [← deduction]
  have Hrep := anonymous_name_mutual_checked_ordinal κ Hκ S
  apply (le_inf (le_refl (⊤ ⊓ injects_into omega S)) (le_top.trans Hrep)).trans
  erw [inf_iSup_eq]
  apply iSup_le
  intro η
  let Γ : anonymousAlgebra κ := (⊤ ⊓ injects_into omega S) ⊓
    (injects_into S (check (PSet.ordinalMk η)) ⊓ injects_into (check (PSet.ordinalMk η)) S)
  have Hto : Γ ≤ injects_into S (check (PSet.ordinalMk η)) := inf_le_right.trans inf_le_left
  have Hfrom : Γ ≤ injects_into (check (PSet.ordinalMk η)) S := inf_le_right.trans inf_le_right
  exact gchAt_of_mutual_injections Hfrom Hto
    (anonymous_gchAt_checked_ordinal κ Hκ HGCH η
      (injects_into_trans (inf_le_left.trans inf_le_right) Hto))

end Erdos1172LevyCohen
