/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyCohenDensePresentation
public import Erdos1172.Part4BooleanCardinalPreservation
public import Erdos1172.Part4GroundIndexNameBound
public import Erdos1172.Part4InternalHartogsUniqueness

@[expose] public section

/-!
# Checked successor Hartogs ordinals in the actual Levy--Cohen iteration

The constructed dense presentation bounds every positive disjoint family
by kappa. Thus the regular threshold used for noncollapse is successor
kappa, not kappa. Every ground cardinal mu at least kappa has checked
successor mu as the internal Hartogs ordinal of checked mu in the actual
two-stage algebra.

Predecessor countability is not assumed: all predecessors inject into
checked mu by their actual index bounds, and bounded quantification covers
arbitrary mixed predecessor names. Mu may be singular. No ground GCH,
internal successor-identification premise, or ideal is used.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172LevyCohen

open bSet

/-- Apply the actual disjoint-family bound at the regular threshold
successor kappa. The separated target can itself have singular cardinality. -/
theorem surjects_onto_eq_bot_of_cardinal_lt (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible)
    (X Y : PSet.{u}) (Hlt : Cardinal.mk X.Type < Cardinal.mk Y.Type)
    (HY : Order.succ κ ≤ Cardinal.mk Y.Type)
    (Hsep : ∀ i j : Y.Type, i ≠ j → ¬ PSet.Equiv (Y.Func i) (Y.Func j)) :
    (surjects_onto (check X) (check Y) : Algebra κ) = ⊥ :=
  ErdosCardinalPreservation.surjects_onto_eq_bot_of_cardinal_lt
    (κ := Order.succ κ) (Cardinal.isRegular_succ Hκ.aleph0_lt.le)
    (fun w Hpositive Hdisjoint =>
      (disjoint_family_cardinal_le_upper κ Hκ w Hpositive Hdisjoint).trans_lt
        (Order.lt_succ κ)) X Y Hlt HY Hsep

/-- No arbitrary internal graph surjects from checked mu onto its checked
ground successor, including when mu is singular. -/
theorem checked_successor_surjects_eq_bot (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) (μ : Cardinal.{u}) (Hκμ : κ ≤ μ) :
    (surjects_onto (check (PSet.ordinalMk μ.ord))
      (check (PSet.ordinalMk (Order.succ μ).ord)) : Algebra κ) = ⊥ :=
  surjects_onto_eq_bot_of_cardinal_lt κ Hκ
    (PSet.ordinalMk μ.ord) (PSet.ordinalMk (Order.succ μ).ord)
    (by simpa only [PSet.ordinalMk_type, Cardinal.mk_ord_toType] using Order.lt_succ μ)
    (by simpa only [PSet.ordinalMk_type, Cardinal.mk_ord_toType] using
      Order.succ_le_succ Hκμ)
    (PSet.ordinalMk_inj (Order.succ μ).ord)

/-- Counting checked successor mu by checked mu would give the forbidden
surjection. Nonemptiness of the checked successor is explicitly proved. -/
theorem checked_successor_injects_base_eq_bot (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) (μ : Cardinal.{u}) (Hκμ : κ ≤ μ) :
    (injects_into (check (PSet.ordinalMk (Order.succ μ).ord))
      (check (PSet.ordinalMk μ.ord)) : Algebra κ) = ⊥ := by
  have Hnonempty : (⊤ : Algebra κ) ≤
      exists_mem (check (PSet.ordinalMk (Order.succ μ).ord)) := by
    obtain ⟨z, Hz⟩ := PSet.exists_mem_of_nonzero
      (Cardinal.ord_pos.mpr (Cardinal.succ_pos μ))
    change (⊤ : Algebra κ) ≤ ⨆ x : bSet (Algebra κ),
      x ∈ᴮ check (PSet.ordinalMk (Order.succ μ).ord)
    exact le_iSup_of_le (check z) (check_mem Hz)
  have Hsurj :
      (injects_into (check (PSet.ordinalMk (Order.succ μ).ord))
        (check (PSet.ordinalMk μ.ord)) : Algebra κ) ≤
      surjects_onto (check (PSet.ordinalMk μ.ord))
        (check (PSet.ordinalMk (Order.succ μ).ord)) :=
    surjects_onto_of_injects_into' le_rfl (le_top.trans Hnonempty)
  rw [checked_successor_surjects_eq_bot κ Hκ μ Hκμ] at Hsurj
  exact bot_unique Hsurj

/-- A displayed predecessor has an actual indexing set of size at most mu.
This direction does not require inaccessibility or a relation to kappa. -/
theorem checked_successor_predecessor_injects (κ μ : Cardinal.{u})
    (i : (Order.succ μ).ord.ToType) :
    (⊤ : Algebra κ) ≤
      injects_into (check (PSet.ordinalMk i.toOrd.val))
        (check (PSet.ordinalMk μ.ord)) := by
  apply ErdosGroundIndexNameBound.injects_checked_cardinal_of_index_cardinal_le
  simpa only [check_type', PSet.ordinalMk_card] using
    (Cardinal.card_le_iff.mpr i.toOrd.property)

/-- The universal predecessor statement covers all second-stage names;
canonical indices occur only in the extensional bounded-forall calculation. -/
theorem checked_successor_members_injects (κ μ : Cardinal.{u}) :
    (⊤ : Algebra κ) ≤
      ⨅ x, _root_.imp
        (x ∈ᴮ check (PSet.ordinalMk (Order.succ μ).ord))
        (injects_into x (check (PSet.ordinalMk μ.ord))) := by
  rw [PSet.ordinalMk_eq_def, check_unfold]
  rw [← bounded_forall (h_congr := B_ext_injects_into_left)]
  change (⊤ : Algebra κ) ≤
    ⨅ i : (Order.succ μ).ord.ToType, _root_.imp ⊤
      (injects_into (check (PSet.ordinalMk i.toOrd.val))
        (check (PSet.ordinalMk μ.ord)))
  apply le_iInf
  intro i
  rw [top_imp]
  exact checked_successor_predecessor_injects κ μ i

/-- The full internal Hartogs property in the concrete two-stage algebra.
No regularity of mu or ground-GCH hypothesis is required. -/
theorem checked_successor_hartogsProperty (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) (μ : Cardinal.{u}) (Hκμ : κ ≤ μ) :
    (⊤ : Algebra κ) ≤
      ErdosHartogs.hartogsProperty (check (PSet.ordinalMk μ.ord))
        (check (PSet.ordinalMk (Order.succ μ).ord)) := by
  refine le_inf (check_Ord (PSet.Ord_mk (Order.succ μ).ord))
    (le_inf ?_ (checked_successor_members_injects κ μ))
  simpa only [checked_successor_injects_base_eq_bot κ Hκ μ Hκμ, compl_bot] using
    (le_rfl : (⊤ : Algebra κ) ≤ ⊤)

end Erdos1172LevyCohen
