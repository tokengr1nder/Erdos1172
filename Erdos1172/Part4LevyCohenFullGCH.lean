/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyCohenPowersetBounds
public import Erdos1172.Part4LevyCohenSuccessorHartogs
public import Erdos1172.Part4LevyCohenNameCardinalRepresentatives
public import Erdos1172.Part4LevyCohenOmegaOne
public import Erdos1172.Part4CheckedOrdinalCardinality
public import Erdos1172.Part4InternalGCHCardinalTransport

@[expose] public section

/-!
# Full internal GCH in the actual Levy--Cohen iteration

The actual dense presentation bounds the two-stage completion and proves
successor noncollapse. Its coefficient bounds and full successor Hartogs
properties establish GCH above checked kappa. Below kappa, transported
countability and the proved second-stage CH suffice. Local mutual-injection
representatives then cover every internally infinite mixed name.

Inaccessibility and host GCH at all cardinals at least kappa remain explicit
hypotheses. This proves full GCH in this concrete two-stage algebra, not in
an ideal-producing final model. No anonymous quotient property, required
normal dense ideal, or joint ideal/GCH consistency witness is constructed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172LevyCohen

open bSet ErdosFullGCH ErdosCheckedOrdinalCardinality ErdosNameTransport

/-- Old small checked ordinals remain countable by positive transport.
No inaccessibility or GCH is required for this direction. -/
theorem checked_ordinal_countable_of_cardinal_lt (κ : Cardinal.{u})
    (η : Ordinal.{u}) (Hcard : η.card < κ) :
    (⊤ : Algebra κ) ≤ injects_into (check (PSet.ordinalMk η)) omega := by
  have HOrd : firstStageHom κ (⊤ : FirstAlgebra κ) ≤
      Ord (mapNames (firstStageHom κ) (omega : bSet (FirstAlgebra κ))) := by
    change firstStageHom κ (⊤ : FirstAlgebra κ) ≤
      Ord (mapNames (firstStageHom κ) (check PSet.omega))
    rw [map_check]
    exact Ord_omega
  have Hmapped := map_injects_into_of_ordinal (firstStageHom κ)
    (Erdos1172LevyCollapse.below_checked_ordinal_countable_of_cardinal_lt κ η Hcard) HOrd
  simpa only [omega, map_check, map_top] using Hmapped

theorem checked_gchAt (κ μ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) (Hκμ : κ ≤ μ)
    (HGCHμ : (2 : Cardinal.{u}) ^ μ = Order.succ μ) :
    (⊤ : Algebra κ) ≤ gchAt (check (PSet.ordinalMk μ.ord)) :=
  gchAt_of_witness
    (checked_successor_hartogsProperty κ Hκ μ Hκμ)
    (checked_powerset_injects_successor κ μ Hκ Hκμ HGCHμ)

theorem gchAt_checked_ordinal (κ : Cardinal.{u}) (Hκ : κ.IsInaccessible)
    (HGCH : ∀ μ : Cardinal.{u}, κ ≤ μ → (2 : Cardinal.{u}) ^ μ = Order.succ μ)
    (η : Ordinal.{u}) {Γ : Algebra κ}
    (Hinf : Γ ≤ injects_into omega (check (PSet.ordinalMk η))) :
    Γ ≤ gchAt (check (PSet.ordinalMk η)) := by
  by_cases Hsmall : η.card < κ
  · apply gchAt_of_mutual_injections Hinf
      (le_top.trans (checked_ordinal_countable_of_cardinal_lt κ η Hsmall))
    rw [gchAt_omega_eq_CH]
    exact le_top.trans (forces_CH κ Hκ)
  · have Hκμ : κ ≤ η.card := le_of_not_gt Hsmall
    exact gchAt_of_mutual_injections
      (le_top.trans (checked_cardinal_injects_ordinal η))
      (le_top.trans (checked_ordinal_injects_cardinal η))
      (le_top.trans (checked_gchAt κ η.card Hκ Hκμ (HGCH η.card Hκμ)))

/-- The full universal quantifier ranges over arbitrary infinite names.
Ground representatives are chosen only on Boolean pieces of a cover. -/
theorem forces_fullGCH (κ : Cardinal.{u}) (Hκ : κ.IsInaccessible)
    (HGCH : ∀ μ : Cardinal.{u}, κ ≤ μ → (2 : Cardinal.{u}) ^ μ = Order.succ μ) :
    (⊤ : Algebra κ) ≤ fullGCHValue := by
  apply le_iInf
  intro S
  rw [← deduction]
  have Hrep := name_mutual_checked_ordinal κ Hκ S
  apply (le_inf (le_refl (⊤ ⊓ injects_into omega S)) (le_top.trans Hrep)).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro η
  have HSord : (⊤ ⊓ injects_into omega S) ⊓
      (injects_into S (check (PSet.ordinalMk η)) ⊓
        injects_into (check (PSet.ordinalMk η)) S) ≤
      injects_into S (check (PSet.ordinalMk η)) := inf_le_right.trans inf_le_left
  have HordS : (⊤ ⊓ injects_into omega S) ⊓
      (injects_into S (check (PSet.ordinalMk η)) ⊓
        injects_into (check (PSet.ordinalMk η)) S) ≤
      injects_into (check (PSet.ordinalMk η)) S := inf_le_right.trans inf_le_right
  exact gchAt_of_mutual_injections HordS HSord
    (gchAt_checked_ordinal κ Hκ HGCH η
      (injects_into_trans (inf_le_left.trans inf_le_right) HSord))

end Erdos1172LevyCohen
