/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyAnonymousOmegaOne
public import Erdos1172.Part4LevyCohenSuccessorHartogs
public import Erdos1172.Part4InternalMutualCardinalDichotomy

@[expose] public section

/-!
# The continuum hypothesis in the anonymous collapse

If the target of a complete embedding preserves a checked successor, an
ambient bound by its predecessor descends to the source. A source injection
from the successor would supply an ambient partial surjection onto it. The
ambient bound and ordinal choice would then collapse the successor. The
source's ordinal comparison therefore bounds the original set by a checked
predecessor on a Boolean cover. Apply this to the full powerset of omega.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosNameTransport

variable {B C : Type u} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

/-- A cardinal bound in the extension descends at the original condition,
provided that the extension preserves the indicated strict successor gap. -/
theorem descend_checked_cardinal_bound (e : CompleteLatticeHom B C) (he : Function.Injective e)
    (μ : Cardinal.{u}) (S : bSet B) {Γ : B}
    (Hnoncollapse : (injects_into (check (PSet.ordinalMk (Order.succ μ).ord))
      (check (PSet.ordinalMk μ.ord)) : C) = ⊥)
    (Hbound : e Γ ≤ injects_into (mapNames e S) (check (PSet.ordinalMk μ.ord))) :
    Γ ≤ injects_into S (check (PSet.ordinalMk μ.ord)) := by
  let Δ := Γ ⊓ injects_into (check (PSet.ordinalMk (Order.succ μ).ord)) S
  have Hlarge := map_larger_than_of e
    (ErdosCHHartogs.larger_than_of_injects_into
      (show Δ ≤ injects_into (check (PSet.ordinalMk (Order.succ μ).ord)) S from inf_le_right))
  rw [map_check] at Hlarge
  have Hlarger := ErdosCountableImage.larger_than_of_injects_into_of_larger_than
    ((OrderHomClass.mono e (show Δ ≤ Γ from inf_le_left)).trans Hbound) Hlarge
  have Hbad := ErdosCHHartogs.injects_into_of_larger_than_ordinal
    (check_Ord (PSet.Ord_mk μ.ord)) Hlarger
  have Hz : Δ = ⊥ := he ((bot_unique (Hbad.trans_eq Hnoncollapse)).trans (map_bot e).symm)
  have Hcase := ErdosPartialInjection.ordinal_mutual_cardinal_dichotomy
    (S := S) (Γ := Γ) (check_Ord (PSet.Ord_mk (Order.succ μ).ord))
  have Hcut := le_inf (le_refl Γ) Hcase
  rw [inf_sup_left, (show Γ ⊓ _ = ⊥ from Hz), bot_sup_eq] at Hcut
  apply (Hcut.trans inf_le_right).trans
  rw [← bounded_exists (h_congr :=
    B_ext_inf (B_ext_injects_into_right (y := S)) (B_ext_injects_into_left (y := S)))]
  rw [PSet.ordinalMk_eq_def (Order.succ μ).ord, check_unfold]
  change (⨆ i : (Order.succ μ).ord.ToType, ⊤ ⊓
    (injects_into S (check (PSet.ordinalMk i.toOrd.val)) ⊓
      injects_into (check (PSet.ordinalMk i.toOrd.val)) S)) ≤ _
  apply iSup_le
  intro i
  have Hp : (⊤ : B) ≤ injects_into (check (PSet.ordinalMk i.toOrd.val))
      (check (PSet.ordinalMk μ.ord)) := by
    apply ErdosGroundIndexNameBound.injects_checked_cardinal_of_index_cardinal_le
    simpa only [check_type', PSet.ordinalMk_card] using (Cardinal.card_le_iff.mpr i.toOrd.property)
  exact injects_into_trans (inf_le_right.trans inf_le_left) (le_top.trans Hp)

end bSet.ErdosNameTransport

namespace Erdos1172LevyCohen

open bSet ErdosNameTransport Erdos1172CompleteSubalgebra

theorem anonymous_injects_checked_of_ambient (κ : Cardinal.{u}) (Hκ : κ.IsInaccessible)
    (μ : Cardinal.{u}) (Hκμ : κ ≤ μ) (S : bSet (anonymousAlgebra κ))
    (Hbound : (⊤ : Algebra κ) ≤ injects_into (mapNames (inclusion (anonymousAlgebra κ)) S)
      (check (PSet.ordinalMk μ.ord))) :
    (⊤ : anonymousAlgebra κ) ≤ injects_into S (check (PSet.ordinalMk μ.ord)) :=
  descend_checked_cardinal_bound (inclusion (anonymousAlgebra κ)) (inclusion_injective _) μ S
    (checked_successor_injects_base_eq_bot κ Hκ μ Hκμ) (le_top.trans Hbound)

theorem anonymous_powerset_omega_injects_checked_upper (κ : Cardinal.{u}) (Hκ : κ.IsInaccessible) :
    (⊤ : anonymousAlgebra κ) ≤ injects_into (bv_powerset omega) (check (PSet.ordinalMk κ.ord)) := by
  apply anonymous_injects_checked_of_ambient κ Hκ κ le_rfl
  have Hsub := map_powerset_subset (inclusion (anonymousAlgebra κ))
    (omega : bSet (anonymousAlgebra κ))
  simp only [omega, map_check] at Hsub
  exact injects_into_trans (injects_into_of_subset Hsub) (powerset_omega_injects_checked_upper κ Hκ)

end Erdos1172LevyCohen
