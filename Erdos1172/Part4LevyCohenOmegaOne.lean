/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4CohenPowersetPreservation
public import Erdos1172.Part4BooleanSurjectionTransport
public import Erdos1172.Part4LevyCohenIteration
public import Erdos1172.Part4LevyContinuumHypothesis
public import Erdos1172.Part4InternalCantor

@[expose] public section

/-!
# Omega-one and CH in the actual Levy--Cohen iteration

Real reading identifies the transported first-stage powerset of omega with
the full second-stage powerset. The first-stage continuum injection into
checked kappa therefore remains an injection of the full powerset. Cantor's
diagonal prevents checked kappa from becoming countable. Each checked
predecessor remains countable by actual ordinal-target injection transport;
bounded quantification then covers every mixed predecessor name.

The complete Hartogs property identifies checked kappa with the SECOND-stage
internal omega-one. The same powerset injection proves CH there. The only
external cardinal hypothesis is inaccessibility of kappa: ground full GCH,
preservation of higher cardinals, and existence of an ideal are not assumed
or concluded.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172LevyCohen

open bSet bSet.ErdosNameTransport

/-- Real reading upgrades the transported old continuum injection to an
injection of the entire second-stage powerset, including mixed real names. -/
theorem powerset_omega_injects_checked_upper (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) :
    (⊤ : Algebra κ) ≤
      injects_into (bv_powerset omega) (check (PSet.ordinalMk κ.ord)) := by
  have HOrd : firstStageHom κ (⊤ : FirstAlgebra κ) ≤
      Ord (mapNames (firstStageHom κ)
        (check (PSet.ordinalMk κ.ord) : bSet (FirstAlgebra κ))) := by
    rw [map_check]
    exact check_Ord (PSet.Ord_mk κ.ord)
  have Hmapped := map_injects_into_of_ordinal (firstStageHom κ)
    (Erdos1172LevyCollapse.below_powerset_omega_injects_checked_upper κ Hκ) HOrd
  rw [map_top, map_check] at Hmapped
  have Hpowerset : (⊤ : Algebra κ) ≤
      mapNames (firstStageHom κ) (bv_powerset (omega : bSet (FirstAlgebra κ))) =ᴮ
        bv_powerset (omega : bSet (Algebra κ)) :=
    Erdos1172CohenIteration.map_powerset_omega_eq
  exact bv_rw'' Hpowerset Hmapped B_ext_injects_into_left

/-- Counting checked kappa would count the full internal powerset of omega,
contradicting the already proved internal Cantor diagonal. -/
theorem checked_upper_not_countable (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) {Γ : Algebra κ} :
    Γ ≤ (injects_into (check (PSet.ordinalMk κ.ord)) (omega : bSet (Algebra κ)))ᶜ := by
  rw [← imp_bot, ← deduction]
  exact bv_absurd _
    (injects_into_trans (le_top.trans (powerset_omega_injects_checked_upper κ Hκ))
      inf_le_right) ErdosCantor.powerset_not_injects

/-- An old countable checked predecessor remains countable in the iteration.
This uses positive transport, not preservation of an unbounded formula. -/
theorem checked_predecessor_countable (κ : Cardinal.{u}) (i : κ.ord.ToType) :
    (⊤ : Algebra κ) ≤
      injects_into (check (PSet.ordinalMk i.toOrd.val)) (omega : bSet (Algebra κ)) := by
  have HOrd : firstStageHom κ (⊤ : FirstAlgebra κ) ≤
      Ord (mapNames (firstStageHom κ) (omega : bSet (FirstAlgebra κ))) := by
    change firstStageHom κ (⊤ : FirstAlgebra κ) ≤
      Ord (mapNames (firstStageHom κ) (check PSet.omega))
    rw [map_check]
    exact Ord_omega
  have Hmapped := map_injects_into_of_ordinal (firstStageHom κ)
    (Erdos1172LevyCollapse.checked_predecessor_countable κ i) HOrd
  simpa only [omega, map_check, map_top] using Hmapped

/-- The predecessor quantifier ranges over all second-stage names. The
canonical checked indices are used only inside extensional bounded forall. -/
theorem checked_members_countable (κ : Cardinal.{u}) :
    (⊤ : Algebra κ) ≤
      ⨅ x, _root_.imp (x ∈ᴮ check (PSet.ordinalMk κ.ord))
        (injects_into x (omega : bSet (Algebra κ))) := by
  rw [PSet.ordinalMk_eq_def, check_unfold]
  rw [← bounded_forall (h_congr := B_ext_injects_into_left)]
  change (⊤ : Algebra κ) ≤
    ⨅ i : κ.ord.ToType, _root_.imp ⊤
      (injects_into (check (PSet.ordinalMk i.toOrd.val)) omega)
  apply le_iInf
  intro i
  rw [top_imp]
  exact checked_predecessor_countable κ i

/-- Checked kappa satisfies the full second-stage Hartogs specification. -/
theorem checked_upper_hartogsProperty (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) :
    (⊤ : Algebra κ) ≤
      ErdosHartogs.hartogsProperty omega (check (PSet.ordinalMk κ.ord)) :=
  le_inf (check_Ord (PSet.Ord_mk κ.ord))
    (le_inf (checked_upper_not_countable κ Hκ) (checked_members_countable κ))

/-- This equality is in the completed two-stage algebra, not merely the
first-stage collapse algebra. -/
theorem checked_upper_eq_omegaOne (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) :
    (⊤ : Algebra κ) ≤
      check (PSet.ordinalMk κ.ord) =ᴮ ErdosOmegaTwo.omegaOne :=
  ErdosOmegaTwo.omegaOne_property_unique (checked_upper_hartogsProperty κ Hκ)

/-- CH in the actual two-stage algebra follows without ground full GCH. -/
theorem forces_CH (κ : Cardinal.{u}) (Hκ : κ.IsInaccessible) :
    (⊤ : Algebra κ) ≤ CH := by
  apply ErdosCHHartogs.CH_iff_powerset_omega_injects_omegaOne.mpr
  exact bv_rw'' (checked_upper_eq_omegaOne κ Hκ)
    (powerset_omega_injects_checked_upper κ Hκ) B_ext_injects_into_right

end Erdos1172LevyCohen
