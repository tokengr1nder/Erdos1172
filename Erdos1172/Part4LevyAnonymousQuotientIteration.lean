/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanQuotientFactorization
public import Erdos1172.Part4BooleanIsoNameTransport
public import Erdos1172.Part4LevyAnonymousOrdinalSequenceReading
public import Erdos1172.Part4LevyCohenFullGCH

@[expose] public section

/-! # The Levy–Cohen forcing as an iteration over its anonymous subalgebra

The quotient is the Boolean name whose checked conditions have coefficients
given by lower projection. The factorization identifies the completed
iteration with the original forcing, preserving its first-stage map. Hence
every ordinal-valued countable sequence in the iteration can be read locally
from a name in the first stage.
-/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
universe u

namespace Erdos1172LevyCohen

open bSet ErdosNameTransport Erdos1172BooleanQuotient Erdos1172CompleteSubalgebra

def anonymousQuotient (κ : Cardinal.{u}) : bSet (anonymousAlgebra κ) :=
  quotientName (inclusion (anonymousAlgebra κ))

abbrev QuotientIteration (κ : Cardinal.{u}) :=
  Erdos1172BooleanNameIteration.Algebra (anonymousQuotient κ)

instance quotientIterationNCBA (κ : Cardinal.{u}) :
    NontrivialCompleteBooleanAlgebra (QuotientIteration κ) :=
  quotientAlgebraNontrivial (inclusion (anonymousAlgebra κ))

def anonymousFactorIso (κ : Cardinal.{u}) : Algebra κ ≃o QuotientIteration κ :=
  factorization (inclusion (anonymousAlgebra κ))

def anonymousFirstStage (κ : Cardinal.{u}) :
    CompleteLatticeHom (anonymousAlgebra κ) (QuotientIteration κ) :=
  firstStage (inclusion (anonymousAlgebra κ))

theorem anonymousFactorIso_comp (κ : Cardinal.{u}) :
    (isoHom (anonymousFactorIso κ)).comp (inclusion (anonymousAlgebra κ)) =
      anonymousFirstStage κ := factorization_comp _

private theorem transfer_ordinal_reading
    {B C D : Type u} [NontrivialCompleteBooleanAlgebra B]
    [NontrivialCompleteBooleanAlgebra C] [NontrivialCompleteBooleanAlgebra D]
    (e : CompleteLatticeHom B C) (φ : C ≃o D)
    (hread : ∀ {S f : bSet C} {Γ : C}, Γ ≤ is_function omega S f →
      Γ ≤ ⨅ i : bSet C, ⨅ x : bSet C, _root_.imp (pair i x ∈ᴮ f) (Ord x) →
      Γ ≤ ⨆ η : Ordinal.{u}, ⨆ g : bSet B, e (is_function omega (check (PSet.ordinalMk η)) g) ⊓
        (f =ᴮ mapNames e g))
    {S f : bSet D} {Γ : D}
    (Hf : Γ ≤ is_function omega S f)
    (Hvalues : Γ ≤ ⨅ i : bSet D, ⨅ x : bSet D,
      _root_.imp (pair i x ∈ᴮ f) (Ord x)) :
    Γ ≤ ⨆ η : Ordinal.{u}, ⨆ g : bSet B,
      ((isoHom φ).comp e) (is_function omega (check (PSet.ordinalMk η)) g) ⊓
        (f =ᴮ mapNames ((isoHom φ).comp e) g) := by
  let f' := mapNames (isoHom φ.symm) f
  let S' := mapNames (isoHom φ.symm) S
  have hf' : isoHom φ.symm Γ ≤ is_function omega S' f' := by
    simpa only [map_is_function, omega, map_check, S', f'] using
      (OrderHomClass.mono (isoHom φ.symm) Hf)
  have hv' : isoHom φ.symm Γ ≤ ⨅ i : bSet C, ⨅ x : bSet C,
      _root_.imp (pair i x ∈ᴮ f') (Ord x) := by
    simpa only [map_iso_iInf, map_imp, map_mem, map_pair, map_iso_Ord,
      mapNames_iso_rightInverse, f'] using (OrderHomClass.mono (isoHom φ.symm) Hvalues)
  have h := OrderHomClass.mono (isoHom φ) (hread hf' hv')
  have hf_back : mapNames (isoHom φ) f' = f := mapNames_iso_rightInverse φ f
  change φ (φ.symm Γ) ≤ _ at h
  rw [φ.apply_symm_apply] at h
  change Γ ≤ isoHom φ _ at h
  simpa only [map_iSup, map_inf, map_bv_eq, hf_back, ← mapNames_comp,
    CompleteLatticeHom.comp_apply] using h

theorem quotientIteration_ordinal_reading (κ : Cardinal.{u}) (Hκ : κ.IsInaccessible)
    {S f : bSet (QuotientIteration κ)} {Γ : QuotientIteration κ}
    (Hf : Γ ≤ is_function omega S f)
    (Hvalues : Γ ≤ ⨅ i : bSet (QuotientIteration κ), ⨅ x : bSet (QuotientIteration κ),
      _root_.imp (pair i x ∈ᴮ f) (Ord x)) :
    Γ ≤ ⨆ η : Ordinal.{u}, ⨆ g : bSet (anonymousAlgebra κ),
      anonymousFirstStage κ (is_function omega (check (PSet.ordinalMk η)) g) ⊓
        (f =ᴮ mapNames (anonymousFirstStage κ) g) := by
  rw [← anonymousFactorIso_comp]
  exact transfer_ordinal_reading _ _ (anonymous_ordinal_valued_function_reading_cover κ Hκ)
    Hf Hvalues

private theorem fullGCH_of_iso {C D : Type u} [NontrivialCompleteBooleanAlgebra C]
    [NontrivialCompleteBooleanAlgebra D] (φ : C ≃o D)
    (h : (⊤ : C) ≤ ErdosFullGCH.fullGCHValue) : (⊤ : D) ≤ ErdosFullGCH.fullGCHValue := by
  simpa only [map_top, map_iso_fullGCHValue] using OrderHomClass.mono (isoHom φ) h

theorem quotientIteration_forces_fullGCH (κ : Cardinal.{u}) (Hκ : κ.IsInaccessible)
    (HGCH : ∀ μ : Cardinal.{u}, κ ≤ μ → (2 : Cardinal.{u}) ^ μ = Order.succ μ) :
    (⊤ : QuotientIteration κ) ≤ ErdosFullGCH.fullGCHValue :=
  fullGCH_of_iso (anonymousFactorIso κ) (forces_fullGCH κ Hκ HGCH)

end Erdos1172LevyCohen
