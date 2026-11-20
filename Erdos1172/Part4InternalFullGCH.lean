/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalHartogsUniqueness
public import Erdos1172.Part4InternalCantor

@[expose] public section

/-!
# Full internal GCH using existential Hartogs witnesses

The base ranges over arbitrary Boolean-valued names. The witness is specified
at the current Boolean condition; no globally nonempty representative is
required in order to invoke a globally chosen Hartogs construction.

The cardinal lemmas below prove initiality, comparison with the base, and the
reverse powerset injection from the Hartogs specification itself. Thus the
GCH upper bound supplies mutual injections with the successor initial
ordinal. The infinitude guard is `omega` injecting into the base; in the
ambient internal ZFC model this ranges over all infinite cardinalities.
These are semantic definitions and implications, not a construction of a
model satisfying full GCH.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFullGCH

open ErdosHartogs ErdosOmegaTwo

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- The GCH upper bound at an arbitrary base, with its exact Hartogs witness. -/
def gchAt (κ : bSet 𝔹) : 𝔹 :=
  ⨆ δ, hartogsProperty κ δ ⊓ injects_into (bv_powerset κ) δ

/-- Full GCH, over all internally infinite names rather than checked names. -/
def fullGCHValue : 𝔹 :=
  ⨅ κ, _root_.imp (injects_into bSet.omega κ) (gchAt κ)

theorem hartogsProperty_ext_witness (κ : bSet 𝔹) :
    B_ext (hartogsProperty κ) :=
  B_ext_inf B_ext_Ord
    (B_ext_inf (B_ext_neg (h := B_ext_injects_into_left))
      (B_ext_iInf (h := fun _ =>
        B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const))))

theorem gchAt_witness_ext (κ : bSet 𝔹) :
    B_ext (fun δ => hartogsProperty κ δ ⊓ injects_into (bv_powerset κ) δ) :=
  B_ext_inf (hartogsProperty_ext_witness κ) B_ext_injects_into_right

theorem gchAt_of_witness {κ δ : bSet 𝔹} {Γ : 𝔹}
    (Hδ : Γ ≤ hartogsProperty κ δ)
    (Hpower : Γ ≤ injects_into (bv_powerset κ) δ) : Γ ≤ gchAt κ :=
  le_iSup_of_le δ (le_inf Hδ Hpower)

/-- Fullness selects the entire Hartogs/GCH witness at the same condition. -/
theorem exists_gchAt_witness {κ : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ gchAt κ) :
    ∃ δ, Γ ≤ hartogsProperty κ δ ⊓ injects_into (bv_powerset κ) δ :=
  exists_convert H (gchAt_witness_ext κ)

theorem gchAt_apply {κ : bSet 𝔹} {Γ : 𝔹}
    (HGCH : Γ ≤ (fullGCHValue : 𝔹))
    (Hκ : Γ ≤ injects_into bSet.omega κ) : Γ ≤ gchAt κ :=
  (le_inf (HGCH.trans (iInf_le _ κ)) Hκ).trans bv_imp_elim

/-- The first instance is exactly the previously verified internal CH value. -/
theorem gchAt_omega_eq_CH : gchAt (bSet.omega : bSet 𝔹) = CH := by
  apply le_antisymm
  · apply iSup_le
    intro δ
    apply ErdosCHHartogs.CH_iff_powerset_omega_injects_omegaOne.mpr
    exact bv_rw'' (ϕ := fun α => injects_into (bv_powerset bSet.omega) α)
      (omegaOne_property_unique inf_le_left) inf_le_right
      B_ext_injects_into_right
  · exact gchAt_of_witness omegaOne_property
      (ErdosCHHartogs.CH_iff_powerset_omega_injects_omegaOne.mp le_rfl)

theorem CH_of_fullGCH {Γ : 𝔹} (H : Γ ≤ (fullGCHValue : 𝔹)) : Γ ≤ CH := by
  rw [← gchAt_omega_eq_CH]
  exact gchAt_apply H injects_into_refl

theorem hartogs_predecessor_injects {κ δ γ : bSet 𝔹} {Γ : 𝔹}
    (Hδ : Γ ≤ hartogsProperty κ δ) (Hγ : Γ ≤ γ ∈ᴮ δ) :
    Γ ≤ injects_into γ κ :=
  (le_inf (Hδ.trans (inf_le_right.trans (inf_le_right.trans (iInf_le _ γ))))
    Hγ).trans bv_imp_elim

end bSet.ErdosFullGCH
