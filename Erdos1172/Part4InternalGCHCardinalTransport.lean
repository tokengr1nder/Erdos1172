/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalPowersetInjection
public import Erdos1172.Part4InternalFullGCH

@[expose] public section

/-!
# Full-GCH instances respect internal cardinal equivalence

Both directions of injection are used at the original Boolean condition.
The powerset bound is transported by the actual induced image injection,
not by identifying equinumerous names with Boolean-equal names.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFullGCH

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

theorem hartogsProperty_of_mutual_injections {X Y δ : bSet 𝔹} {Γ : 𝔹}
    (HXY : Γ ≤ injects_into X Y) (HYX : Γ ≤ injects_into Y X)
    (Hδ : Γ ≤ ErdosHartogs.hartogsProperty X δ) :
    Γ ≤ ErdosHartogs.hartogsProperty Y δ := by
  refine le_inf (Hδ.trans inf_le_left) (le_inf ?_ ?_)
  · rw [← imp_bot, ← deduction]
    exact bv_absurd _ (injects_into_trans inf_le_right (inf_le_left.trans HYX))
      (inf_le_left.trans (Hδ.trans (inf_le_right.trans inf_le_left)))
  · apply le_iInf
    intro γ
    rw [← deduction]
    exact injects_into_trans
      (hartogs_predecessor_injects (inf_le_left.trans Hδ) inf_le_right)
      (inf_le_left.trans HXY)

theorem gchAt_of_mutual_injections {X Y : bSet 𝔹} {Γ : 𝔹}
    (HXY : Γ ≤ injects_into X Y) (HYX : Γ ≤ injects_into Y X)
    (HX : Γ ≤ gchAt X) : Γ ≤ gchAt Y := by
  obtain ⟨δ, Hδ⟩ := exists_gchAt_witness HX
  apply gchAt_of_witness (hartogsProperty_of_mutual_injections HXY HYX (Hδ.trans inf_le_left))
  exact injects_into_trans
    (ErdosPowersetInjection.powerset_injects_of_injects HYX)
    (Hδ.trans inf_le_right)

end bSet.ErdosFullGCH
