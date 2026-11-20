/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.OrdinalUnaryIndivisibility

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3BHTExactBlueColumns

open Erdos1172Part3Failure Erdos1172Part3OneSuccessorBarrier Erdos1172OrdinalUnaryIndivisibility

/-- `RedCoreTarget = omegaOne ^ (omega + 2)` is literally a nonzero
power of `omega`.  The exponent is left existential: only its
omega-power form, not a chosen logarithm of `omegaOne`, is used below. -/
theorem exists_redCoreTarget_eq_omega_opow :
    ∃ e : Ordinal, RedCoreTarget = ω ^ e := by
  have honePrincipal : IsPrincipal (· + ·) (omega 1) :=
    Ordinal.isPrincipal_add_omega 1
  rcases Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.mp
      honePrincipal with honeZero | ⟨e, he⟩
  · have honePos : (0 : Ordinal) < omega 1 :=
      Ordinal.omega0_pos.trans_le (Ordinal.omega0_le_omega 1)
    exact (honePos.ne' honeZero).elim
  · refine ⟨e * (ω + 2), ?_⟩
    rw [RedCoreTarget, ← he, Ordinal.opow_mul]

end Erdos1172Part3BHTExactBlueColumns
