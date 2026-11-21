/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCantor
public import Erdos1172.Part4InternalPowersetPairCoding
public import Erdos1172.Part4InternalProductInjection

@[expose] public section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCardinalSquare

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- Internal CH supplies the omega-one square bound for the concrete Hartogs name.
The route uses all internal subsets of omega, not checked ground-model subsets. -/
theorem omegaOne_square_injects {Γ : 𝔹} (HCH : Γ ≤ (CH : 𝔹)) :
    Γ ≤ injects_into (prod ErdosOmegaTwo.omegaOne ErdosOmegaTwo.omegaOne)
      ErdosOmegaTwo.omegaOne := by
  exact injects_into_trans
    (ErdosProductInjection.injects_into_prod_self
      (ErdosCantor.omegaOne_injects_powerset_omega (Γ := Γ)))
    (injects_into_trans ErdosPowersetPairCoding.powerset_omega_square_injects
      (ErdosCHHartogs.CH_iff_powerset_omega_injects_omegaOne.mp HCH))

end bSet.ErdosCardinalSquare
