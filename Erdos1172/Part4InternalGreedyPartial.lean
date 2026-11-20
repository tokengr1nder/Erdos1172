/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalRowCandidateCongruence

@[expose] public section

/-!
The actual set of partial greedy graphs on internal omega-one. Each used
coordinate is assigned the least member of its exact row-candidate set,
computed from the same graph. Separation inside the existing partial-map
family retains support, injectivity and an initial-segment domain.
No successful run, ideal assumptions, or totality on omega-one is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosGreedyPartial

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartialInjection ErdosRowCandidates ErdosOrdinalLeast

def greedyLaw (seed F f : bSet 𝔹) : 𝔹 :=
  ⨅ i, ⨅ x, _root_.imp (pair i x ∈ᴮ f) (leastIn (rowCandidates i seed F f) x)

theorem greedyLaw_apply {seed F f i x : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ greedyLaw seed F f) (Hpair : Γ ≤ pair i x ∈ᴮ f) :
    Γ ≤ leastIn (rowCandidates i seed F f) x :=
  (le_inf (H.trans ((iInf_le _ i).trans (iInf_le _ x))) Hpair).trans bv_imp_elim

end bSet.ErdosGreedyPartial
