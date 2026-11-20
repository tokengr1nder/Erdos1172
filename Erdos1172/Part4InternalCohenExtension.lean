/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCohenConditions
public import Erdos1172.Part4InternalCountableSuccessor
public import Erdos1172.Part4InternalFullGCH

@[expose] public section

/-!
# Actual one-coordinate extensions of internal Cohen conditions

For the internal first uncountable ordinal, small domains are countable.
Adjoining a fresh binary assignment preserves this property, using an
actual insertion bound on the graph domain. All hypotheses and conclusions
hold at the same Boolean condition, for arbitrary mixed names.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCohen

open ErdosPartialInjection ErdosInjectionExtension

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

theorem smallDomain_of_countable {K p : bSet 𝔹} {Γ : 𝔹}
    (Hω : Γ ≤ omega ∈ᴮ K)
    (Hcount : Γ ≤ injects_into (graphDomain K two p) omega) :
    Γ ≤ smallDomain K p :=
  le_iSup_of_le omega (le_inf Hω Hcount)

theorem countable_of_smallDomain {K p : bSet 𝔹} {Γ : 𝔹}
    (HK : Γ ≤ ErdosHartogs.hartogsProperty omega K)
    (Hp : Γ ≤ smallDomain K p) :
    Γ ≤ injects_into (graphDomain K two p) omega := by
  apply (le_inf le_rfl Hp).trans
  rw [smallDomain, inf_iSup_eq]
  apply iSup_le
  intro δ
  exact injects_into_trans (inf_le_right.trans inf_le_right)
    (ErdosFullGCH.hartogs_predecessor_injects (inf_le_left.trans HK)
      (inf_le_right.trans inf_le_left))

theorem omega_mem_of_hartogsProperty {K : bSet 𝔹} {Γ : 𝔹}
    (HK : Γ ≤ ErdosHartogs.hartogsProperty omega K) : Γ ≤ omega ∈ᴮ K :=
  mem_congr bv_refl (bv_symm (ErdosOmegaTwo.omegaOne_property_unique HK))
    ErdosOmegaTwo.omega_mem_omegaOne

end bSet.ErdosCohen
