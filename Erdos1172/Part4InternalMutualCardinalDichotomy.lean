/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCardinalDichotomy

@[expose] public section

/-!
# Cardinal comparison retaining both injections in the smaller branch

An actual maximal partial injection from an ordinal into an arbitrary name
either has full domain or covers the entire target from a strict ordinal
predecessor. In the latter case we retain the constructed forward injection
as well as the inverse injection. The alternatives are a Boolean join at the
original condition, not an externally chosen alternative or ground ordinal.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosPartialInjection

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- Every internal name either admits an injection of the given ordinal,
or has mutual injections with one of its strict predecessors. -/
theorem ordinal_mutual_cardinal_dichotomy {κ S : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ) :
    Γ ≤ injects_into κ S ⊔
      ⨆ A, (A ∈ᴮ κ) ⊓ (injects_into S A ⊓ injects_into A S) := by
  have Hmax := exists_maximal_partialGraph (κ := κ) (S := S) (Γ := Γ)
  apply (le_inf (le_refl Γ) Hmax).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro f
  let Δ := Γ ⊓ (partialGraph κ S f ⊓
    ⨅ g, _root_.imp (partialGraph κ S g) (_root_.imp (f ⊆ᴮ g) (f =ᴮ g)))
  have Hf : Δ ≤ partialGraph κ S f := inf_le_right.trans inf_le_left
  have Hmaxf : Δ ≤ ⨅ g, _root_.imp (partialGraph κ S g)
      (_root_.imp (f ⊆ᴮ g) (f =ᴮ g)) := inf_le_right.trans inf_le_right
  let A := graphDomain κ S f
  have HA : Δ ≤ Ord A := partialGraph_domain_Ord (inf_le_left.trans Hκ) Hf
  have Hfunc : Δ ≤ is_injective_function A S f := partialGraph_function Hf
  have Hcase : Δ ≤ A =ᴮ κ ⊔ A ∈ᴮ κ :=
    ErdosInitialSegments.eq_or_mem_of_ordinal_subset HA (inf_le_left.trans Hκ)
      graphDomain_subset
  apply (le_inf (le_refl Δ) Hcase).trans
  rw [inf_sup_left]
  apply sup_le
  · apply le_sup_of_le_left
    have Hinj : Δ ⊓ A =ᴮ κ ≤ injects_into A S :=
      injects_into_of_injection_into
        (le_iSup_of_le f (inf_le_left.trans Hfunc))
    exact bv_rw'' (ϕ := fun X => injects_into X S) inf_le_right Hinj
      B_ext_injects_into_left
  · apply le_sup_of_le_right
    apply le_iSup_of_le A
    refine le_inf inf_le_right (le_inf ?_ ?_)
    · exact injection_back_of_range_covers (inf_le_left.trans Hfunc)
        (maximal_range_covers_of_domain_mem
          (inf_le_left.trans (inf_le_left.trans Hκ))
          (inf_le_left.trans Hf) (inf_le_left.trans Hmaxf) inf_le_right)
    · exact injects_into_of_injection_into
        (le_iSup_of_le f (inf_le_left.trans Hfunc))

end bSet.ErdosPartialInjection
