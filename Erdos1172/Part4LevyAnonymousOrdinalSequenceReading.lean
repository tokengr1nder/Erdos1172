/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyAnonymousCheckedSequenceReading
public import Erdos1172.Part4LevyCohenOrdinalSequenceBound

@[expose] public section

/-!
# Relative anonymous recovery of arbitrary ordinal-valued omega functions

The original graph and codomain may be arbitrary ambient mixed names.
The checked ordinal bound is constructed from their actual numeral values;
it is not supplied as a hypothesis. The resulting Boolean cover retains
supported-function truth in the anonymous algebra at the original context.

This is an exact relative no-new-ordinal-sequences statement. It does not
construct quotient forcing, identify its internal distributivity semantics,
lift an embedding, or construct the required normal dense ideal and final
joint full-GCH model. Inaccessibility is used by the ground-bound argument.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172LevyCohen

open bSet ErdosNameTransport Erdos1172CompleteSubalgebra

/-- Every arbitrary supported ordinal-valued omega function is covered by
actual anonymous function names at its original Boolean condition. -/
theorem anonymous_ordinal_sequence_reading_cover (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible)
    {S f : bSet (Algebra κ)} {Γ : Algebra κ}
    (Hf : Γ ≤ is_function omega S f)
    (HS : Γ ≤ ⨅ x : bSet (Algebra κ), _root_.imp (x ∈ᴮ S) (Ord x)) :
    Γ ≤ ⨆ η : Ordinal.{u}, ⨆ g : bSet (anonymousAlgebra κ),
      inclusion (anonymousAlgebra κ)
          (is_function omega (check (PSet.ordinalMk η)) g) ⊓
        (f =ᴮ mapNames (inclusion (anonymousAlgebra κ)) g) := by
  obtain ⟨η, Hbound⟩ := exists_checked_ordinal_function_bound κ Hκ Hf HS
  exact le_iSup_of_le η
    (anonymous_checked_sequence_reading_cover κ Hκ.isRegular Hκ.aleph0_lt
      (PSet.ordinalMk η) (PSet.ordinalMk_inj η) Hbound)

/-- Only actual function values need be ordinal; irrelevant elements of
the supplied codomain are unrestricted. Factoring through the actual image
keeps the original graph and condition. -/
theorem anonymous_ordinal_valued_function_reading_cover (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible)
    {S f : bSet (Algebra κ)} {Γ : Algebra κ}
    (Hf : Γ ≤ is_function omega S f)
    (Hvalues : Γ ≤ ⨅ i : bSet (Algebra κ), ⨅ x : bSet (Algebra κ),
      _root_.imp (pair i x ∈ᴮ f) (Ord x)) :
    Γ ≤ ⨆ η : Ordinal.{u}, ⨆ g : bSet (anonymousAlgebra κ),
      inclusion (anonymousAlgebra κ)
          (is_function omega (check (PSet.ordinalMk η)) g) ⊓
        (f =ᴮ mapNames (inclusion (anonymousAlgebra κ)) g) := by
  apply anonymous_ordinal_sequence_reading_cover κ Hκ (factor_image_is_function Hf)
  apply le_iInf
  intro x
  rw [← deduction]
  obtain ⟨i, Hi⟩ := exists_convert
    (mem_image_iff.mp (show Γ ⊓ x ∈ᴮ image omega S f ≤
      x ∈ᴮ image omega S f from inf_le_right)).2
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  exact (le_inf
    (inf_le_left.trans (Hvalues.trans ((iInf_le _ i).trans (iInf_le _ x))))
    (Hi.trans inf_le_right)).trans bv_imp_elim

end Erdos1172LevyCohen
