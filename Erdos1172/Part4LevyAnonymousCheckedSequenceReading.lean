/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyAnonymousSmallSubsetReading
public import Erdos1172.Part4LevyCohenCheckedSequenceCapture

@[expose] public section

/-!
# Anonymous recovery of supported sequences in a fixed checked ground set

The actual first-stage reading cover captures each source function's range
inside a ground subfamily with index cardinal below kappa. Its entire graph
is therefore supported on a small checked ground product. The constructed
small-subset reading cover recovers that graph through the anonymous algebra.

Exact transport of supported-function truth, not unbounded elementarity,
recovers the function validity guard. The codomain is enlarged back to the
original checked ground set. Both witness covers are distributed locally
under the original Boolean condition; no one global representative is chosen.

This is recovery for every fixed separated checked ground codomain. It does
not assert a ground bound for arbitrary unbounded ordinal names, blanket
elementarity, or an ideal/model construction.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172LevyCohen

open bSet ErdosNameTransport Erdos1172CompleteSubalgebra

/-- Arbitrary ambient supported omega-to-check-A functions are covered by
actual anonymous function names, retaining validity for the original A. -/
theorem anonymous_checked_sequence_reading_cover (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ)
    (A : PSet.{u})
    (Hsep : ∀ i j : A.Type, i ≠ j → ¬ PSet.Equiv (A.Func i) (A.Func j))
    {f : bSet (Algebra κ)} {Γ : Algebra κ}
    (Hf : Γ ≤ is_function omega (check A) f) :
    Γ ≤ ⨆ h : bSet (anonymousAlgebra κ),
      inclusion (anonymousAlgebra κ) (is_function omega (check A) h) ⊓
        (f =ᴮ mapNames (inclusion (anonymousAlgebra κ)) h) := by
  apply (checked_sequence_small_ground_capture_cover κ Hκ Hunc A Hsep Hf).trans
  apply iSup_le
  intro A₀
  apply iSup_le
  intro g
  have Hproduct : Cardinal.mk (PSet.pSet_prod PSet.omega A₀.val).Type < κ := by
    change Cardinal.mk (ULift.{u} ℕ × A₀.val.Type) < κ
    rw [Cardinal.mk_prod, mul_comm]
    simpa only [Cardinal.mk_prod] using small_times_nat_cardinal_lt κ Hunc A₀.val.Type A₀.property.1
  have Hsupport : is_function omega (check A₀.val) g ≤
      g ⊆ᴮ check (PSet.pSet_prod PSet.omega A₀.val) :=
    subset_trans' (subset_prod_of_is_function le_rfl)
      (subset_of_eq (bv_symm (check_pset_prod (x := PSet.omega) (y := A₀.val))))
  have HsubsetCover : firstStageHom κ (is_function omega (check A₀.val) g) ≤
      ⨆ h : bSet (anonymousAlgebra κ),
        inclusion (anonymousAlgebra κ)
            (h ⊆ᴮ check (PSet.pSet_prod PSet.omega A₀.val)) ⊓
          (mapNames (firstStageHom κ) g =ᴮ mapNames (inclusion (anonymousAlgebra κ)) h) :=
    (OrderHomClass.mono (firstStageHom κ) Hsupport).trans
      (firstStage_small_subset_anonymous_cover κ Hκ Hunc
        (PSet.pSet_prod PSet.omega A₀.val) Hproduct g)
  have Hmapped : firstStageHom κ (is_function omega (check A₀.val) g) ≤
      is_function omega (check A₀.val) (mapNames (firstStageHom κ) g) := by
    simpa only [omega, map_check] using
      (map_is_function (firstStageHom κ) omega (check A₀.val) g).le
  apply (le_inf le_rfl (inf_le_left.trans HsubsetCover)).trans
  erw [inf_iSup_eq]
  apply iSup_le
  intro h
  apply le_iSup_of_le h
  have Hfunction :
      (firstStageHom κ (is_function omega (check A₀.val) g) ⊓
          (f =ᴮ mapNames (firstStageHom κ) g)) ⊓
        (inclusion (anonymousAlgebra κ)
            (h ⊆ᴮ check (PSet.pSet_prod PSet.omega A₀.val)) ⊓
          (mapNames (firstStageHom κ) g =ᴮ mapNames (inclusion (anonymousAlgebra κ)) h)) ≤
      is_function omega (check A₀.val) (mapNames (inclusion (anonymousAlgebra κ)) h) :=
    bv_rw' (bv_symm (inf_le_right.trans inf_le_right))
      (h_congr := B_ext_is_function_right)
      (H_new := (inf_le_left.trans inf_le_left).trans Hmapped)
  have Horiginal := ErdosIndependentHomogeneous.is_function_codomain_mono
    (check_subset A₀.property.2) Hfunction
  refine le_inf ?_ (bv_trans (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
  have Htransport : inclusion (anonymousAlgebra κ) (is_function omega (check A) h) =
      is_function omega (check A) (mapNames (inclusion (anonymousAlgebra κ)) h) := by
    rw [map_is_function]
    simp only [omega, map_check]
  exact Horiginal.trans_eq Htransport.symm

end Erdos1172LevyCohen
