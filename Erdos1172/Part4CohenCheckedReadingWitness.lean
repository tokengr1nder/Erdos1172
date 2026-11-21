/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4CohenCoverFusion
public import Erdos1172.Part4CohenReadingBridge
public import Erdos1172.Part4BooleanNameTransport

@[expose] public section

/-!
# An actual first-stage witness for a checked-value reading cover

Fullness selects a first-stage mixed name from the whole reading cover,
not a ground label. It belongs to the checked set at the original value
of the condition. Transporting every reading piece gives equality with
the arbitrary ambient name on the entire completed condition.

The ambient algebra is the concrete omega-one iteration with its fixed
canonical completion structure. There is no ground
inhabitance, separation of checked children, partition, or global equality
premise. This single-value helper does not assert countable-sequence
preservation or unbounded elementarity.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172CohenIteration

open bSet ErdosNameTransport Erdos1172PosetCompletion

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- A checked-value reading join yields one actual first-stage name, with
local source membership and equality on the whole completed condition. -/
theorem exists_checked_reading_witness (r : Conditions (ErdosOmegaTwo.omegaOne : bSet B)) (A : PSet.{u})
    (x : bSet (omegaOneAlgebra B))
    (Hread : r.value ≤ ⨆ i : A.Type,
      reads (x =ᴮ check (A.Func i)) (Erdos1172BooleanNameIteration.name r)) :
    ∃ y : bSet B, r.value ≤ y ∈ᴮ check A ∧
      condition r ≤ x =ᴮ mapNames (omegaOneFirstStageHom) y := by
  let W : bSet B → B := fun y => ⨆ i : A.Type,
    reads (x =ᴮ check (A.Func i)) (Erdos1172BooleanNameIteration.name r) ⊓ (y =ᴮ check (A.Func i))
  have Hex : r.value ≤ ⨆ y : bSet B, W y := by
    apply Hread.trans
    apply iSup_le
    intro i
    exact le_iSup_of_le (check (A.Func i)) (le_iSup_of_le i (le_inf le_rfl bv_refl))
  have Hext : B_ext W := B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_bv_eq_left)
  obtain ⟨y, Hy⟩ := exists_convert Hex Hext
  have Hymem : r.value ≤ y ∈ᴮ check A := by
    apply Hy.trans
    apply iSup_le
    intro i
    exact mem_congr (bv_symm inf_le_right) bv_refl (check_mem (PSet.func_mem A i))
  refine ⟨y, Hymem, ?_⟩
  have Hlift : condition r ≤ omegaOneFirstStageHom (W y) :=
    (condition_le_firstStageHom_iff ErdosOmegaTwo.omegaOne r (W y)).mpr Hy
  apply (le_inf le_rfl Hlift).trans
  change condition r ⊓ omegaOneFirstStageHom
    (⨆ i : A.Type,
      reads (x =ᴮ check (A.Func i)) (Erdos1172BooleanNameIteration.name r) ⊓
        (y =ᴮ check (A.Func i))) ≤ x =ᴮ mapNames (omegaOneFirstStageHom) y
  rw [map_iSup]
  erw [inf_iSup_eq]
  apply iSup_le
  intro i
  let Δ : omegaOneAlgebra B := condition r ⊓ omegaOneFirstStageHom
    (reads (x =ᴮ check (A.Func i)) (Erdos1172BooleanNameIteration.name r) ⊓ (y =ᴮ check (A.Func i)))
  have HreadPiece : Δ ≤ condition r ⊓ omegaOneFirstStageHom
      (reads (x =ᴮ check (A.Func i)) (Erdos1172BooleanNameIteration.name r)) :=
    le_inf inf_le_left (inf_le_right.trans (OrderHomClass.mono (omegaOneFirstStageHom) inf_le_left))
  have Hx : Δ ≤ x =ᴮ check (A.Func i) :=
    HreadPiece.trans (condition_inf_firstStageHom_reads_le r (x =ᴮ check (A.Func i)))
  have Hychecked : Δ ≤ mapNames (omegaOneFirstStageHom) y =ᴮ check (A.Func i) := by
    have Hpiece : Δ ≤ omegaOneFirstStageHom (y =ᴮ check (A.Func i)) :=
      inf_le_right.trans (OrderHomClass.mono (omegaOneFirstStageHom) inf_le_right)
    rwa [map_bv_eq, map_check] at Hpiece
  exact bv_trans Hx (bv_symm Hychecked)

end Erdos1172CohenIteration
