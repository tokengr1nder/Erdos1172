/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanUltrapowerOperations
public import Erdos1172.Part4BooleanUltrapowerConstants
public import Erdos1172.Part4BooleanUltrapowerChecked
public import Erdos1172.Part4BooleanSeedKernelClosure

@[expose] public section

/-! # The critical-seed ideal on omega-one in the first Lévy collapse

The constants embed the collapse algebra completely into the completion
of its ultrapower. The hereditary name map fixes each checked predecessor
of the critical ordinal and moves the critical ordinal above its seed.
Splitting mixed members of omega-one into their checked values therefore
places every internally countable subset of omega-one in the seed kernel.
-/

set_option autoImplicit false
noncomputable section
open Filter bSet Erdos1172GroundUltrapower Erdos1172LevyCohen Lattice
open bSet.ErdosIdeal bSet.ErdosSeedKernel bSet.ErdosOmegaTwo
open scoped Flypitch
universe u

namespace Erdos1172BooleanUltrapower

variable (κ : Cardinal.{u}) (U : Ultrafilter κ.ord.ToType)
variable [CardinalInterFilter (U : Filter κ.ord.ToType) κ]
variable (hκ : κ.IsRegular) (hunc : Cardinal.aleph0 < κ)

def firstCollapseLift (x : bSet (FirstAlgebra κ)) : bSet (Algebra U (FirstAlgebra κ)) :=
  letI := CardinalInterFilter.toCountableInterFilter (U : Filter κ.ord.ToType) hunc
  hereditary U (fun _ => x)

def firstCollapseCriticalIdeal : bSet (FirstAlgebra κ) :=
  seedKernelName (firstCollapseConstantHom U κ hκ hunc) (firstCollapseLift κ U hunc)
    (check (PSet.ordinalMk κ.ord)) omegaOne

local notation "e" => firstCollapseConstantHom U κ hκ hunc
local notation "j" => firstCollapseLift κ U hunc
local notation "s" => (check (PSet.ordinalMk κ.ord) : bSet (Algebra U (FirstAlgebra κ)))

theorem firstCollapseLift_eq (x y : bSet (FirstAlgebra κ)) : e (x =ᴮ y) = (j x =ᴮ j y) := by
  let := CardinalInterFilter.toCountableInterFilter (U : Filter κ.ord.ToType) hunc
  exact value_name_eq U (fun _ => x) (fun _ => y)

theorem firstCollapseLift_subset (x y : bSet (FirstAlgebra κ)) : e (x ⊆ᴮ y) = (j x ⊆ᴮ j y) := by
  let := CardinalInterFilter.toCountableInterFilter (U : Filter κ.ord.ToType) hunc
  exact value_name_subset U (fun _ => x) (fun _ => y)

private theorem mem_checked_ord_eq {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (x : bSet B) (o : Ordinal.{u}) :
    (x ∈ᴮ check (PSet.ordinalMk o)) = ⨆ i : o.ToType, x =ᴮ check (PSet.ordinalMk i.toOrd.val) := by
  rw [PSet.ordinalMk_eq_def o, check_unfold, mem_unfold]
  change (⨆ i : o.ToType, ⊤ ⊓ (x =ᴮ check (PSet.ordinalMk i.toOrd.val))) = _
  simp only [top_inf_eq]

variable (hN : NormalRegressive κ U) (hT : ContainsStrictTails κ U)

include hκ hN hT in
theorem firstCollapseCritical_mem : (⊤ : Algebra U (FirstAlgebra κ)) ≤ s ∈ᴮ j omegaOne := by
  let := CardinalInterFilter.toCountableInterFilter (U : Filter κ.ord.ToType) hunc
  have he : (⊤ : Algebra U (FirstAlgebra κ)) ≤ j (check (PSet.ordinalMk κ.ord)) =ᴮ j omegaOne := by
    rw [← firstCollapseLift_eq κ U hκ hunc, ← TopHomClass.map_top e]
    exact OrderHomClass.mono e (Erdos1172LevyCollapse.below_checked_upper_eq_omegaOne κ hκ hunc)
  exact bv_rw'' he (checked_critical_mem_liftName κ U hN hT) B_ext_mem_right

include hN hT in
theorem firstCollapseCritical_misses_bound (b : bSet (FirstAlgebra κ)) :
    e (b ∈ᴮ omegaOne) ≤ (s ∈ᴮ j b)ᶜ := by
  let := CardinalInterFilter.toCountableInterFilter (U : Filter κ.ord.ToType) hunc
  have hb : (b ∈ᴮ omegaOne) ≤ b ∈ᴮ check (PSet.ordinalMk κ.ord) :=
    bv_rw'' (le_top.trans (Erdos1172LevyCollapse.below_omegaOne_eq_checked_upper κ hκ hunc))
      le_rfl B_ext_mem_right
  apply (OrderHomClass.mono e hb).trans
  rw [mem_checked_ord_eq, _root_.map_iSup]
  apply iSup_le
  intro i
  let a := PSet.ordinalMk i.toOrd.val
  have he : e (b =ᴮ check a) ≤ j b =ᴮ check a :=
    bv_trans (firstCollapseLift_eq κ U hκ hunc b (check a)).le
      (le_top.trans (liftName_checked_fixed κ U hN hT i.toOrd.val i.toOrd.property))
  apply le_compl_iff_disjoint_right.mpr
  apply disjoint_iff.mpr
  have hm : e (b =ᴮ check a) ⊓ (s ∈ᴮ j b) ≤ s ∈ᴮ check a :=
    bv_rw'' (inf_le_left.trans he) inf_le_right B_ext_mem_right
  exact bot_unique (hm.trans_eq (not_check_mem_iff.mp (fun h => (not_lt_of_ge i.toOrd.property.le)
    (PSet.ordinalMk_lt_of_mem h))))

include hN hT in
theorem firstCollapseCriticalIdeal_proper :
    (⊤ : FirstAlgebra κ) ≤ properIdeal omegaOne (firstCollapseCriticalIdeal κ U hκ hunc) := by
  let := CardinalInterFilter.toCountableInterFilter (U : Filter κ.ord.ToType) hunc
  apply seedKernelName_properIdeal e j s (fun x y => (firstCollapseLift_eq κ U hκ hunc x y).le)
    (firstCollapseConstantHom_injective U κ hκ hunc)
  · exact le_top.trans (firstCollapseCritical_mem κ U hκ hunc hN hT)
  · exact hereditary_empty (B := FirstAlgebra κ) U
  · exact fun x y => (firstCollapseLift_subset κ U hκ hunc x y).le
  · exact fun x y => hereditary_binary_union_subset U (fun _ => x) (fun _ => y)

include hN hT in
theorem firstCollapseCriticalIdeal_countableAbsorption :
    (⊤ : FirstAlgebra κ) ≤ countableAbsorption omegaOne (firstCollapseCriticalIdeal κ U hκ hunc) := by
  apply seedKernelName_countableAbsorption e j s (fun x y => (firstCollapseLift_eq κ U hκ hunc x y).le)
    (fun x y => (firstCollapseLift_subset κ U hκ hunc x y).le)
  intro b
  rw [top_inf_eq]
  exact firstCollapseCritical_misses_bound κ U hκ hunc hN hT b

include hN hT in
theorem firstCollapseSeedCovered (y : bSet (Algebra U (FirstAlgebra κ))) :
    (y ∈ᴮ s) ≤ ⨆ x : bSet (FirstAlgebra κ), e (x ∈ᴮ omegaOne) ⊓ (y =ᴮ j x) := by
  let := CardinalInterFilter.toCountableInterFilter (U : Filter κ.ord.ToType) hunc
  rw [mem_checked_ord_eq]
  apply iSup_le
  intro i
  let a := PSet.ordinalMk i.toOrd.val
  apply le_iSup_of_le (check a)
  have hb : (⊤ : FirstAlgebra κ) ≤ check a ∈ᴮ omegaOne :=
    bv_rw'' (Erdos1172LevyCollapse.below_checked_upper_eq_omegaOne κ hκ hunc)
      (check_mem (PSet.mk_mem_mk_of_lt i.toOrd.property)) B_ext_mem_right
  apply le_inf
  · rw [top_unique hb, TopHomClass.map_top]; exact le_top
  · exact bv_trans le_rfl (bv_symm (le_top.trans
      (liftName_checked_fixed κ U hN hT i.toOrd.val i.toOrd.property)))

end Erdos1172BooleanUltrapower
