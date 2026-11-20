/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4GroundFineSeedOrderType
public import Erdos1172.Part4BooleanUltrapowerAtomic
public import Erdos1172.Part4BooleanUltrapowerChecked
public import Erdos1172.Part4BooleanUltrapowerConstants

@[expose] public section

/-!
# The checked critical seed for a fine Boolean ultrapower

The ultrafilter may be indexed by any small type. Its κ-completeness fixes
the checked predecessors of κ, while its normal fine fibers of order type κ
identify the image of checked κ with checked θ. For the first collapse these
facts give membership in the lifted omega-one, exclusion from every mixed
bounded initial segment, and coverage of every mixed member of the seed.
-/

set_option autoImplicit false
noncomputable section
open Filter bSet Erdos1172GroundUltrapower Lattice
open scoped Flypitch
universe u

namespace Erdos1172BooleanUltrapower

variable {I B : Type u} [NontrivialCompleteBooleanAlgebra B] (U : Ultrafilter I)
variable (κ : Cardinal.{u}) [CardinalInterFilter (U : Filter I) κ]

section Checked

variable [CountableInterFilter (U : Filter I)]

theorem hereditary_fixed_checked_ordinal (α : Ordinal.{u}) (hα : α < κ.ord) :
    (⊤ : Algebra U B) ≤ hereditary U (fun _ => (check (PSet.ordinalMk α) : bSet B)) =ᴮ
      check (PSet.ordinalMk α) := by
  apply bv_trans (liftName_checked U (fun _ => PSet.ordinalMk α))
  apply check_bv_eq
  apply PSet.equiv_iff_eq.mpr
  rw [mk_groundPSet]
  exact diagonal_fix_of_cardinalInterFilter U κ α hα

omit [CardinalInterFilter (U : Filter I) κ] in
theorem hereditary_fine_checked_image (θ : Cardinal.{u}) (a : I → Set θ.ord.ToType)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a) :
    (⊤ : Algebra U B) ≤ hereditary U (fun _ => (check (PSet.ordinalMk κ.ord) : bSet B)) =ᴮ
      check (PSet.ordinalMk θ.ord) := by
  apply bv_trans (liftName_checked U (fun _ => PSet.ordinalMk κ.ord))
  apply check_bv_eq
  apply PSet.equiv_iff_eq.mpr
  rw [mk_groundPSet]
  exact diagonal_cardinal_eq_of_fine_order_type U κ θ a hf hn ht

private theorem ordinal_member_values {C : Type u} [NontrivialCompleteBooleanAlgebra C]
    (y : bSet C) (o : Ordinal.{u}) :
    (y ∈ᴮ check (PSet.ordinalMk o)) = ⨆ i : o.ToType, y =ᴮ check (PSet.ordinalMk i.toOrd.val) := by
  rw [PSet.ordinalMk_eq_def o, check_unfold, mem_unfold]
  change (⨆ i : o.ToType, ⊤ ⊓ (y =ᴮ check (PSet.ordinalMk i.toOrd.val))) = _
  simp only [top_inf_eq]

/-- Every member of the critical ordinal is locally a hereditary image
of an index from the original ordinal. -/
theorem critical_seed_covered (e : CompleteLatticeHom B (Algebra U B)) (K : bSet B)
    (hK : (⊤ : B) ≤ check (PSet.ordinalMk κ.ord) =ᴮ K) (y : bSet (Algebra U B)) :
    (y ∈ᴮ check (PSet.ordinalMk κ.ord)) ≤
      ⨆ x : bSet B, e (x ∈ᴮ K) ⊓ (y =ᴮ hereditary U (fun _ => x)) := by
  rw [ordinal_member_values]
  apply iSup_le
  intro i
  let A := PSet.ordinalMk i.toOrd.val
  apply le_iSup_of_le (check A)
  have hm : (⊤ : B) ≤ check A ∈ᴮ K :=
    mem_congr bv_refl hK (check_mem (PSet.mk_mem_mk_of_lt i.toOrd.property))
  apply le_inf
  · rw [top_unique hm, TopHomClass.map_top]
    exact le_top
  · exact bv_trans le_rfl (bv_symm (le_top.trans
      (hereditary_fixed_checked_ordinal U κ i.toOrd.val i.toOrd.property)))

theorem critical_seed_excludes_bound (e : CompleteLatticeHom B (Algebra U B))
    (he : ∀ b : B, e b = value U (fun _ => b)) (K : bSet B)
    (hK : (⊤ : B) ≤ check (PSet.ordinalMk κ.ord) =ᴮ K) (b : bSet B) :
    e (b ∈ᴮ K) ≤ (check (PSet.ordinalMk κ.ord) ∈ᴮ hereditary U (fun _ => b))ᶜ := by
  have hm : (b ∈ᴮ K) ≤ b ∈ᴮ check (PSet.ordinalMk κ.ord) :=
    mem_congr bv_refl (bv_symm (le_top.trans hK)) le_rfl
  apply (OrderHomClass.mono e hm).trans
  rw [ordinal_member_values, _root_.map_iSup]
  apply iSup_le
  intro i
  let A := PSet.ordinalMk i.toOrd.val
  have hbe : e (b =ᴮ check A) ≤ hereditary U (fun _ => b) =ᴮ check A := by
    rw [he]
    exact bv_trans (value_name_eq U (fun _ => b) (fun _ => check A)).le
      (le_top.trans (hereditary_fixed_checked_ordinal U κ i.toOrd.val i.toOrd.property))
  apply le_compl_iff_disjoint_right.mpr
  apply disjoint_iff.mpr
  have hh : e (b =ᴮ check A) ⊓ (check (PSet.ordinalMk κ.ord) ∈ᴮ hereditary U (fun _ => b)) ≤
      check (PSet.ordinalMk κ.ord) ∈ᴮ check A :=
    bv_rw'' (inf_le_left.trans hbe) inf_le_right B_ext_mem_right
  exact bot_unique (hh.trans_eq (not_check_mem_iff.mp
    (fun h => (not_lt_of_ge i.toOrd.property.le) (PSet.ordinalMk_lt_of_mem h))))

end Checked

open Erdos1172LevyCohen (FirstAlgebra firstStage_checked_upper_eq_omegaOne)
open bSet.ErdosOmegaTwo (omegaOne)

variable (hκ : κ.IsRegular) (hunc : Cardinal.aleph0 < κ)

def fineFirstCollapseLift (x : bSet (FirstAlgebra κ)) : bSet (Algebra U (FirstAlgebra κ)) :=
  letI := CardinalInterFilter.toCountableInterFilter (U : Filter I) hunc
  hereditary U (fun _ => x)

local notation "eκ" => firstCollapseConstantHom U κ hκ hunc
local notation "jκ" => fineFirstCollapseLift U κ hunc
local notation "sκ" => (check (PSet.ordinalMk κ.ord) : bSet (Algebra U (FirstAlgebra κ)))

theorem fine_firstCollapse_seed_covered (y : bSet (Algebra U (FirstAlgebra κ))) :
    (y ∈ᴮ sκ) ≤ ⨆ x : bSet (FirstAlgebra κ), eκ (x ∈ᴮ omegaOne) ⊓ (y =ᴮ jκ x) := by
  let := CardinalInterFilter.toCountableInterFilter (U : Filter I) hunc
  exact critical_seed_covered U κ eκ omegaOne (firstStage_checked_upper_eq_omegaOne κ hκ hunc) y

theorem fine_firstCollapse_seed_excludes_bound (b : bSet (FirstAlgebra κ)) :
    eκ (b ∈ᴮ omegaOne) ≤ (sκ ∈ᴮ jκ b)ᶜ := by
  let := CardinalInterFilter.toCountableInterFilter (U : Filter I) hunc
  exact critical_seed_excludes_bound U κ eκ (firstCollapseConstantHom_apply U κ hκ hunc)
    omegaOne (firstStage_checked_upper_eq_omegaOne κ hκ hunc) b

include hκ in
theorem fine_firstCollapse_omegaOne_image (θ : Cardinal.{u}) (a : I → Set θ.ord.ToType)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a) :
    (⊤ : Algebra U (FirstAlgebra κ)) ≤ jκ omegaOne =ᴮ check (PSet.ordinalMk θ.ord) := by
  let := CardinalInterFilter.toCountableInterFilter (U : Filter I) hunc
  apply bv_trans _ (hereditary_fine_checked_image U κ θ a hf hn ht)
  have hsrc := bv_symm (firstStage_checked_upper_eq_omegaOne κ hκ hunc)
  have h := OrderHomClass.mono eκ hsrc
  rw [TopHomClass.map_top eκ] at h
  exact h.trans_eq (value_name_eq U (fun _ => omegaOne) (fun _ => check (PSet.ordinalMk κ.ord)))

include hκ in
theorem fine_firstCollapse_seed_mem (θ : Cardinal.{u}) (a : I → Set θ.ord.ToType)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a) (hkθ : κ < θ) :
    (⊤ : Algebra U (FirstAlgebra κ)) ≤ sκ ∈ᴮ jκ omegaOne := by
  exact mem_congr bv_refl (bv_symm (fine_firstCollapse_omegaOne_image U κ hκ hunc θ a hf hn ht))
    (check_mem (PSet.mk_mem_mk_of_lt (Cardinal.ord_lt_ord.mpr hkθ)))

end Erdos1172BooleanUltrapower
