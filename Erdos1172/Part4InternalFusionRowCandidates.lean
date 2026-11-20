/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalBoundedFunctionValue
public import Erdos1172.Part4InternalCanonicalBlockEnumeration
public import Erdos1172.Part4InternalSimultaneousTraces
public import Erdos1172.Part4InternalRowCandidates
public import Erdos1172.Part4InternalRowCandidateCongruence

@[expose] public section

/-!
# Activated row candidates for the second block fusion

The row is the proof-independent value of the same fixed canonical
enumeration graph. Only stages `nu < j < xi` constrain this row. A failed
intermediate block is the empty set and imposes no edge condition, while
its recorded coordinate still imposes the strict order condition.

The actual section family is constructed, not assumed. Least choice
derives nonemptiness from a proper countably closed absorbing
ideal, a co-large terminal seed, and co-large activated whole-block
sections. Deriving those last two co-largeness premises from a complete
fusion history remains a separate structural obligation. No successful
run or nonempty candidate set is supplied as a premise.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionRowCandidates

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosPartition ErdosCanonicalBlocks
open ErdosBoundedFunctionValue ErdosRelationGraph ErdosSimultaneousTraces
open ErdosColargeIntersection ErdosRowCandidates ErdosCountablePast
open ErdosIndexedIntersection ErdosOrdinalLeast

def activatedStages (ξ ν : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun j => ν ∈ᴮ j) ξ

theorem mem_activatedStages_iff {ξ ν j : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ j ∈ᴮ activatedStages ξ ν ↔ Γ ≤ j ∈ᴮ ξ ∧ Γ ≤ ν ∈ᴮ j :=
  mem_comprehend_and B_ext_mem_right

theorem activatedStages_subset {ξ ν : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ activatedStages ξ ν ⊆ᴮ ξ := comprehend_subset (ϕ := fun j => ν ∈ᴮ j) ξ

theorem activatedStages_countable {ξ ν : bSet 𝔹} {Γ : 𝔹}
    (Hξ : Γ ≤ ξ ∈ᴮ omegaOne) : Γ ≤ injects_into (activatedStages ξ ν) bSet.omega :=
  injects_into_trans (injects_into_of_subset activatedStages_subset)
    (omegaOne_member_injects Hξ)

theorem activatedStages_congr_row (ξ : bSet 𝔹) : B_congr (activatedStages ξ) := by
  intro ν μ Γ H
  apply mem_ext
  · apply le_iInf
    intro j
    rw [← deduction]
    have Hj := mem_activatedStages_iff.mp
      (show Γ ⊓ j ∈ᴮ activatedStages ξ ν ≤ j ∈ᴮ activatedStages ξ ν from inf_le_right)
    exact mem_activatedStages_iff.mpr ⟨Hj.1,
      mem_congr (inf_le_left.trans H) bv_refl Hj.2⟩
  · apply le_iInf
    intro j
    rw [← deduction]
    have Hj := mem_activatedStages_iff.mp
      (show Γ ⊓ j ∈ᴮ activatedStages ξ μ ≤ j ∈ᴮ activatedStages ξ μ from inf_le_right)
    exact mem_activatedStages_iff.mpr ⟨Hj.1,
      mem_congr (inf_le_left.trans (bv_symm H)) bv_refl Hj.2⟩

def canonicalRow (E b : bSet 𝔹) : bSet 𝔹 := graphValue blockEnumerationCodes E b

theorem canonicalRow_pair {color : Bool} {R E b : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (Hb : Γ ≤ b ∈ᴮ blockObjects color R) : Γ ≤ pair b (canonicalRow E b) ∈ᴮ E :=
  graphValue_pair_mem HE Hb

theorem canonicalRow_eq_of_pair {color : Bool} {R E b r : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (Hbr : Γ ≤ pair b r ∈ᴮ E) : Γ ≤ canonicalRow E b =ᴮ r :=
  graphValue_eq_of_pair HE Hbr

theorem canonicalRow_data {color : Bool} {R E b : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (Hlaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (Hb : Γ ≤ b ∈ᴮ blockObjects color R) :
    Γ ≤ blockEnumerationData color R b (canonicalRow E b) :=
  blockEnumerationFamilyLaw_apply Hlaw Hb (canonicalRow_pair HE Hb)

def fusionSeed (edgeColor : Bool) (R E b top : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun v => ⨆ x, pair v x ∈ᴮ canonicalRow E b ⊓
    graphColor edgeColor R x top) omegaOne

private theorem seedPredicate_ext (edgeColor : Bool) (R E b top : bSet 𝔹) :
    B_ext (fun v => ⨆ x, pair v x ∈ᴮ canonicalRow E b ⊓ graphColor edgeColor R x top) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_pair_mem_left B_ext_const)

theorem mem_fusionSeed_iff {edgeColor : Bool} {R E b top v : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ v ∈ᴮ fusionSeed edgeColor R E b top ↔
      Γ ≤ v ∈ᴮ omegaOne ∧
        Γ ≤ ⨆ x, pair v x ∈ᴮ canonicalRow E b ⊓ graphColor edgeColor R x top :=
  mem_comprehend_and (seedPredicate_ext edgeColor R E b top)

theorem fusionSeed_subset {edgeColor : Bool} {R E b top : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ fusionSeed edgeColor R E b top ⊆ᴮ omegaOne :=
  comprehend_subset (ϕ := fun v => ⨆ x, pair v x ∈ᴮ canonicalRow E b ⊓
    graphColor edgeColor R x top) omegaOne

theorem fusionSeed_value_of_pair {edgeColor : Bool} {R E b top v x : bSet 𝔹} {Γ : 𝔹}
    (Hfunc : Γ ≤ is_func (canonicalRow E b))
    (Hv : Γ ≤ v ∈ᴮ fusionSeed edgeColor R E b top)
    (Hvx : Γ ≤ pair v x ∈ᴮ canonicalRow E b) : Γ ≤ graphColor edgeColor R x top := by
  obtain ⟨y, Hy⟩ := exists_convert (mem_fusionSeed_iff.mp Hv).2
    (B_ext_inf B_ext_pair_mem_right (graphColor_ext_left edgeColor R top))
  have Hxy := eq_of_is_func_of_eq Hfunc bv_refl Hvx (Hy.trans inf_le_left)
  exact bv_rw' (ϕ := fun z => graphColor edgeColor R z top) Hxy
    (h_congr := graphColor_ext_left edgeColor R top)
    (H_new := Hy.trans inf_le_right)

def sectionRequirement (edgeColor : Bool) (R E b Blocks j v : bSet 𝔹) : 𝔹 :=
  ⨅ c, ⨅ x, ⨅ y, _root_.imp
    ((pair j c ∈ᴮ Blocks ⊓ pair v x ∈ᴮ canonicalRow E b) ⊓ y ∈ᴮ c)
    (graphColor edgeColor R x y)

theorem sectionRequirement_ext_coordinate
    (edgeColor : Bool) (R E b Blocks j : bSet 𝔹) :
    B_ext (sectionRequirement edgeColor R E b Blocks j) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_imp (h₁ := B_ext_inf (B_ext_inf B_ext_const B_ext_pair_mem_left) B_ext_const)
      (h₂ := B_ext_const))))

theorem sectionRequirement_ext_stage
    (edgeColor : Bool) (R E b Blocks v : bSet 𝔹) :
    B_ext (fun j => sectionRequirement edgeColor R E b Blocks j v) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_imp (h₁ := B_ext_inf (B_ext_inf B_ext_pair_mem_left B_ext_const) B_ext_const)
      (h₂ := B_ext_const))))

def fusionSection (edgeColor : Bool) (R E b Blocks j : bSet 𝔹) : bSet 𝔹 :=
  comprehend (sectionRequirement edgeColor R E b Blocks j) omegaOne

theorem mem_fusionSection_iff {edgeColor : Bool} {R E b Blocks j v : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ v ∈ᴮ fusionSection edgeColor R E b Blocks j ↔
      Γ ≤ v ∈ᴮ omegaOne ∧ Γ ≤ sectionRequirement edgeColor R E b Blocks j v :=
  mem_comprehend_and (sectionRequirement_ext_coordinate edgeColor R E b Blocks j)

theorem fusionSection_subset {edgeColor : Bool} {R E b Blocks j : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ fusionSection edgeColor R E b Blocks j ⊆ᴮ omegaOne :=
  comprehend_subset (ϕ := sectionRequirement edgeColor R E b Blocks j) omegaOne

theorem fusionSection_congr_stage (edgeColor : Bool) (R E b Blocks : bSet 𝔹) :
    B_congr (fusionSection edgeColor R E b Blocks) := by
  intro j k Γ Hjk
  apply mem_ext
  · apply le_iInf
    intro v
    rw [← deduction]
    have Hv := mem_fusionSection_iff.mp
      (show Γ ⊓ v ∈ᴮ fusionSection edgeColor R E b Blocks j ≤
        v ∈ᴮ fusionSection edgeColor R E b Blocks j from inf_le_right)
    exact mem_fusionSection_iff.mpr ⟨Hv.1,
      bv_rw'' (inf_le_left.trans Hjk) Hv.2
        (sectionRequirement_ext_stage edgeColor R E b Blocks v)⟩
  · apply le_iInf
    intro v
    rw [← deduction]
    have Hv := mem_fusionSection_iff.mp
      (show Γ ⊓ v ∈ᴮ fusionSection edgeColor R E b Blocks k ≤
        v ∈ᴮ fusionSection edgeColor R E b Blocks k from inf_le_right)
    exact mem_fusionSection_iff.mpr ⟨Hv.1,
      bv_rw' (inf_le_left.trans Hjk)
        (h_congr := sectionRequirement_ext_stage edgeColor R E b Blocks v) (H_new := Hv.2)⟩

theorem fusionSection_apply
    {edgeColor : Bool} {R E b Blocks j c v x y : bSet 𝔹} {Γ : 𝔹}
    (Hv : Γ ≤ v ∈ᴮ fusionSection edgeColor R E b Blocks j)
    (Hjc : Γ ≤ pair j c ∈ᴮ Blocks) (Hvx : Γ ≤ pair v x ∈ᴮ canonicalRow E b)
    (Hy : Γ ≤ y ∈ᴮ c) : Γ ≤ graphColor edgeColor R x y :=
  (le_inf ((mem_fusionSection_iff.mp Hv).2.trans
    ((iInf_le _ c).trans ((iInf_le _ x).trans (iInf_le _ y))))
    (le_inf (le_inf Hjc Hvx) Hy)).trans bv_imp_elim

/-- Empty intermediate blocks contribute the full coordinate set, not an
empty section. Their past coordinate will still be removed separately. -/
theorem fusionSection_eq_omegaOne_of_empty
    {edgeColor : Bool} {R E b Blocks j : bSet 𝔹} {Γ : 𝔹}
    (Hfunc : Γ ≤ is_func Blocks) (Hempty : Γ ≤ pair j (∅ : bSet 𝔹) ∈ᴮ Blocks) :
    Γ ≤ fusionSection edgeColor R E b Blocks j =ᴮ omegaOne := by
  apply subset_ext fusionSection_subset
  rw [subset_unfold']
  apply le_iInf
  intro v
  rw [← deduction]
  apply mem_fusionSection_iff.mpr
  refine ⟨inf_le_right, ?_⟩
  apply le_iInf
  intro c
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  have Hc : (Γ ⊓ v ∈ᴮ omegaOne) ⊓
      ((pair j c ∈ᴮ Blocks ⊓ pair v x ∈ᴮ canonicalRow E b) ⊓ y ∈ᴮ c) ≤
      c =ᴮ (∅ : bSet 𝔹) :=
    eq_of_is_func_of_eq (inf_le_left.trans (inf_le_left.trans Hfunc)) bv_refl
      (inf_le_right.trans (inf_le_left.trans inf_le_left))
      (inf_le_left.trans (inf_le_left.trans Hempty))
  have Hyempty := mem_congr bv_refl Hc (inf_le_right.trans inf_le_right)
  exact (bot_of_mem_empty Hyempty).trans bot_le

def fusionSectionFamily (edgeColor : Bool) (R E b Blocks D : bSet 𝔹) : bSet 𝔹 :=
  relationGraph D (bv_powerset omegaOne)
    (fun j A => A =ᴮ fusionSection edgeColor R E b Blocks j)

private theorem sectionFamily_ext_left
    (edgeColor : Bool) (R E b Blocks A : bSet 𝔹) :
    B_ext (fun j => A =ᴮ fusionSection edgeColor R E b Blocks j) :=
  B_ext_term (ϕ := fun X => A =ᴮ X) (t := fusionSection edgeColor R E b Blocks)
    B_ext_bv_eq_right (fusionSection_congr_stage edgeColor R E b Blocks)

theorem mem_fusionSectionFamily_iff
    {edgeColor : Bool} {R E b Blocks D j A : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair j A ∈ᴮ fusionSectionFamily edgeColor R E b Blocks D ↔
      Γ ≤ j ∈ᴮ D ∧ Γ ≤ A ∈ᴮ bv_powerset omegaOne ∧
        Γ ≤ A =ᴮ fusionSection edgeColor R E b Blocks j :=
  mem_relationGraph_iff (sectionFamily_ext_left edgeColor R E b Blocks)
    (fun _ => B_ext_bv_eq_left)

theorem fusionSectionFamily_is_function
    {edgeColor : Bool} {R E b Blocks D : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ is_function D (bv_powerset omegaOne)
      (fusionSectionFamily edgeColor R E b Blocks D) := by
  apply relationGraph_is_function
    (sectionFamily_ext_left edgeColor R E b Blocks) (fun _ => B_ext_bv_eq_left)
  · apply le_iInf
    intro j
    rw [← deduction]
    exact le_iSup_of_le (fusionSection edgeColor R E b Blocks j)
      (le_inf (mem_powerset_iff.mpr fusionSection_subset) bv_refl)
  · intro j k A B Δ _ _ _ _ _ HA HB Hjk
    exact bv_trans HA (bv_trans (fusionSection_congr_stage edgeColor R E b Blocks Hjk)
      (bv_symm HB))

theorem fusionSectionFamily_pair
    {edgeColor : Bool} {R E b Blocks D j : bSet 𝔹} {Γ : 𝔹}
    (Hj : Γ ≤ j ∈ᴮ D) :
    Γ ≤ pair j (fusionSection edgeColor R E b Blocks j) ∈ᴮ
      fusionSectionFamily edgeColor R E b Blocks D :=
  mem_fusionSectionFamily_iff.mpr ⟨Hj, mem_powerset_iff.mpr fusionSection_subset, bv_refl⟩

def fusionRowCandidates (edgeColor : Bool) (R E b top ξ ν Blocks X : bSet 𝔹) : bSet 𝔹 :=
  rowCandidates (activatedStages ξ ν) (fusionSeed edgeColor R E b top)
    (fusionSectionFamily edgeColor R E b Blocks ξ)
    (rowHistory ξ X ν)

theorem fusionRowCandidates_congr_row
    (edgeColor : Bool) (R E b top ξ Blocks X : bSet 𝔹) :
    B_congr (fun ν => fusionRowCandidates edgeColor R E b top ξ ν Blocks X) := by
  intro ν μ Γ H
  exact bv_trans
    (rowCandidates_congr_stage (fusionSeed edgeColor R E b top)
      (fusionSectionFamily edgeColor R E b Blocks ξ) (rowHistory ξ X ν)
      (activatedStages_congr_row ξ H))
    (rowCandidates_congr_graph (activatedStages ξ μ) (fusionSeed edgeColor R E b top)
      (fusionSectionFamily edgeColor R E b Blocks ξ) (rowHistory_congr_row ξ X H))

theorem fusionRowCandidates_subset
    {edgeColor : Bool} {R E b top ξ ν Blocks X : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ fusionRowCandidates edgeColor R E b top ξ ν Blocks X ⊆ᴮ omegaOne :=
  rowCandidates_subset

theorem activated_rowHistory_is_func' {ξ ν X : bSet 𝔹} {Γ : 𝔹}
    (HX : Γ ≤ is_func' (prod ξ omegaOne) omegaOne X) (Hν : Γ ≤ ν ∈ᴮ omegaOne) :
    Γ ≤ is_func' (activatedStages ξ ν) omegaOne (rowHistory ξ X ν) :=
  is_func'_subset_of_is_func' (is_func'_of_is_function (rowHistory_is_function HX Hν))
    activatedStages_subset

/-- Exact membership, before expanding the activation guard. The ordinary
row-candidate equivalence requires only the actual weak coordinate history. -/
theorem mem_fusionRowCandidates_iff
    {edgeColor : Bool} {R E b top ξ ν Blocks X v : bSet 𝔹} {Γ : 𝔹}
    (HX : Γ ≤ is_func' (prod ξ omegaOne) omegaOne X) (Hν : Γ ≤ ν ∈ᴮ omegaOne) :
    Γ ≤ v ∈ᴮ fusionRowCandidates edgeColor R E b top ξ ν Blocks X ↔
      Γ ≤ rowAdmissible (activatedStages ξ ν) (fusionSeed edgeColor R E b top)
        (fusionSectionFamily edgeColor R E b Blocks ξ)
        (rowHistory ξ X ν) v :=
  mem_rowCandidates_iff (activated_rowHistory_is_func' HX Hν)

theorem fusionCandidate_mem_seed
    {edgeColor : Bool} {R E b top ξ ν Blocks X v : bSet 𝔹} {Γ : 𝔹}
    (HX : Γ ≤ is_func' (prod ξ omegaOne) omegaOne X) (Hν : Γ ≤ ν ∈ᴮ omegaOne)
    (Hv : Γ ≤ v ∈ᴮ fusionRowCandidates edgeColor R E b top ξ ν Blocks X) :
    Γ ≤ v ∈ᴮ fusionSeed edgeColor R E b top :=
  ((mem_fusionRowCandidates_iff HX Hν).mp Hv).trans (inf_le_right.trans inf_le_left)

theorem fusionCandidate_mem_section
    {edgeColor : Bool} {R E b top ξ ν Blocks X v j : bSet 𝔹} {Γ : 𝔹}
    (HX : Γ ≤ is_func' (prod ξ omegaOne) omegaOne X) (Hν : Γ ≤ ν ∈ᴮ omegaOne)
    (Hv : Γ ≤ v ∈ᴮ fusionRowCandidates edgeColor R E b top ξ ν Blocks X)
    (Hjξ : Γ ≤ j ∈ᴮ ξ) (Hνj : Γ ≤ ν ∈ᴮ j) :
    Γ ≤ v ∈ᴮ fusionSection edgeColor R E b Blocks j := by
  have Hlegal := (mem_fusionRowCandidates_iff HX Hν).mp Hv
  have Hj := mem_activatedStages_iff.mpr ⟨Hjξ, Hνj⟩
  exact (le_inf (Hlegal.trans (inf_le_right.trans (inf_le_right.trans
    (inf_le_left.trans ((iInf_le _ j).trans
      (iInf_le _ (fusionSection edgeColor R E b Blocks j)))))))
    (le_inf Hj (fusionSectionFamily_pair Hjξ))).trans bv_imp_elim

theorem fusionCandidate_above_previous
    {edgeColor : Bool} {R E b top ξ ν Blocks X v j w : bSet 𝔹} {Γ : 𝔹}
    (HX : Γ ≤ is_func' (prod ξ omegaOne) omegaOne X) (Hν : Γ ≤ ν ∈ᴮ omegaOne)
    (Hv : Γ ≤ v ∈ᴮ fusionRowCandidates edgeColor R E b top ξ ν Blocks X)
    (Hjξ : Γ ≤ j ∈ᴮ ξ) (Hνj : Γ ≤ ν ∈ᴮ j)
    (Hjw : Γ ≤ pair (pair j ν) w ∈ᴮ X) : Γ ≤ w ∈ᴮ v := by
  have Hlegal := (mem_fusionRowCandidates_iff HX Hν).mp Hv
  have Hhistory := (rowHistory_pair_iff HX Hν Hjξ).mpr Hjw
  exact (le_inf (Hlegal.trans (inf_le_right.trans (inf_le_right.trans
    (inf_le_right.trans ((iInf_le _ j).trans (iInf_le _ w))))))
    (le_inf (mem_activatedStages_iff.mpr ⟨Hjξ, Hνj⟩) Hhistory)).trans bv_imp_elim

theorem fusionCandidate_seed_edge
    {edgeColor : Bool} {R E b top ξ ν Blocks X v x : bSet 𝔹} {Γ : 𝔹}
    (HX : Γ ≤ is_func' (prod ξ omegaOne) omegaOne X) (Hν : Γ ≤ ν ∈ᴮ omegaOne)
    (Hr : Γ ≤ is_func (canonicalRow E b))
    (Hv : Γ ≤ v ∈ᴮ fusionRowCandidates edgeColor R E b top ξ ν Blocks X)
    (Hvx : Γ ≤ pair v x ∈ᴮ canonicalRow E b) : Γ ≤ graphColor edgeColor R x top :=
  fusionSeed_value_of_pair Hr (fusionCandidate_mem_seed HX Hν Hv) Hvx

theorem fusionCandidate_cross_previous_block
    {edgeColor : Bool} {R E b top ξ ν Blocks X v j c x y : bSet 𝔹} {Γ : 𝔹}
    (HX : Γ ≤ is_func' (prod ξ omegaOne) omegaOne X) (Hν : Γ ≤ ν ∈ᴮ omegaOne)
    (Hv : Γ ≤ v ∈ᴮ fusionRowCandidates edgeColor R E b top ξ ν Blocks X)
    (Hjξ : Γ ≤ j ∈ᴮ ξ) (Hνj : Γ ≤ ν ∈ᴮ j) (Hjc : Γ ≤ pair j c ∈ᴮ Blocks)
    (Hvx : Γ ≤ pair v x ∈ᴮ canonicalRow E b) (Hy : Γ ≤ y ∈ᴮ c) :
    Γ ≤ graphColor edgeColor R x y :=
  fusionSection_apply (fusionCandidate_mem_section HX Hν Hv Hjξ Hνj) Hjc Hvx Hy

/-- The whole-block condition applies to every point of the same fixed
canonical enumeration of an intermediate successful object. -/
theorem fusionCandidate_cross_selected_enumeration
    {color edgeColor : Bool} {R E b top ξ ν Blocks X v j c r x k y : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (Hlaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HX : Γ ≤ is_func' (prod ξ omegaOne) omegaOne X) (Hν : Γ ≤ ν ∈ᴮ omegaOne)
    (Hv : Γ ≤ v ∈ᴮ fusionRowCandidates edgeColor R E b top ξ ν Blocks X)
    (Hjξ : Γ ≤ j ∈ᴮ ξ) (Hνj : Γ ≤ ν ∈ᴮ j) (Hjc : Γ ≤ pair j c ∈ᴮ Blocks)
    (Hvx : Γ ≤ pair v x ∈ᴮ canonicalRow E b)
    (Hcr : Γ ≤ pair c r ∈ᴮ E) (Hky : Γ ≤ pair k y ∈ᴮ r) :
    Γ ≤ graphColor edgeColor R x y := by
  have Hr : Γ ≤ is_function omegaOne omegaTwo r :=
    (selected_enumeration_data HE Hlaw Hcr).trans (inf_le_left.trans inf_le_left)
  have Hy : Γ ≤ y ∈ᴮ c := mem_congr bv_refl (selected_enumeration_image HE Hlaw Hcr)
    (mem_image Hky (mem_domain_of_is_function Hky Hr) (mem_codomain_of_is_function Hky Hr))
  exact fusionCandidate_cross_previous_block HX Hν Hv Hjξ Hνj Hjc Hvx Hy

theorem fusionRowCandidates_colarge
    {edgeColor : Bool} {R J E b top ξ ν Blocks X : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J) (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J) (Hξ : Γ ≤ ξ ∈ᴮ omegaOne)
    (Hν : Γ ≤ ν ∈ᴮ omegaOne) (HX : Γ ≤ is_func' (prod ξ omegaOne) omegaOne X)
    (Hseed : Γ ≤ colarge omegaOne J (fusionSeed edgeColor R E b top))
    (Hsections : Γ ≤ ⨅ j, _root_.imp (j ∈ᴮ ξ ⊓ ν ∈ᴮ j)
      (colarge omegaOne J (fusionSection edgeColor R E b Blocks j))) :
    Γ ≤ colarge omegaOne J (fusionRowCandidates edgeColor R E b top ξ ν Blocks X) := by
  let D := activatedStages ξ ν
  let F := fusionSectionFamily edgeColor R E b Blocks ξ
  have Hvalues : Γ ≤ ⨅ j, ⨅ A, _root_.imp (j ∈ᴮ D ⊓ pair j A ∈ᴮ F)
      (colarge omegaOne J A) := by
    apply le_iInf
    intro j
    apply le_iInf
    intro A
    rw [← deduction]
    have Hj := mem_activatedStages_iff.mp
      (show Γ ⊓ (j ∈ᴮ D ⊓ pair j A ∈ᴮ F) ≤ j ∈ᴮ activatedStages ξ ν from
        inf_le_right.trans inf_le_left)
    have HA := mem_fusionSectionFamily_iff.mp
      (show Γ ⊓ (j ∈ᴮ D ⊓ pair j A ∈ᴮ F) ≤ pair j A ∈ᴮ F from
        inf_le_right.trans inf_le_right)
    have Hcolarge := (le_inf (inf_le_left.trans (Hsections.trans (iInf_le _ j)))
      (le_inf Hj.1 Hj.2)).trans bv_imp_elim
    exact le_inf (mem_powerset_iff.mp HA.2.1)
      (mem_congr (bv_symm (difference_congr_right HA.2.2)) bv_refl
        (Hcolarge.trans inf_le_right))
  have Hinter : Γ ≤ colarge omegaOne J (indexedIntersection omegaOne F D) :=
    indexedIntersection_colarge_of_colarge_values HJ Hclosure
      (is_func'_subset_of_is_func' (is_func'_of_is_function fusionSectionFamily_is_function)
        activatedStages_subset)
      (activatedStages_countable Hξ) Hvalues
  have Hpast : Γ ≤ past (image D omegaOne (rowHistory ξ X ν)) ∈ᴮ J :=
    past_small HJ Habsorb Hclosure image_subset
      (ErdosCountableImage.image_countable (activated_rowHistory_is_func' HX Hν)
        (activatedStages_countable Hξ))
  exact colarge_difference_of_small HJ Hinter
    (small_union (unionClosed_of_isIdeal HJ) (Hseed.trans inf_le_right) Hpast)

/-- Existence is derived from the actual countable section intersection
and loss removal. No candidate-nonemptiness or successful history premise
is hidden in the conclusion. -/
theorem exists_least_fusionRowCandidate
    {edgeColor : Bool} {R J E b top ξ ν Blocks X : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ properIdeal omegaOne J) (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J) (Hξ : Γ ≤ ξ ∈ᴮ omegaOne)
    (Hν : Γ ≤ ν ∈ᴮ omegaOne) (HX : Γ ≤ is_func' (prod ξ omegaOne) omegaOne X)
    (Hseed : Γ ≤ colarge omegaOne J (fusionSeed edgeColor R E b top))
    (Hsections : Γ ≤ ⨅ j, _root_.imp (j ∈ᴮ ξ ⊓ ν ∈ᴮ j)
      (colarge omegaOne J (fusionSection edgeColor R E b Blocks j))) :
    ∃ v : bSet 𝔹,
      Γ ≤ colarge omegaOne J (fusionRowCandidates edgeColor R E b top ξ ν Blocks X) ⊓
        leastIn (fusionRowCandidates edgeColor R E b top ξ ν Blocks X) v := by
  have Hcolarge := fusionRowCandidates_colarge (HJ.trans inf_le_left) Habsorb Hclosure
    Hξ Hν HX Hseed Hsections
  have Hnonempty := positive_not_empty (HJ.trans inf_le_left) (colarge_positive HJ Hcolarge)
  obtain ⟨v, Hv⟩ := exists_least_of_nonempty omegaOne_Ord fusionRowCandidates_subset Hnonempty
  exact ⟨v, le_inf Hcolarge Hv⟩

end bSet.ErdosFusionRowCandidates
