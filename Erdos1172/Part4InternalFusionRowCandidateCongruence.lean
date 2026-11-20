/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionRowCandidates
public import Erdos1172.Part4InternalFusionHistoryCongruence

@[expose] public section

/-!
# Unconditional congruence of second-fusion row candidates

Every equality here holds on arbitrary names, including malformed graphs,
inactive rows, and failed intermediate blocks. No candidate nonemptiness,
functionality, ordinal membership, or ideal law is assumed. In particular
evaluating the earlier block at the varying row index is accounted for:
both the chosen block and the activated-stage guard change coherently.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionRowCandidates

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosPartition ErdosCanonicalBlocks ErdosBoundedFunctionValue
open ErdosRelationGraph ErdosRowCandidates ErdosIndexedIntersection
open ErdosSimultaneousTraces ErdosCountablePast ErdosFusionHistoryCongruence

private theorem binary_union_congr_both {A B C D : bSet 𝔹} {Γ : 𝔹}
    (HAB : Γ ≤ A =ᴮ B) (HCD : Γ ≤ C =ᴮ D) :
    Γ ≤ binary_union A C =ᴮ binary_union B D := by
  unfold binary_union
  exact B_congr_bv_union (bv_trans (B_congr_insert1_left HAB)
    (B_congr_insert1_right (B_congr_insert1_left HCD)))

private theorem difference_congr_both {A B C D : bSet 𝔹} {Γ : 𝔹}
    (HAB : Γ ≤ A =ᴮ B) (HCD : Γ ≤ C =ᴮ D) :
    Γ ≤ difference A C =ᴮ difference B D :=
  bv_trans (B_congr_comprehend (ϕ := fun z => (z ∈ᴮ C)ᶜ)
    (H_congr := B_ext_neg (h := B_ext_mem_left)) HAB) (difference_congr_right HCD)

theorem canonicalRow_congr_object (E : bSet 𝔹) : B_congr (canonicalRow E) :=
  graphValue_congr_input blockEnumerationCodes E

theorem fusionSeed_congr_object (edgeColor : Bool) (R E top : bSet 𝔹) :
    B_congr (fun b => fusionSeed edgeColor R E b top) :=
  comprehend_parameter_congr omegaOne
    (fun b v => ⨆ x, pair v x ∈ᴮ canonicalRow E b ⊓ graphColor edgeColor R x top)
    (fun _ => B_ext_iSup (h := fun _ => B_ext_inf B_ext_pair_mem_left B_ext_const))
    (fun v => B_ext_iSup (h := fun x => B_ext_inf
      (B_ext_term (ϕ := fun r => pair v x ∈ᴮ r) (t := canonicalRow E)
        B_ext_mem_right (canonicalRow_congr_object E)) B_ext_const))

theorem fusionSeed_congr_top (edgeColor : Bool) (R E b : bSet 𝔹) :
    B_congr (fusionSeed edgeColor R E b) :=
  comprehend_parameter_congr omegaOne
    (fun top v => ⨆ x, pair v x ∈ᴮ canonicalRow E b ⊓ graphColor edgeColor R x top)
    (fun _ => B_ext_iSup (h := fun _ => B_ext_inf B_ext_pair_mem_left B_ext_const))
    (fun _ => B_ext_iSup (h := fun x =>
      B_ext_inf B_ext_const (graphColor_ext_right edgeColor R x)))

theorem sectionRequirement_ext_object
    (edgeColor : Bool) (R E Blocks j v : bSet 𝔹) :
    B_ext (fun b => sectionRequirement edgeColor R E b Blocks j v) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun x => B_ext_iInf (h := fun _ =>
    B_ext_imp (h₁ := B_ext_inf (B_ext_inf B_ext_const
      (B_ext_term (ϕ := fun r => pair v x ∈ᴮ r) (t := canonicalRow E)
        B_ext_mem_right (canonicalRow_congr_object E))) B_ext_const)
      (h₂ := B_ext_const))))

theorem sectionRequirement_ext_blocks
    (edgeColor : Bool) (R E b j v : bSet 𝔹) :
    B_ext (fun Blocks => sectionRequirement edgeColor R E b Blocks j v) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_imp (h₁ := B_ext_inf (B_ext_inf B_ext_mem_right B_ext_const) B_ext_const)
      (h₂ := B_ext_const))))

theorem fusionSection_congr_object
    (edgeColor : Bool) (R E Blocks j : bSet 𝔹) :
    B_congr (fun b => fusionSection edgeColor R E b Blocks j) :=
  comprehend_parameter_congr omegaOne
    (fun b v => sectionRequirement edgeColor R E b Blocks j v)
    (fun b => sectionRequirement_ext_coordinate edgeColor R E b Blocks j)
    (sectionRequirement_ext_object edgeColor R E Blocks j)

theorem fusionSection_congr_blocks
    (edgeColor : Bool) (R E b j : bSet 𝔹) :
    B_congr (fun Blocks => fusionSection edgeColor R E b Blocks j) :=
  comprehend_parameter_congr omegaOne
    (fun Blocks v => sectionRequirement edgeColor R E b Blocks j v)
    (fun Blocks => sectionRequirement_ext_coordinate edgeColor R E b Blocks j)
    (sectionRequirement_ext_blocks edgeColor R E b j)

theorem fusionSectionFamily_congr_object
    (edgeColor : Bool) (R E Blocks D : bSet 𝔹) :
    B_congr (fun b => fusionSectionFamily edgeColor R E b Blocks D) :=
  relationGraph_parameter_congr D (bv_powerset omegaOne)
    (fun b j A => A =ᴮ fusionSection edgeColor R E b Blocks j)
    (fun j A => B_ext_term (ϕ := fun C => A =ᴮ C)
      (t := fun b => fusionSection edgeColor R E b Blocks j)
      B_ext_bv_eq_right (fusionSection_congr_object edgeColor R E Blocks j))

theorem fusionSectionFamily_congr_blocks
    (edgeColor : Bool) (R E b D : bSet 𝔹) :
    B_congr (fun Blocks => fusionSectionFamily edgeColor R E b Blocks D) :=
  relationGraph_parameter_congr D (bv_powerset omegaOne)
    (fun Blocks j A => A =ᴮ fusionSection edgeColor R E b Blocks j)
    (fun j A => B_ext_term (ϕ := fun C => A =ᴮ C)
      (t := fun Blocks => fusionSection edgeColor R E b Blocks j)
      B_ext_bv_eq_right (fusionSection_congr_blocks edgeColor R E b j))

theorem fusionSectionFamily_congr_domain
    (edgeColor : Bool) (R E b Blocks : bSet 𝔹) :
    B_congr (fusionSectionFamily edgeColor R E b Blocks) :=
  relationGraph_domain_congr (bv_powerset omegaOne)
    (fun j A => A =ᴮ fusionSection edgeColor R E b Blocks j)

theorem activatedStages_congr_stage (ν : bSet 𝔹) :
    B_congr (fun ξ => activatedStages ξ ν) :=
  B_congr_comprehend (ϕ := fun j => ν ∈ᴮ j) (H_congr := B_ext_mem_right)

theorem fusionRowHistory_congr_stage (X ν : bSet 𝔹) :
    B_congr (fun ξ => rowHistory ξ X ν) :=
  relationGraph_domain_congr omegaOne (fun j v => pair (pair j ν) v ∈ᴮ X)

theorem fusionRowHistory_congr_coordinates (ξ ν : bSet 𝔹) :
    B_congr (fun X => rowHistory ξ X ν) :=
  relationGraph_parameter_congr ξ omegaOne
    (fun X j v => pair (pair j ν) v ∈ᴮ X) (fun _ _ => B_ext_mem_right)

theorem indexedIntersection_congr_family (κ D : bSet 𝔹) :
    B_congr (fun F => indexedIntersection κ F D) :=
  comprehend_parameter_congr κ
    (fun F z => ⨅ j, ⨅ A, _root_.imp (j ∈ᴮ D ⊓ pair j A ∈ᴮ F) (z ∈ᴮ A))
    (fun _ => B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_mem_left))))
    (fun _ => B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_inf B_ext_const B_ext_mem_right) (h₂ := B_ext_const))))

theorem rowCandidates_congr_seed (D F h : bSet 𝔹) :
    B_congr (fun seed => rowCandidates D seed F h) := by
  intro seed other Γ H
  exact difference_congr_both bv_refl
    (binary_union_congr_both (difference_congr_right H) bv_refl)

theorem rowCandidates_congr_family (D seed h : bSet 𝔹) :
    B_congr (fun F => rowCandidates D seed F h) := by
  intro F G Γ H
  exact difference_congr_both (indexedIntersection_congr_family omegaOne D H) bv_refl

theorem fusionRowCandidates_congr_object
    (edgeColor : Bool) (R E top ξ ν Blocks X : bSet 𝔹) :
    B_congr (fun b => fusionRowCandidates edgeColor R E b top ξ ν Blocks X) := by
  intro b c Γ H
  exact bv_trans
    (rowCandidates_congr_seed (activatedStages ξ ν)
      (fusionSectionFamily edgeColor R E b Blocks ξ) (rowHistory ξ X ν)
      (fusionSeed_congr_object edgeColor R E top H))
    (rowCandidates_congr_family (activatedStages ξ ν) (fusionSeed edgeColor R E c top)
      (rowHistory ξ X ν) (fusionSectionFamily_congr_object edgeColor R E Blocks ξ H))

theorem fusionRowCandidates_congr_top
    (edgeColor : Bool) (R E b ξ ν Blocks X : bSet 𝔹) :
    B_congr (fun top => fusionRowCandidates edgeColor R E b top ξ ν Blocks X) := by
  intro top other Γ H
  exact rowCandidates_congr_seed (activatedStages ξ ν)
    (fusionSectionFamily edgeColor R E b Blocks ξ) (rowHistory ξ X ν)
    (fusionSeed_congr_top edgeColor R E b H)

theorem fusionRowCandidates_congr_stage
    (edgeColor : Bool) (R E b top ν Blocks X : bSet 𝔹) :
    B_congr (fun ξ => fusionRowCandidates edgeColor R E b top ξ ν Blocks X) := by
  intro ξ η Γ H
  exact bv_trans
    (ErdosRowCandidates.rowCandidates_congr_stage (fusionSeed edgeColor R E b top)
      (fusionSectionFamily edgeColor R E b Blocks ξ) (rowHistory ξ X ν)
      (activatedStages_congr_stage ν H))
    (bv_trans
      (rowCandidates_congr_family (activatedStages η ν) (fusionSeed edgeColor R E b top)
        (rowHistory ξ X ν) (fusionSectionFamily_congr_domain edgeColor R E b Blocks H))
      (rowCandidates_congr_graph (activatedStages η ν) (fusionSeed edgeColor R E b top)
        (fusionSectionFamily edgeColor R E b Blocks η) (fusionRowHistory_congr_stage X ν H)))

theorem fusionRowCandidates_congr_blocks
    (edgeColor : Bool) (R E b top ξ ν X : bSet 𝔹) :
    B_congr (fun Blocks => fusionRowCandidates edgeColor R E b top ξ ν Blocks X) := by
  intro Blocks Other Γ H
  exact rowCandidates_congr_family (activatedStages ξ ν) (fusionSeed edgeColor R E b top)
    (rowHistory ξ X ν) (fusionSectionFamily_congr_blocks edgeColor R E b ξ H)

theorem fusionRowCandidates_congr_coordinates
    (edgeColor : Bool) (R E b top ξ ν Blocks : bSet 𝔹) :
    B_congr (fusionRowCandidates edgeColor R E b top ξ ν Blocks) := by
  intro X Y Γ H
  exact rowCandidates_congr_graph (activatedStages ξ ν) (fusionSeed edgeColor R E b top)
    (fusionSectionFamily edgeColor R E b Blocks ξ) (fusionRowHistory_congr_coordinates ξ ν H)

/-- Every mutable input may change by local Boolean equality at once.
The coloring and the one fixed canonical enumeration remain the same. -/
theorem fusionRowCandidates_congr
    {edgeColor : Bool} {R E b c top other ξ η ν μ Blocks Other X Y : bSet 𝔹} {Γ : 𝔹}
    (Hbc : Γ ≤ b =ᴮ c) (Htop : Γ ≤ top =ᴮ other) (Hξη : Γ ≤ ξ =ᴮ η)
    (Hνμ : Γ ≤ ν =ᴮ μ) (HBlocks : Γ ≤ Blocks =ᴮ Other) (HXY : Γ ≤ X =ᴮ Y) :
    Γ ≤ fusionRowCandidates edgeColor R E b top ξ ν Blocks X =ᴮ
      fusionRowCandidates edgeColor R E c other η μ Other Y :=
  bv_trans (fusionRowCandidates_congr_object edgeColor R E top ξ ν Blocks X Hbc)
    (bv_trans (fusionRowCandidates_congr_top edgeColor R E c ξ ν Blocks X Htop)
      (bv_trans (fusionRowCandidates_congr_stage edgeColor R E c other ν Blocks X Hξη)
        (bv_trans (fusionRowCandidates_congr_row edgeColor R E c other η Blocks X Hνμ)
          (bv_trans (fusionRowCandidates_congr_blocks edgeColor R E c other η μ X HBlocks)
            (fusionRowCandidates_congr_coordinates edgeColor R E c other η μ Other HXY)))))

theorem fusionRowCandidates_of_history_congr_blocks
    (edgeColor : Bool) (R E top ξ ν X : bSet 𝔹) :
    B_congr (fun Blocks => fusionRowCandidates edgeColor R E
      (graphValue (bv_powerset omegaTwo) Blocks ν) top ξ ν Blocks X) := by
  intro Blocks Other Γ H
  exact fusionRowCandidates_congr (graphValue_congr_graph (bv_powerset omegaTwo) ν H)
    bv_refl bv_refl bv_refl H bv_refl

end bSet.ErdosFusionRowCandidates
