/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalBlockPoolRunIncreasing
public import Erdos1172.Part4InternalBlockPoolSmallInvariant

@[expose] public section

/-!
# Capturing histories and closing the actual final pools

The final pools are the actual component unions of the constructed run.
They agree with the unions of its actual coordinate families. Explicit
countable boundedness of omega-one captures both internal countable
histories in one stored state. A genuinely later stage then contains the
fixed selector's output, retaining successful whole objects and all points
of every output. No supplied closed pool or successful run is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosBlockPoolFinalClosure

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosCanonicalBlocks ErdosPoolAggregation ErdosBlockPoolRecursion
open ErdosBlockPoolUpdate ErdosBlockPoolRunIncreasing ErdosBlockPoolSmallInvariant
open ErdosBoundedImageRecursion ErdosCountableChainCapture ErdosCountablyBoundedSup
open ErdosOmegaOneIdealBounded ErdosSmallFamilyUnion ErdosCountableSubsetCodes
open ErdosBlockSelector ErdosBlockSelectorPool ErdosCountableChoicePoolStep

def finalObjects (color : Bool) (R Run : bSet 𝔹) : bSet 𝔹 :=
  priorObjects color R (image omegaOne (stateSpace color R) Run)

def finalPoints (color : Bool) (R Run : bSet 𝔹) : bSet 𝔹 :=
  priorPoints color R (image omegaOne (stateSpace color R) Run)

theorem finalObjects_subset {color : Bool} {R Run : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ finalObjects color R Run ⊆ᴮ blockObjects color R := aggregateLeft_subset

theorem finalPoints_subset {color : Bool} {R Run : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ finalPoints color R Run ⊆ᴮ omegaTwo := aggregateRight_subset

theorem state_objects_subset_final {color : Bool} {R Run i B P : bSet 𝔹} {Γ : 𝔹}
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hpair : Γ ≤ pair i (pair B P) ∈ᴮ Run) :
    Γ ≤ B ⊆ᴮ finalObjects color R Run :=
  left_subset_aggregate image_subset
    (mem_image Hpair (mem_domain_of_is_function Hpair HRun)
      (mem_codomain_of_is_function Hpair HRun))

theorem state_points_subset_final {color : Bool} {R Run i B P : bSet 𝔹} {Γ : 𝔹}
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hpair : Γ ≤ pair i (pair B P) ∈ᴮ Run) :
    Γ ≤ P ⊆ᴮ finalPoints color R Run :=
  right_subset_aggregate image_subset
    (mem_image Hpair (mem_domain_of_is_function Hpair HRun)
      (mem_codomain_of_is_function Hpair HRun))

theorem finalObjects_eq_coordinate_union {color : Bool} {R Run : bSet 𝔹} {Γ : 𝔹}
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run) :
    Γ ≤ finalObjects color R Run =ᴮ
      bv_union (image omegaOne (bv_powerset (blockObjects color R)) (objectFamily HRun)) := by
  apply mem_ext
  · apply le_iInf
    intro x
    rw [← deduction]
    let Δ := Γ ⊓ x ∈ᴮ finalObjects color R Run
    obtain ⟨B, P, Hstate, HB, _, Hx⟩ := aggregateLeft_witness
      (show Δ ≤ x ∈ᴮ finalObjects color R Run from inf_le_right)
    obtain ⟨i, Hi⟩ := exists_convert ((mem_image_iff.mp Hstate).2)
      (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    have Hfamily : Δ ≤ pair i B ∈ᴮ objectFamily HRun :=
      objectFamily_pair (inf_le_left.trans HRun) (Hi.trans inf_le_right)
    exact mem_bv_union_iff.mpr (le_iSup_of_le B
      (le_inf (mem_image Hfamily (Hi.trans inf_le_left) (mem_powerset_iff.mpr HB)) Hx))
  · apply le_iInf
    intro x
    rw [← deduction]
    let Δ := Γ ⊓ x ∈ᴮ bv_union
      (image omegaOne (bv_powerset (blockObjects color R)) (objectFamily HRun))
    obtain ⟨i, B, Hx⟩ := exists_indexed_union_witness
      (show Δ ≤ x ∈ᴮ bv_union
        (image omegaOne (bv_powerset (blockObjects color R)) (objectFamily HRun)) from
        inf_le_right)
    obtain ⟨P, Hpair⟩ := objectFamily_witness HRun
      (Hx.trans (inf_le_left.trans inf_le_right))
    exact mem_of_mem_subset (state_objects_subset_final (inf_le_left.trans HRun) Hpair)
      (Hx.trans inf_le_right)

theorem finalPoints_eq_coordinate_union {color : Bool} {R Run : bSet 𝔹} {Γ : 𝔹}
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run) :
    Γ ≤ finalPoints color R Run =ᴮ
      bv_union (image omegaOne (bv_powerset omegaTwo) (pointFamily HRun)) := by
  apply mem_ext
  · apply le_iInf
    intro x
    rw [← deduction]
    let Δ := Γ ⊓ x ∈ᴮ finalPoints color R Run
    obtain ⟨B, P, Hstate, _, HP, Hx⟩ := aggregateRight_witness
      (show Δ ≤ x ∈ᴮ finalPoints color R Run from inf_le_right)
    obtain ⟨i, Hi⟩ := exists_convert ((mem_image_iff.mp Hstate).2)
      (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    have Hfamily : Δ ≤ pair i P ∈ᴮ pointFamily HRun :=
      pointFamily_pair (inf_le_left.trans HRun) (Hi.trans inf_le_right)
    exact mem_bv_union_iff.mpr (le_iSup_of_le P
      (le_inf (mem_image Hfamily (Hi.trans inf_le_left) (mem_powerset_iff.mpr HP)) Hx))
  · apply le_iInf
    intro x
    rw [← deduction]
    let Δ := Γ ⊓ x ∈ᴮ bv_union (image omegaOne (bv_powerset omegaTwo) (pointFamily HRun))
    obtain ⟨i, P, Hx⟩ := exists_indexed_union_witness
      (show Δ ≤ x ∈ᴮ bv_union
        (image omegaOne (bv_powerset omegaTwo) (pointFamily HRun)) from inf_le_right)
    obtain ⟨B, Hpair⟩ := pointFamily_witness HRun
      (Hx.trans (inf_le_left.trans inf_le_right))
    exact mem_of_mem_subset (state_points_subset_final (inf_le_left.trans HRun) Hpair)
      (Hx.trans inf_le_right)

theorem exists_object_history_stage
    {color : Bool} {R F Run T : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ countablyBounded omegaOne)
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hrec : Γ ≤ imageRecLaw (stateSpace color R)
      (fun _ U => poolUpdate color R F U) Run)
    (HT : Γ ≤ T ⊆ᴮ finalObjects color R Run) (Hcount : Γ ≤ injects_into T bSet.omega) :
    ∃ i B : bSet 𝔹, Γ ≤ i ∈ᴮ omegaOne ⊓ (pair i B ∈ᴮ objectFamily HRun ⊓ T ⊆ᴮ B) :=
  exists_family_value_containing_countable HB (objectFamily_is_function HRun)
    (objectFamily_increasing HRun Hrec)
    (bv_rw'' (ϕ := fun X => T ⊆ᴮ X) (finalObjects_eq_coordinate_union HRun) HT
      B_ext_subset_right) Hcount

theorem exists_point_history_stage
    {color : Bool} {R F Run T : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ countablyBounded omegaOne)
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hrec : Γ ≤ imageRecLaw (stateSpace color R)
      (fun _ U => poolUpdate color R F U) Run)
    (HT : Γ ≤ T ⊆ᴮ finalPoints color R Run) (Hcount : Γ ≤ injects_into T bSet.omega) :
    ∃ i P : bSet 𝔹, Γ ≤ i ∈ᴮ omegaOne ⊓ (pair i P ∈ᴮ pointFamily HRun ⊓ T ⊆ᴮ P) :=
  exists_family_value_containing_countable HB (pointFamily_is_function HRun)
    (pointFamily_increasing HRun Hrec)
    (bv_rw'' (ϕ := fun X => T ⊆ᴮ X) (finalPoints_eq_coordinate_union HRun) HT
      B_ext_subset_right) Hcount

private theorem ordinal_subset_mem {a b c : bSet 𝔹} {Γ : 𝔹}
    (Ha : Γ ≤ Ord a) (Hb : Γ ≤ Ord b) (Hc : Γ ≤ Ord c)
    (Hab : Γ ≤ a ⊆ᴮ b) (Hbc : Γ ≤ b ∈ᴮ c) : Γ ≤ a ∈ᴮ c := by
  have Hcases := (Ord.le_iff_lt_or_eq Ha Hb).mp Hab
  apply (le_inf (le_refl Γ) Hcases).trans
  rw [inf_sup_left]
  exact sup_le (mem_of_mem_Ord inf_le_right (inf_le_left.trans Hbc) (inf_le_left.trans Hc))
    (mem_congr (bv_symm inf_le_right) bv_refl (inf_le_left.trans Hbc))

/-- Boolean ordinal comparison and fullness give one common strict upper
stage without deciding an external comparison branch. -/
theorem exists_above_two_stages {i j : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ countablyBounded omegaOne)
    (Hi : Γ ≤ i ∈ᴮ omegaOne) (Hj : Γ ≤ j ∈ᴮ omegaOne) :
    ∃ k : bSet 𝔹, Γ ≤ k ∈ᴮ omegaOne ⊓ (i ∈ᴮ k ⊓ j ∈ᴮ k) := by
  have HiOrd := Ord_of_mem_Ord Hi omegaOne_Ord
  have HjOrd := Ord_of_mem_Ord Hj omegaOne_Ord
  have Hcases := Ord.le_or_le HiOrd HjOrd
  have Hex : Γ ≤ ⨆ k, k ∈ᴮ omegaOne ⊓ (i ∈ᴮ k ⊓ j ∈ᴮ k) := by
    apply (le_inf (le_refl Γ) Hcases).trans
    rw [inf_sup_left]
    apply sup_le
    · obtain ⟨k, Hk⟩ := exists_above_of_countablyBounded
        (inf_le_left.trans HB) (inf_le_left.trans Hj)
      exact le_iSup_of_le k (le_inf (Hk.trans inf_le_left)
        (le_inf (ordinal_subset_mem (inf_le_left.trans HiOrd) (inf_le_left.trans HjOrd)
          (Ord_of_mem_Ord (Hk.trans inf_le_left) omegaOne_Ord)
          inf_le_right (Hk.trans inf_le_right)) (Hk.trans inf_le_right)))
    · obtain ⟨k, Hk⟩ := exists_above_of_countablyBounded
        (inf_le_left.trans HB) (inf_le_left.trans Hi)
      exact le_iSup_of_le k (le_inf (Hk.trans inf_le_left)
        (le_inf (Hk.trans inf_le_right)
          (ordinal_subset_mem (inf_le_left.trans HjOrd) (inf_le_left.trans HiOrd)
            (Ord_of_mem_Ord (Hk.trans inf_le_left) omegaOne_Ord)
            inf_le_right (Hk.trans inf_le_right))))
  exact exists_convert Hex (B_ext_inf B_ext_mem_left (B_ext_inf B_ext_mem_right B_ext_mem_right))

theorem exists_pool_state {color : Bool} {R Run i : bSet 𝔹} {Γ : 𝔹}
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hi : Γ ≤ i ∈ᴮ omegaOne) :
    ∃ B P : bSet 𝔹, Γ ≤ pair i (pair B P) ∈ᴮ Run := by
  have Hex : Γ ≤ ⨆ q, q ∈ᴮ stateSpace color R ⊓ pair i q ∈ᴮ Run :=
    (le_inf ((is_total_of_is_function HRun).trans (iInf_le _ i)) Hi).trans bv_imp_elim
  obtain ⟨q, Hq⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  obtain ⟨B, _, P, _, Heq⟩ := mem_prod_iff₂.mp (Hq.trans inf_le_left)
  exact ⟨B, P, mem_congr (pair_congr bv_refl Heq) bv_refl (Hq.trans inf_le_right)⟩

theorem exists_joint_history_stage
    {color : Bool} {R F Run Earlier Active : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ countablyBounded omegaOne)
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hrec : Γ ≤ imageRecLaw (stateSpace color R)
      (fun _ T => poolUpdate color R F T) Run)
    (HEarlier : Γ ≤ Earlier ∈ᴮ countableSubsets (finalObjects color R Run))
    (HActive : Γ ≤ Active ∈ᴮ countableSubsets (finalPoints color R Run)) :
    ∃ i B P : bSet 𝔹, Γ ≤ i ∈ᴮ omegaOne ∧ Γ ≤ pair i (pair B P) ∈ᴮ Run ∧
      Γ ≤ Earlier ⊆ᴮ B ∧ Γ ≤ Active ⊆ᴮ P := by
  have HE := mem_countableSubsets_iff.mp HEarlier
  have HA := mem_countableSubsets_iff.mp HActive
  obtain ⟨i, B, Hi⟩ := exists_object_history_stage HB HRun Hrec HE.1 HE.2
  obtain ⟨j, Q, Hj⟩ := exists_point_history_stage HB HRun Hrec HA.1 HA.2
  obtain ⟨P, Hipair⟩ := objectFamily_witness HRun (Hi.trans (inf_le_right.trans inf_le_left))
  obtain ⟨C, Hjpair⟩ := pointFamily_witness HRun (Hj.trans (inf_le_right.trans inf_le_left))
  obtain ⟨k, Hk⟩ := exists_above_two_stages HB (Hi.trans inf_le_left) (Hj.trans inf_le_left)
  obtain ⟨D, U, Hkpair⟩ := exists_pool_state HRun (Hk.trans inf_le_left)
  have Hiinc := pool_recursion_increasing HRun Hrec
    (Hk.trans (inf_le_right.trans inf_le_left)) Hipair Hkpair
  have Hjinc := pool_recursion_increasing HRun Hrec
    (Hk.trans (inf_le_right.trans inf_le_right)) Hjpair Hkpair
  exact ⟨k, D, U, Hk.trans inf_le_left, Hkpair,
    subset_trans' (Hi.trans (inf_le_right.trans inf_le_right)) (Hiinc.trans inf_le_left),
    subset_trans' (Hj.trans (inf_le_right.trans inf_le_right)) (Hjinc.trans inf_le_right)⟩

/-- Closure includes every output's entire point set; a nonempty output
is also retained as a whole object. Both implications stay at the same
condition, including mixed success and failure. -/
theorem selected_output_in_final_pools
    {color : Bool} {R J E S F Run Earlier Active A : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ countablyBounded omegaOne)
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hrec : Γ ≤ imageRecLaw (stateSpace color R)
      (fun _ T => poolUpdate color R F T) Run)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HEarlier : Γ ≤ Earlier ∈ᴮ countableSubsets (finalObjects color R Run))
    (HActive : Γ ≤ Active ∈ᴮ countableSubsets (finalPoints color R Run))
    (Hselected : Γ ≤ pair (pair Earlier Active) A ∈ᴮ F) :
    Γ ≤ (A ⊆ᴮ finalPoints color R Run) ⊓
      _root_.imp ((A =ᴮ (∅ : bSet 𝔹))ᶜ) (A ∈ᴮ finalObjects color R Run) := by
  obtain ⟨i, B, P, Hi, Hstate, HEB, HAP⟩ :=
    exists_joint_history_stage HB HRun Hrec HEarlier HActive
  obtain ⟨j, Hj⟩ := exists_above_of_countablyBounded HB Hi
  obtain ⟨C, Q, Hjstate⟩ := exists_pool_state HRun (Hj.trans inf_le_left)
  let T := image j (stateSpace color R) Run
  let B₀ := priorObjects color R T
  let P₀ := priorPoints color R T
  have Hpast : Γ ≤ pair B P ∈ᴮ T :=
    mem_image Hstate (Hj.trans inf_le_right) (mem_codomain_of_is_function Hstate HRun)
  have HEB₀ : Γ ≤ Earlier ⊆ᴮ B₀ :=
    subset_trans' HEB (left_subset_aggregate image_subset Hpast)
  have HAP₀ : Γ ≤ Active ⊆ᴮ P₀ :=
    subset_trans' HAP (right_subset_aggregate image_subset Hpast)
  have HEcount : Γ ≤ Earlier ∈ᴮ countableSubsets B₀ :=
    mem_countableSubsets_iff.mpr ⟨HEB₀, (mem_countableSubsets_iff.mp HEarlier).2⟩
  have HAcount : Γ ≤ Active ∈ᴮ countableSubsets P₀ :=
    mem_countableSubsets_iff.mpr ⟨HAP₀, (mem_countableSubsets_iff.mp HActive).2⟩
  have Hentry := pool_recursion_entry Hrec Hjstate
  have HpointNext : Γ ≤ A ⊆ᴮ nextPoints B₀ P₀ F :=
    subset_trans' (selected_value_subset_selectedPoints
      (selector_local_is_func' HF aggregateLeft_subset aggregateRight_subset)
      HEcount HAcount Hselected)
      (selectedPoints_subset_nextPoints aggregateLeft_subset aggregateRight_subset)
  have HAQ : Γ ≤ A ⊆ᴮ Q :=
    bv_rw' (ϕ := fun X => A ⊆ᴮ X) (Hentry.trans inf_le_right)
      (h_congr := B_ext_subset_right) (H_new := HpointNext)
  refine le_inf (subset_trans' HAQ (state_points_subset_final HRun Hjstate)) ?_
  rw [← deduction]
  let Δ := Γ ⊓ (A =ᴮ (∅ : bSet 𝔹))ᶜ
  have Hsuccess : Δ ≤ A ∈ᴮ successfulObjects color R B₀ P₀ F :=
    nonempty_selected_value_mem_successful (inf_le_left.trans HF) (inf_le_left.trans Hlaw)
      aggregateLeft_subset aggregateRight_subset (inf_le_left.trans HEcount)
      (inf_le_left.trans HAcount) (inf_le_left.trans Hselected) inf_le_right
  have Hnext : Δ ≤ A ∈ᴮ nextObjects color R B₀ P₀ F :=
    mem_of_mem_subset successfulObjects_subset_nextObjects Hsuccess
  have HAC : Δ ≤ A ∈ᴮ C :=
    mem_congr bv_refl (bv_symm (inf_le_left.trans (Hentry.trans inf_le_left))) Hnext
  exact mem_of_mem_subset (inf_le_left.trans (state_objects_subset_final HRun Hjstate)) HAC

theorem selected_value_subset_finalPoints
    {color : Bool} {R J E S F Run Earlier Active A : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ countablyBounded omegaOne)
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hrec : Γ ≤ imageRecLaw (stateSpace color R)
      (fun _ T => poolUpdate color R F T) Run)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HEarlier : Γ ≤ Earlier ∈ᴮ countableSubsets (finalObjects color R Run))
    (HActive : Γ ≤ Active ∈ᴮ countableSubsets (finalPoints color R Run))
    (Hselected : Γ ≤ pair (pair Earlier Active) A ∈ᴮ F) :
    Γ ≤ A ⊆ᴮ finalPoints color R Run :=
  (selected_output_in_final_pools HB HRun Hrec HF Hlaw HEarlier HActive Hselected).trans
    inf_le_left

theorem nonempty_selected_value_mem_finalObjects
    {color : Bool} {R J E S F Run Earlier Active A : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ countablyBounded omegaOne)
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hrec : Γ ≤ imageRecLaw (stateSpace color R)
      (fun _ T => poolUpdate color R F T) Run)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HEarlier : Γ ≤ Earlier ∈ᴮ countableSubsets (finalObjects color R Run))
    (HActive : Γ ≤ Active ∈ᴮ countableSubsets (finalPoints color R Run))
    (Hselected : Γ ≤ pair (pair Earlier Active) A ∈ᴮ F)
    (Hnonempty : Γ ≤ (A =ᴮ (∅ : bSet 𝔹))ᶜ) :
    Γ ≤ A ∈ᴮ finalObjects color R Run :=
  (le_inf ((selected_output_in_final_pools HB HRun Hrec HF Hlaw HEarlier HActive
    Hselected).trans inf_le_right) Hnonempty).trans bv_imp_elim

theorem final_pools_small {color : Bool} {R J E S F Run : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hrec : Γ ≤ imageRecLaw (stateSpace color R)
      (fun _ T => poolUpdate color R F T) Run) :
    Γ ≤ injects_into (finalObjects color R Run) omegaOne ⊓
      injects_into (finalPoints color R Run) omegaOne :=
  pool_final_aggregates_small HCH HF Hlaw HRun Hrec

end bSet.ErdosBlockPoolFinalClosure
