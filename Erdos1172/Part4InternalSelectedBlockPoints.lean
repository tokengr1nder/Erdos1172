/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionHistories
public import Erdos1172.Part4InternalFusionRowCandidates

@[expose] public section

/-!
# Physical points selected from actual whole blocks

The proof-independent evaluator uses the same block graph, coordinate
graph, and fixed canonical enumeration. Its supported graph is defined
on an arbitrary internal domain, which may be empty. The pair theorem
retains actual same-condition block and coordinate witnesses. Whole-block
strict order transfers to the actual point function without assuming a
partition target or choosing any new enumerations.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSelectedBlockPoints

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosCanonicalBlocks ErdosFusionHistories ErdosFusionRowCandidates
open ErdosBoundedFunctionValue ErdosRelationGraph ErdosPartition

def selectedPoints (K E Blocks coords : bSet 𝔹) : bSet 𝔹 :=
  relationGraph K omegaTwo (fun i x => x =ᴮ currentPoint E Blocks coords i)

theorem mem_selectedPoints_iff {K E Blocks coords i x : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair i x ∈ᴮ selectedPoints K E Blocks coords ↔
      Γ ≤ i ∈ᴮ K ∧ Γ ≤ x ∈ᴮ omegaTwo ∧ Γ ≤ x =ᴮ currentPoint E Blocks coords i :=
  mem_relationGraph_iff
    (fun x => B_ext_term (ϕ := fun y => x =ᴮ y) (t := currentPoint E Blocks coords)
      B_ext_bv_eq_right (currentPoint_congr E Blocks coords))
    (fun _ => B_ext_bv_eq_left)

variable {color : Bool} {R K E Blocks coords : bSet 𝔹} {Γ : 𝔹}
variable (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
  (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
  (HBlocks : Γ ≤ is_function K (bv_powerset omegaTwo) Blocks)
  (Hvalues : Γ ≤ ⨅ i, ⨅ b, _root_.imp (i ∈ᴮ K ⊓ pair i b ∈ᴮ Blocks)
    (b ∈ᴮ blockObjects color R))
  (Hcoords : Γ ≤ is_function K omegaOne coords)

include HE HElaw HBlocks Hvalues Hcoords in
/-- The existing evaluator is valid on an arbitrary actual coordinate
domain; no enlargement of its graph to all of omega-one is asserted. -/
theorem currentPoint_spec_on {i : bSet 𝔹} (Hi : Γ ≤ i ∈ᴮ K) :
    Γ ≤ currentPoint E Blocks coords i ∈ᴮ omegaTwo ⊓
      (pair (graphValue omegaOne coords i) (currentPoint E Blocks coords i) ∈ᴮ
        canonicalRow E (blockValue Blocks i) ⊓
          currentPoint E Blocks coords i ∈ᴮ blockValue Blocks i) := by
  have Hb : Γ ≤ blockValue Blocks i ∈ᴮ blockObjects color R :=
    (le_inf (Hvalues.trans ((iInf_le _ i).trans (iInf_le _ (blockValue Blocks i))))
      (le_inf Hi (graphValue_pair_mem HBlocks Hi))).trans bv_imp_elim
  have Hr := canonicalRow_data HE HElaw Hb
  have Hv := graphValue_mem Hcoords Hi
  have Hpoint := graphValue_spec (Hr.trans (inf_le_left.trans inf_le_left)) Hv
  have Him : Γ ≤ currentPoint E Blocks coords i ∈ᴮ
      image omegaOne omegaTwo (canonicalRow E (blockValue Blocks i)) :=
    mem_image (Hpoint.trans inf_le_right) Hv (Hpoint.trans inf_le_left)
  exact le_inf (Hpoint.trans inf_le_left) (le_inf (Hpoint.trans inf_le_right)
    (mem_congr bv_refl (Hr.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))) Him))

include HE HElaw HBlocks Hvalues Hcoords in
theorem selectedPoints_is_function :
    Γ ≤ is_function K omegaTwo (selectedPoints K E Blocks coords) := by
  apply relationGraph_is_function
    (fun x => B_ext_term (ϕ := fun y => x =ᴮ y) (t := currentPoint E Blocks coords)
      B_ext_bv_eq_right (currentPoint_congr E Blocks coords))
    (fun _ => B_ext_bv_eq_left)
  · apply le_iInf
    intro i
    rw [← deduction]
    exact le_iSup_of_le (currentPoint E Blocks coords i)
      (le_inf ((currentPoint_spec_on (inf_le_left.trans HE) (inf_le_left.trans HElaw)
        (inf_le_left.trans HBlocks) (inf_le_left.trans Hvalues)
        (inf_le_left.trans Hcoords) inf_le_right).trans inf_le_left) bv_refl)
  · intro i j x y Δ _ _ _ _ _ Hx Hy Hij
    exact bv_trans Hx (bv_trans (currentPoint_congr E Blocks coords Hij) (bv_symm Hy))

include HE HElaw HBlocks Hvalues Hcoords in
theorem selectedPoints_witness {i x : bSet 𝔹}
    (Hpair : Γ ≤ pair i x ∈ᴮ selectedPoints K E Blocks coords) :
    ∃ b v : bSet 𝔹, Γ ≤ pair i b ∈ᴮ Blocks ∧ Γ ≤ pair i v ∈ᴮ coords ∧
      Γ ≤ pair v x ∈ᴮ canonicalRow E b := by
  have Hdata := mem_selectedPoints_iff.mp Hpair
  have Hpoint := currentPoint_spec_on HE HElaw HBlocks Hvalues Hcoords Hdata.1
  exact ⟨blockValue Blocks i, graphValue omegaOne coords i,
    graphValue_pair_mem HBlocks Hdata.1, graphValue_pair_mem Hcoords Hdata.1,
    mem_congr (pair_congr bv_refl (bv_symm Hdata.2.2)) bv_refl
      (Hpoint.trans (inf_le_right.trans inf_le_left))⟩

include HE HElaw HBlocks Hvalues Hcoords in
theorem selectedPoints_mem_block {i b x : bSet 𝔹}
    (Hpair : Γ ≤ pair i x ∈ᴮ selectedPoints K E Blocks coords)
    (Hib : Γ ≤ pair i b ∈ᴮ Blocks) : Γ ≤ x ∈ᴮ b := by
  have Hdata := mem_selectedPoints_iff.mp Hpair
  have Hpoint := currentPoint_spec_on HE HElaw HBlocks Hvalues Hcoords Hdata.1
  exact mem_congr (bv_symm Hdata.2.2) (graphValue_eq_of_pair HBlocks Hib)
    (Hpoint.trans (inf_le_right.trans inf_le_right))

include HE HElaw HBlocks Hvalues Hcoords in
/-- Strict order of the whole block values gives increasingness of the
physical-point graph, on its original actual domain. -/
theorem selectedPoints_increasingOn
    (Horder : Γ ≤ ⨅ i, ⨅ j, ⨅ b, ⨅ c, ⨅ x, ⨅ y, _root_.imp
      ((i ∈ᴮ j ⊓ (pair i b ∈ᴮ Blocks ⊓ pair j c ∈ᴮ Blocks)) ⊓ (x ∈ᴮ b ⊓ y ∈ᴮ c)) (x ∈ᴮ y)) :
    Γ ≤ increasingOn K (selectedPoints K E Blocks coords) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro j
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ (((i ∈ᴮ K ⊓ j ∈ᴮ K) ⊓ i ∈ᴮ j) ⊓
    (pair i x ∈ᴮ selectedPoints K E Blocks coords ⊓ pair j y ∈ᴮ selectedPoints K E Blocks coords))
  have HΔ : Δ ≤ Γ := inf_le_left
  have Hix : Δ ≤ pair i x ∈ᴮ selectedPoints K E Blocks coords :=
    inf_le_right.trans (inf_le_right.trans inf_le_left)
  have Hjy : Δ ≤ pair j y ∈ᴮ selectedPoints K E Blocks coords :=
    inf_le_right.trans (inf_le_right.trans inf_le_right)
  obtain ⟨b, _, Hib, _, _⟩ := selectedPoints_witness (HΔ.trans HE) (HΔ.trans HElaw)
    (HΔ.trans HBlocks) (HΔ.trans Hvalues) (HΔ.trans Hcoords) Hix
  obtain ⟨c, _, Hjc, _, _⟩ := selectedPoints_witness (HΔ.trans HE) (HΔ.trans HElaw)
    (HΔ.trans HBlocks) (HΔ.trans Hvalues) (HΔ.trans Hcoords) Hjy
  have Hxb := selectedPoints_mem_block (HΔ.trans HE) (HΔ.trans HElaw)
    (HΔ.trans HBlocks) (HΔ.trans Hvalues) (HΔ.trans Hcoords) Hix Hib
  have Hyc := selectedPoints_mem_block (HΔ.trans HE) (HΔ.trans HElaw)
    (HΔ.trans HBlocks) (HΔ.trans Hvalues) (HΔ.trans Hcoords) Hjy Hjc
  exact (le_inf (HΔ.trans (Horder.trans ((iInf_le _ i).trans
    ((iInf_le _ j).trans ((iInf_le _ b).trans ((iInf_le _ c).trans
      ((iInf_le _ x).trans (iInf_le _ y))))))))
    (le_inf (le_inf (inf_le_right.trans (inf_le_left.trans inf_le_right)) (le_inf Hib Hjc))
      (le_inf Hxb Hyc))).trans bv_imp_elim

end bSet.ErdosSelectedBlockPoints
