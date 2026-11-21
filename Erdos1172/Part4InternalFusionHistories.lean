/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCanonicalBlockEnumeration
public import Erdos1172.Part4InternalBoundedFunctionValue

@[expose] public section

/-!
# Actual whole-block and current-point histories for ordered fusion

The same fixed enumeration graph supplies the physical point of each
successful old row. Failed rows are separated out before taking the
point image; no fallback physical point is added to the active history.
All constructions are internal and support arbitrary mixed histories.
Countability is derived from the actual stage domain, not supplied as a
property of an externally enumerated collection. Current points do not
depend on whether the next block selector succeeds.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionHistories

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosCanonicalBlocks ErdosBoundedFunctionValue
open ErdosRelationGraph ErdosCountableImage

def blockValue (Blocks ν : bSet 𝔹) : bSet 𝔹 :=
  graphValue (bv_powerset omegaTwo) Blocks ν

def rowValue (E Blocks ν : bSet 𝔹) : bSet 𝔹 :=
  graphValue blockEnumerationCodes E (blockValue Blocks ν)

def currentPoint (E Blocks Z ν : bSet 𝔹) : bSet 𝔹 :=
  graphValue omegaTwo (rowValue E Blocks ν) (graphValue omegaOne Z ν)

theorem blockValue_congr (Blocks : bSet 𝔹) : B_congr (blockValue Blocks) :=
  graphValue_congr_input _ _

theorem rowValue_congr (E Blocks : bSet 𝔹) : B_congr (rowValue E Blocks) := by
  intro ν μ Γ H
  exact graphValue_congr_input _ _ (blockValue_congr Blocks H)

theorem currentPoint_congr (E Blocks Z : bSet 𝔹) : B_congr (currentPoint E Blocks Z) := by
  intro ν μ Γ H
  exact bv_trans
    (graphValue_congr_graph omegaTwo (graphValue omegaOne Z ν) (rowValue_congr E Blocks H))
    (graphValue_congr_input omegaTwo (rowValue E Blocks μ) (graphValue_congr_input omegaOne Z H))

def successfulRows (color : Bool) (R ξ Blocks : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun ν => blockValue Blocks ν ∈ᴮ blockObjects color R) ξ

theorem mem_successfulRows_iff {color : Bool} {R ξ Blocks ν : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ ν ∈ᴮ successfulRows color R ξ Blocks ↔
      Γ ≤ ν ∈ᴮ ξ ∧ Γ ≤ blockValue Blocks ν ∈ᴮ blockObjects color R :=
  mem_comprehend_and (B_ext_term _ _ B_ext_mem_left (blockValue_congr Blocks))

theorem successfulRows_subset {color : Bool} {R ξ Blocks : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ successfulRows color R ξ Blocks ⊆ᴮ ξ :=
  comprehend_subset (ϕ := fun ν => blockValue Blocks ν ∈ᴮ blockObjects color R) ξ

theorem currentPoint_spec {color : Bool} {R E Blocks Z ν : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HZ : Γ ≤ is_function omegaOne omegaOne Z)
    (Hν : Γ ≤ ν ∈ᴮ omegaOne)
    (HA : Γ ≤ blockValue Blocks ν ∈ᴮ blockObjects color R) :
    Γ ≤ currentPoint E Blocks Z ν ∈ᴮ omegaTwo ⊓
      (pair (graphValue omegaOne Z ν) (currentPoint E Blocks Z ν) ∈ᴮ
        rowValue E Blocks ν ⊓ currentPoint E Blocks Z ν ∈ᴮ blockValue Blocks ν) := by
  have Hr : Γ ≤ blockEnumerationData color R (blockValue Blocks ν) (rowValue E Blocks ν) :=
    blockEnumerationFamilyLaw_apply HElaw HA (graphValue_pair_mem HE HA)
  have Hv : Γ ≤ graphValue omegaOne Z ν ∈ᴮ omegaOne := graphValue_mem HZ Hν
  have Hpoint := graphValue_spec (Hr.trans (inf_le_left.trans inf_le_left)) Hv
  have Himage : Γ ≤ currentPoint E Blocks Z ν ∈ᴮ
      image omegaOne omegaTwo (rowValue E Blocks ν) :=
    mem_image (Hpoint.trans inf_le_right) Hv (Hpoint.trans inf_le_left)
  exact le_inf (Hpoint.trans inf_le_left) (le_inf (Hpoint.trans inf_le_right)
    (mem_congr bv_refl (Hr.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))) Himage))

/-- The point equals the value of the original selected enumeration at
the original current coordinate, not a newly chosen row enumeration. -/
theorem currentPoint_eq_of_pairs
    {color : Bool} {R E ξ Blocks Z ν A r v x : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HBlocks : Γ ≤ is_function ξ (bv_powerset omegaTwo) Blocks)
    (HZ : Γ ≤ is_function omegaOne omegaOne Z)
    (HνA : Γ ≤ pair ν A ∈ᴮ Blocks) (HAr : Γ ≤ pair A r ∈ᴮ E)
    (Hνv : Γ ≤ pair ν v ∈ᴮ Z) (Hvx : Γ ≤ pair v x ∈ᴮ r) :
    Γ ≤ currentPoint E Blocks Z ν =ᴮ x := by
  have HA : Γ ≤ blockValue Blocks ν =ᴮ A := graphValue_eq_of_pair HBlocks HνA
  have Hr : Γ ≤ rowValue E Blocks ν =ᴮ r :=
    bv_trans (graphValue_congr_input _ _ HA) (graphValue_eq_of_pair HE HAr)
  have Hv : Γ ≤ graphValue omegaOne Z ν =ᴮ v := graphValue_eq_of_pair HZ Hνv
  have Hdata := selected_enumeration_data HE HElaw HAr
  exact bv_trans (graphValue_congr_graph omegaTwo _ Hr)
    (bv_trans (graphValue_congr_input omegaTwo r Hv)
      (graphValue_eq_of_pair (Hdata.trans (inf_le_left.trans inf_le_left)) Hvx))

def currentPointGraph (color : Bool) (R E ξ Blocks Z : bSet 𝔹) : bSet 𝔹 :=
  relationGraph (successfulRows color R ξ Blocks) omegaTwo
    (fun ν x => x =ᴮ currentPoint E Blocks Z ν)

theorem currentPointGraph_is_function
    {color : Bool} {R E ξ Blocks Z : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HZ : Γ ≤ is_function omegaOne omegaOne Z) (Hξ : Γ ≤ ξ ⊆ᴮ omegaOne) :
    Γ ≤ is_function (successfulRows color R ξ Blocks) omegaTwo
      (currentPointGraph color R E ξ Blocks Z) := by
  apply relationGraph_is_function
    (fun x => B_ext_term _ _ B_ext_bv_eq_right (currentPoint_congr E Blocks Z))
    (fun _ => B_ext_bv_eq_left)
  · apply le_iInf
    intro ν
    rw [← deduction]
    have Hparts := mem_successfulRows_iff.mp
      (show Γ ⊓ ν ∈ᴮ successfulRows color R ξ Blocks ≤
        ν ∈ᴮ successfulRows color R ξ Blocks from inf_le_right)
    exact le_iSup_of_le (currentPoint E Blocks Z ν)
      (le_inf ((currentPoint_spec (inf_le_left.trans HE) (inf_le_left.trans HElaw)
        (inf_le_left.trans HZ) (mem_of_mem_subset (inf_le_left.trans Hξ) Hparts.1)
        Hparts.2).trans inf_le_left) bv_refl)
  · intro ν μ x y Δ _ _ _ _ _ Hx Hy Hνμ
    exact bv_trans Hx (bv_trans (currentPoint_congr E Blocks Z Hνμ) (bv_symm Hy))

theorem currentPointGraph_pair
    {color : Bool} {R E ξ Blocks Z ν : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HZ : Γ ≤ is_function omegaOne omegaOne Z) (Hξ : Γ ≤ ξ ⊆ᴮ omegaOne)
    (Hν : Γ ≤ ν ∈ᴮ successfulRows color R ξ Blocks) :
    Γ ≤ pair ν (currentPoint E Blocks Z ν) ∈ᴮ currentPointGraph color R E ξ Blocks Z := by
  have Hparts := mem_successfulRows_iff.mp Hν
  exact (mem_relationGraph_iff
    (fun x => B_ext_term _ _ B_ext_bv_eq_right (currentPoint_congr E Blocks Z))
    (fun _ => B_ext_bv_eq_left)).mpr
    ⟨Hν, (currentPoint_spec HE HElaw HZ (mem_of_mem_subset Hξ Hparts.1)
      Hparts.2).trans inf_le_left, bv_refl⟩

def currentPoints (color : Bool) (R E ξ Blocks Z : bSet 𝔹) : bSet 𝔹 :=
  image (successfulRows color R ξ Blocks) omegaTwo
    (currentPointGraph color R E ξ Blocks Z)

theorem currentPoints_subset {color : Bool} {R E ξ Blocks Z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ currentPoints color R E ξ Blocks Z ⊆ᴮ omegaTwo := image_subset

theorem currentPoints_countable
    {color : Bool} {R E ξ Blocks Z : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HZ : Γ ≤ is_function omegaOne omegaOne Z) (Hξ : Γ ≤ ξ ⊆ᴮ omegaOne)
    (Hcount : Γ ≤ injects_into ξ bSet.omega) :
    Γ ≤ injects_into (currentPoints color R E ξ Blocks Z) bSet.omega :=
  image_countable_of_function (currentPointGraph_is_function HE HElaw HZ Hξ)
    (injects_into_trans (injects_into_of_subset successfulRows_subset) Hcount)

theorem currentPoint_mem_currentPoints
    {color : Bool} {R E ξ Blocks Z ν : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HZ : Γ ≤ is_function omegaOne omegaOne Z) (Hξ : Γ ≤ ξ ⊆ᴮ omegaOne)
    (Hν : Γ ≤ ν ∈ᴮ successfulRows color R ξ Blocks) :
    Γ ≤ currentPoint E Blocks Z ν ∈ᴮ currentPoints color R E ξ Blocks Z :=
  mem_image (currentPointGraph_pair HE HElaw HZ Hξ Hν) Hν
    ((currentPoint_spec HE HElaw HZ
      (mem_of_mem_subset Hξ (mem_successfulRows_iff.mp Hν).1)
      (mem_successfulRows_iff.mp Hν).2).trans inf_le_left)

def earlierHistory (color : Bool) (R ξ Blocks : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun A => A ∈ᴮ blockObjects color R)
    (image ξ (bv_powerset omegaTwo) Blocks)

theorem earlierHistory_subset {color : Bool} {R ξ Blocks : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ earlierHistory color R ξ Blocks ⊆ᴮ blockObjects color R := by
  rw [subset_unfold']
  apply le_iInf
  intro A
  rw [← deduction]
  exact ((mem_comprehend_and B_ext_mem_left).mp
    (show Γ ⊓ A ∈ᴮ earlierHistory color R ξ Blocks ≤
      A ∈ᴮ earlierHistory color R ξ Blocks from inf_le_right)).2

theorem earlierHistory_countable
    {color : Bool} {R ξ Blocks : bSet 𝔹} {Γ : 𝔹}
    (HBlocks : Γ ≤ is_function ξ (bv_powerset omegaTwo) Blocks)
    (Hcount : Γ ≤ injects_into ξ bSet.omega) :
    Γ ≤ injects_into (earlierHistory color R ξ Blocks) bSet.omega :=
  injects_into_trans (injects_into_of_subset
    (comprehend_subset (ϕ := fun A => A ∈ᴮ blockObjects color R)
      (image ξ (bv_powerset omegaTwo) Blocks)))
    (image_countable_of_function HBlocks Hcount)

theorem earlierHistory_mem_of_pair
    {color : Bool} {R ξ Blocks ν A : bSet 𝔹} {Γ : 𝔹}
    (HBlocks : Γ ≤ is_function ξ (bv_powerset omegaTwo) Blocks)
    (Hpair : Γ ≤ pair ν A ∈ᴮ Blocks) (HA : Γ ≤ A ∈ᴮ blockObjects color R) :
    Γ ≤ A ∈ᴮ earlierHistory color R ξ Blocks :=
  (mem_comprehend_and B_ext_mem_left).mpr
    ⟨mem_image Hpair (mem_domain_of_is_function Hpair HBlocks)
      (mem_codomain_of_is_function Hpair HBlocks), HA⟩

end bSet.ErdosFusionHistories
