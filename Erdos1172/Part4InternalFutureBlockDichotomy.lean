/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSectionPullback
public import Erdos1172.Part4InternalIncreasingComposition
public import Erdos1172.Part4InternalLargeCliqueTwoBlock
public import Erdos1172.Part4InternalSimultaneousBlockDichotomy

@[expose] public section

/-!
# A simultaneous block inside an arbitrary large future

An actual increasing injection of omega-two into the supplied future is
constructed. The coloring and row sections are pulled back along that
graph, the all-endpoint simultaneous dichotomy is applied, and its actual
graphs are composed back into the future.

The original section and normal-row assumptions are guarded only by the
future name L. In particular, the output does not assert normal row
availability for the original sections on all of omega-two. The same
common-row family and every applicable original row ideal are retained.
The future need not be stationary or nonempty by a separate assumption.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFutureBlockDichotomy

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosPartition ErdosColargeIntersection
open ErdosSuccessfulRunBlock ErdosSectionPullback ErdosGraphPullback
open ErdosIncreasingComposition ErdosOrderedDushnikMiller ErdosIncreasingPartial

/-- Availability and the ideal-value law refer only to the original
future. The containment law refers to the original sections and graph. -/
def futureCommonBlockRows (S L f C : bSet 𝔹) : 𝔹 :=
  is_function omegaOne (bv_powerset omegaOne) C ⊓
    (normalRowAvailabilityOn S L ⊓
      ((⨅ σ, ⨅ J, ⨅ A, _root_.imp
        (rowNormalIdealDataOn S L σ J ⊓ pair σ A ∈ᴮ C) (colarge omegaOne J A)) ⊓
        blockRowContainment S f C))

def futureSuccessfulBlockData (color : Bool) (R S L f C : bSet 𝔹) : 𝔹 :=
  is_injective_function omegaOne L f ⊓
    (increasingOn omegaOne f ⊓
      (homogeneousUnion color R omegaOne omegaOne f f ⊓ futureCommonBlockRows S L f C))

def hasFutureSuccessfulBlock (color : Bool) (R S L : bSet 𝔹) : 𝔹 :=
  ⨆ f, ⨆ C, futureSuccessfulBlockData color R S L f C

theorem futureCommonBlockRows_colarge_apply {S L f C σ J A : bSet 𝔹} {Γ : 𝔹}
    (Hcommon : Γ ≤ futureCommonBlockRows S L f C)
    (Hdata : Γ ≤ rowNormalIdealDataOn S L σ J) (HC : Γ ≤ pair σ A ∈ᴮ C) :
    Γ ≤ colarge omegaOne J A :=
  (le_inf ((Hcommon.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))).trans
    ((iInf_le _ σ).trans ((iInf_le _ J).trans (iInf_le _ A)))) (le_inf Hdata HC)).trans bv_imp_elim

theorem futureCommonBlockRows_section_apply {S L f C σ A y B : bSet 𝔹} {Γ : 𝔹}
    (Hcommon : Γ ≤ futureCommonBlockRows S L f C) (HC : Γ ≤ pair σ A ∈ᴮ C)
    (Hy : Γ ≤ rangeMem omegaOne f y) (HB : Γ ≤ pair (pair σ y) B ∈ᴮ S) :
    Γ ≤ A ⊆ᴮ B :=
  (le_inf ((Hcommon.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))).trans
    ((iInf_le _ σ).trans ((iInf_le _ A).trans ((iInf_le _ y).trans (iInf_le _ B)))))
    (le_inf (le_inf HC Hy) HB)).trans bv_imp_elim

/-- Composition transports the common-row law with the original row
ideals. No surjectivity onto L or original all-endpoint row law is used. -/
theorem futureCommonBlockRows_of_pullback {S L e f C : bSet 𝔹} {Γ : 𝔹}
    (He : Γ ≤ is_function omegaTwo L e)
    (Hf : Γ ≤ is_func' omegaOne omegaTwo f)
    (HS : Γ ≤ is_func' (prod omegaOne L) (bv_powerset omegaOne) S)
    (Hrows : Γ ≤ normalRowAvailabilityOn S L)
    (Hcommon : Γ ≤ commonBlockRows (sectionPullback e S) f C) :
    Γ ≤ futureCommonBlockRows S L (is_func'_comp Hf (is_func'_of_is_function He)) C := by
  refine le_inf (Hcommon.trans inf_le_left) (le_inf Hrows (le_inf ?_ ?_))
  · apply le_iInf
    intro σ
    apply le_iInf
    intro J
    apply le_iInf
    intro A
    rw [← deduction]
    let Δ := Γ ⊓ (rowNormalIdealDataOn S L σ J ⊓ pair σ A ∈ᴮ C)
    have Hdata := rowNormalIdealData_pullback (inf_le_left.trans He)
      (show Δ ≤ rowNormalIdealDataOn S L σ J from inf_le_right.trans inf_le_left)
    exact (le_inf (inf_le_left.trans
      ((Hcommon.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))).trans
        ((iInf_le _ σ).trans ((iInf_le _ J).trans (iInf_le _ A)))))
      (le_inf Hdata (inf_le_right.trans inf_le_right))).trans bv_imp_elim
  · apply le_iInf
    intro σ
    apply le_iInf
    intro A
    apply le_iInf
    intro y
    apply le_iInf
    intro B
    rw [← deduction]
    let Δ := Γ ⊓ ((pair σ A ∈ᴮ C ⊓
      rangeMem omegaOne (is_func'_comp Hf (is_func'_of_is_function He)) y) ⊓ pair (pair σ y) B ∈ᴮ S)
    have HC : Δ ≤ pair σ A ∈ᴮ C := inf_le_right.trans (inf_le_left.trans inf_le_left)
    have Hσ : Δ ≤ σ ∈ᴮ omegaOne :=
      mem_domain_of_is_function HC (inf_le_left.trans (Hcommon.trans inf_le_left))
    obtain ⟨t, Ht⟩ := rangeMem_comp_witness Hf (is_func'_of_is_function He)
      (show Δ ≤ rangeMem omegaOne (is_func'_comp Hf (is_func'_of_is_function He)) y from
        inf_le_right.trans (inf_le_left.trans inf_le_right))
    have Hsection : Δ ≤ pair (pair σ t) B ∈ᴮ sectionPullback e S :=
      (sectionPullback_pair_iff_of_value (inf_le_left.trans He) (inf_le_left.trans HS)
        Hσ (Ht.trans (inf_le_right.trans inf_le_right))).mpr
          (show Δ ≤ pair (pair σ y) B ∈ᴮ S from inf_le_right.trans inf_le_right)
    exact commonBlockRows_section_apply (inf_le_left.trans Hcommon) HC
      (Ht.trans (inf_le_right.trans inf_le_left)) Hsection

/-- Both the vertex graph and all common-row witnesses are transported;
the common-row family C itself is unchanged. -/
theorem futureSuccessfulBlockData_of_pullback
    {color : Bool} {R S L e f C : bSet 𝔹} {Γ : 𝔹}
    (He : Γ ≤ is_injective_function omegaTwo L e)
    (Hinc : Γ ≤ increasingOn omegaTwo e)
    (HS : Γ ≤ is_func' (prod omegaOne L) (bv_powerset omegaOne) S)
    (Hrows : Γ ≤ normalRowAvailabilityOn S L)
    (Hblock : Γ ≤ successfulBlockData color (pullbackRelation omegaTwo R e)
      (sectionPullback e S) f C) :
    Γ ≤ futureSuccessfulBlockData color R S L
      (injective_function_comp (Hblock.trans inf_le_left) He) C := by
  have Hf := Hblock.trans inf_le_left
  refine le_inf (injective_function_comp_is_injective_function (H₁ := Hf) (H₂ := He))
    (le_inf ?_ (le_inf ?_ ?_))
  · exact increasingOn_injective_function_comp Hf He
      (Hblock.trans (inf_le_right.trans inf_le_left)) Hinc
  · exact homogeneousUnion_injective_function_comp_pullback omegaTwo_Ord Hf Hf He Hinc
      (Hblock.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))
  · exact futureCommonBlockRows_of_pullback (He.trans inf_le_left)
      (is_func'_of_is_injective_function Hf) HS Hrows
      (Hblock.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))

theorem hasFutureSuccessfulBlock_of_pullback
    {color : Bool} {R S L e : bSet 𝔹} {Γ : 𝔹}
    (He : Γ ≤ is_injective_function omegaTwo L e)
    (Hinc : Γ ≤ increasingOn omegaTwo e)
    (HS : Γ ≤ is_func' (prod omegaOne L) (bv_powerset omegaOne) S)
    (Hrows : Γ ≤ normalRowAvailabilityOn S L)
    (Hblock : Γ ≤ hasSuccessfulBlock color (pullbackRelation omegaTwo R e)
      (sectionPullback e S)) : Γ ≤ hasFutureSuccessfulBlock color R S L := by
  apply (le_inf le_rfl Hblock).trans
  change Γ ⊓ (⨆ f, ⨆ C, successfulBlockData color (pullbackRelation omegaTwo R e)
    (sectionPullback e S) f C) ≤ _
  rw [inf_iSup_eq]
  apply iSup_le
  intro f
  rw [inf_iSup_eq]
  apply iSup_le
  intro C
  let Δ := Γ ⊓ successfulBlockData color (pullbackRelation omegaTwo R e) (sectionPullback e S) f C
  have Hdata : Δ ≤ successfulBlockData color (pullbackRelation omegaTwo R e)
      (sectionPullback e S) f C := inf_le_right
  exact le_iSup_of_le (injective_function_comp (Hdata.trans inf_le_left) (inf_le_left.trans He))
    (le_iSup_of_le C (futureSuccessfulBlockData_of_pullback
      (inf_le_left.trans He) (inf_le_left.trans Hinc) (inf_le_left.trans HS)
      (inf_le_left.trans Hrows) Hdata))

/-- The opposite branch retains its exact increasing omega-two domain
and is supported inside the original future, in either Boolean color. -/
theorem orderedLargeClique_of_pullback
    {color : Bool} {R L e : bSet 𝔹} {Γ : 𝔹}
    (He : Γ ≤ is_injective_function omegaTwo L e)
    (Hinc : Γ ≤ increasingOn omegaTwo e)
    (Hclique : Γ ≤ orderedLargeClique color (pullbackRelation omegaTwo R e) omegaTwo) :
    Γ ≤ orderedLargeClique color R L := by
  apply (le_inf le_rfl Hclique).trans
  change Γ ⊓ (⨆ f, is_injective_function omegaTwo omegaTwo f ⊓
    (increasingOn omegaTwo f ⊓
      homogeneousUnion color (pullbackRelation omegaTwo R e) omegaTwo omegaTwo f f)) ≤ _
  rw [inf_iSup_eq]
  apply iSup_le
  intro f
  let Δ := Γ ⊓ (is_injective_function omegaTwo omegaTwo f ⊓
    (increasingOn omegaTwo f ⊓
      homogeneousUnion color (pullbackRelation omegaTwo R e) omegaTwo omegaTwo f f))
  have Hf : Δ ≤ is_injective_function omegaTwo omegaTwo f := inf_le_right.trans inf_le_left
  have He' : Δ ≤ is_injective_function omegaTwo L e := inf_le_left.trans He
  apply le_iSup_of_le (injective_function_comp Hf He')
  exact le_inf (injective_function_comp_is_injective_function (H₁ := Hf) (H₂ := He'))
    (le_inf (increasingOn_injective_function_comp Hf He'
      (inf_le_right.trans (inf_le_right.trans inf_le_left)) (inf_le_left.trans Hinc))
      (homogeneousUnion_injective_function_comp_pullback omegaTwo_Ord Hf Hf He'
        (inf_le_left.trans Hinc) (inf_le_right.trans (inf_le_right.trans inf_le_right))))

/-- The internal analogue of the large-future block extension theorem.
Reindexing, the successful block, and the opposite clique are constructed
from exactly the displayed assumptions. L need not be stationary. -/
theorem successful_block_in_future_or_ordered_opposite
    {color : Bool} {R S L : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HL : Γ ≤ L ⊆ᴮ omegaTwo)
    (Hlarge : Γ ≤ injects_into omegaTwo L)
    (HS : Γ ≤ is_func' (prod omegaOne L) (bv_powerset omegaOne) S)
    (Hrows : Γ ≤ normalRowAvailabilityOn S L) :
    Γ ≤ hasFutureSuccessfulBlock color R S L ⊔ orderedLargeClique (!color) R L := by
  obtain ⟨e, He⟩ := exists_increasing_injection omegaTwo_Ord HL omegaTwo_initial Hlarge
  have Heinj := He.trans inf_le_left
  have Heinc := He.trans (inf_le_right.trans inf_le_left)
  have HSp := is_func'_of_is_function (sectionPullback_is_function (Heinj.trans inf_le_left) HS)
  have Hrowsp := normalRowAvailability_pullback (Heinj.trans inf_le_left) Hrows
  have Hdichotomy :=
    ErdosInternalSimultaneousBlockDichotomy.successful_block_or_ordered_opposite
      (color := color) (R := pullbackRelation omegaTwo R e) HCH HSp Hrowsp
  apply (le_inf le_rfl Hdichotomy).trans
  rw [inf_sup_left]
  exact sup_le
    ((hasFutureSuccessfulBlock_of_pullback (inf_le_left.trans Heinj)
      (inf_le_left.trans Heinc) (inf_le_left.trans HS) (inf_le_left.trans Hrows)
      inf_le_right).trans le_sup_left)
    ((orderedLargeClique_of_pullback (inf_le_left.trans Heinj)
      (inf_le_left.trans Heinc) inf_le_right).trans le_sup_right)

/-- The opposite branch also gives the exact two-block target inside the
same future. The successful one-block branch still awaits full fusion. -/
theorem successful_block_in_future_or_opposite_twoBlock
    {color : Bool} {R S L : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HL : Γ ≤ L ⊆ᴮ omegaTwo)
    (Hlarge : Γ ≤ injects_into omegaTwo L)
    (HS : Γ ≤ is_func' (prod omegaOne L) (bv_powerset omegaOne) S)
    (Hrows : Γ ≤ normalRowAvailabilityOn S L) :
    Γ ≤ hasFutureSuccessfulBlock color R S L ⊔ hasTwoBlock (!color) R omegaOne bSet.omega L := by
  apply (le_inf le_rfl
    (successful_block_in_future_or_ordered_opposite HCH HL Hlarge HS Hrows)).trans
  rw [inf_sup_left]
  exact sup_le (inf_le_right.trans le_sup_left)
    ((ErdosLargeCliqueTwoBlock.twoBlock_of_orderedLargeClique
      (inf_le_left.trans HCH) (inf_le_left.trans HL) inf_le_right).trans le_sup_right)

end bSet.ErdosFutureBlockDichotomy
