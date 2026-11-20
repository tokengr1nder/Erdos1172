/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalRowSectionFamily
public import Erdos1172.Part4InternalFutureBlockWitness

@[expose] public section

/-!
# One actual simultaneous block extension

A large future is constructed for the actual old row family. Its opposite
sections form an actual graph, whose normal-row data use the same fixed
ideal only on that future. The future-block theorem then constructs an
increasing homogeneous omega-one graph and one actual common-row family.
All old rows lie strictly below the new block, and the common values give
co-large opposite-color cross edges. No successful run, new block, section
graph, or compatible cross-edge family is supplied as an input.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosOneBlockExtension

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosIdeal ErdosDenseBasis
open ErdosColargeIntersection ErdosForwardSections ErdosSimultaneousFuture
open ErdosRowSectionFamily ErdosSectionPullback ErdosFutureBlockDichotomy
open ErdosFutureBlockWitness ErdosIndependentHomogeneous

def rowsBeforeBlock (Rows f : bSet 𝔹) : 𝔹 :=
  ⨅ σ, ⨅ r, ⨅ x, ⨅ y, _root_.imp
    ((σ ∈ᴮ omegaOne ⊓ pair σ r ∈ᴮ Rows) ⊓
      (rangeMem omegaOne r x ⊓ rangeMem omegaOne f y)) (x ∈ᴮ y)

def commonRowCrossEdges (color : Bool) (R Rows f C : bSet 𝔹) : 𝔹 :=
  ⨅ σ, ⨅ r, ⨅ A, ⨅ i, ⨅ x, ⨅ y, _root_.imp
    ((pair σ r ∈ᴮ Rows ⊓ pair σ A ∈ᴮ C) ⊓
      (i ∈ᴮ A ⊓ (pair i x ∈ᴮ r ⊓ rangeMem omegaOne f y)))
    (x ∈ᴮ y ⊓ graphColor (!color) R x y)

theorem rowsBeforeBlock_apply {Rows f σ r x y : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ rowsBeforeBlock Rows f) (Hσ : Γ ≤ σ ∈ᴮ omegaOne)
    (Hrow : Γ ≤ pair σ r ∈ᴮ Rows) (Hx : Γ ≤ rangeMem omegaOne r x)
    (Hy : Γ ≤ rangeMem omegaOne f y) : Γ ≤ x ∈ᴮ y :=
  (le_inf (H.trans ((iInf_le _ σ).trans ((iInf_le _ r).trans
    ((iInf_le _ x).trans (iInf_le _ y)))))
    (le_inf (le_inf Hσ Hrow) (le_inf Hx Hy))).trans bv_imp_elim

theorem commonRowCrossEdges_apply
    {color : Bool} {R Rows f C σ r A i x y : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ commonRowCrossEdges color R Rows f C)
    (Hrow : Γ ≤ pair σ r ∈ᴮ Rows) (HC : Γ ≤ pair σ A ∈ᴮ C)
    (Hi : Γ ≤ i ∈ᴮ A) (Hix : Γ ≤ pair i x ∈ᴮ r)
    (Hy : Γ ≤ rangeMem omegaOne f y) : Γ ≤ x ∈ᴮ y ⊓ graphColor (!color) R x y :=
  (le_inf (H.trans ((iInf_le _ σ).trans ((iInf_le _ r).trans
    ((iInf_le _ A).trans ((iInf_le _ i).trans ((iInf_le _ x).trans (iInf_le _ y)))))))
    (le_inf (le_inf Hrow HC) (le_inf Hi (le_inf Hix Hy)))).trans bv_imp_elim

theorem rowsBeforeBlock_of_bound {Rows a L f : bSet 𝔹} {Γ : 𝔹}
    (Hbelow : Γ ≤ rowsBelow omegaOne Rows a)
    (Hlater : Γ ≤ ⨅ y, _root_.imp (y ∈ᴮ L) (a ∈ᴮ y))
    (HL : Γ ≤ L ⊆ᴮ omegaTwo) (Hf : Γ ≤ is_function omegaOne L f) :
    Γ ≤ rowsBeforeBlock Rows f := by
  apply le_iInf
  intro σ
  apply le_iInf
  intro r
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ ((σ ∈ᴮ omegaOne ⊓ pair σ r ∈ᴮ Rows) ⊓
    (rangeMem omegaOne r x ⊓ rangeMem omegaOne f y))
  have Hy : Δ ≤ y ∈ᴮ L := rangeMem_le_codomain
    (is_func'_of_is_function (inf_le_left.trans Hf))
    (inf_le_right.trans (inf_le_right.trans inf_le_right))
  have Hxa : Δ ≤ x ∈ᴮ a :=
    (le_inf (inf_le_left.trans (Hbelow.trans
      ((iInf_le _ σ).trans ((iInf_le _ r).trans (iInf_le _ x)))))
      (le_inf (inf_le_right.trans inf_le_left)
        (inf_le_right.trans (inf_le_right.trans inf_le_left)))).trans bv_imp_elim
  have Hay : Δ ≤ a ∈ᴮ y :=
    (le_inf (inf_le_left.trans (Hlater.trans (iInf_le _ y))) Hy).trans bv_imp_elim
  exact mem_of_mem_Ord Hxa Hay
    (Ord_of_mem_Ord (mem_of_mem_subset (inf_le_left.trans HL) Hy) omegaTwo_Ord)

/-- Containment in the actual row sections gives the explicit cross-edge
law. Only the functionality part of each old row injection is used here. -/
theorem commonRowCrossEdges_of_future_block
    {color : Bool} {R Rows L f C : bSet 𝔹} {Γ : 𝔹}
    (HRows : Γ ≤ is_function omegaOne (bv_powerset (prod omegaOne omegaTwo)) Rows)
    (HrowInj : Γ ≤ ⨅ σ, ⨅ r, _root_.imp
      (σ ∈ᴮ omegaOne ⊓ pair σ r ∈ᴮ Rows)
      (is_injective_function omegaOne omegaTwo r))
    (HL : Γ ≤ L ⊆ᴮ omegaTwo) (Hf : Γ ≤ is_function omegaOne L f)
    (Hcommon : Γ ≤ futureCommonBlockRows (rowSections color R Rows) L f C) :
    Γ ≤ commonRowCrossEdges color R Rows f C := by
  apply le_iInf
  intro σ
  apply le_iInf
  intro r
  apply le_iInf
  intro A
  apply le_iInf
  intro i
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ ((pair σ r ∈ᴮ Rows ⊓ pair σ A ∈ᴮ C) ⊓
    (i ∈ᴮ A ⊓ (pair i x ∈ᴮ r ⊓ rangeMem omegaOne f y)))
  have Hrow : Δ ≤ pair σ r ∈ᴮ Rows := inf_le_right.trans (inf_le_left.trans inf_le_left)
  have HC : Δ ≤ pair σ A ∈ᴮ C := inf_le_right.trans (inf_le_left.trans inf_le_right)
  have Hi : Δ ≤ i ∈ᴮ A := inf_le_right.trans (inf_le_right.trans inf_le_left)
  have Hix : Δ ≤ pair i x ∈ᴮ r :=
    inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have Hy : Δ ≤ rangeMem omegaOne f y :=
    inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  have Hσ : Δ ≤ σ ∈ᴮ omegaOne :=
    mem_domain_of_is_function HC (inf_le_left.trans (Hcommon.trans inf_le_left))
  have Hyω : Δ ≤ y ∈ᴮ omegaTwo := mem_of_mem_subset (inf_le_left.trans HL)
    (rangeMem_le_codomain (is_func'_of_is_function (inf_le_left.trans Hf)) Hy)
  have Hr : Δ ≤ is_injective_function omegaOne omegaTwo r :=
    (le_inf (inf_le_left.trans (HrowInj.trans ((iInf_le _ σ).trans (iInf_le _ r))))
      (le_inf Hσ Hrow)).trans bv_imp_elim
  have Hfunc : Δ ≤ is_func Rows :=
    inf_le_left.trans (HRows.trans (inf_le_left.trans inf_le_left))
  have Hsection : Δ ≤ pair (pair σ y) (forwardSection (!color) R r y) ∈ᴮ
      rowSections color R Rows :=
    (rowSections_pair_iff_of_row Hfunc Hσ Hyω Hrow).mpr bv_refl
  have Hsub : Δ ≤ A ⊆ᴮ forwardSection (!color) R r y :=
    futureCommonBlockRows_section_apply (inf_le_left.trans Hcommon) HC Hy Hsection
  exact forwardSection_value_of_pair
    (Hr.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)))
    (mem_of_mem_subset Hsub Hi) Hix

/-- The original proper normal ideal makes every value of the same actual
common-row family co-large; no ideal is exchanged after the block choice. -/
theorem commonRows_colarge_of_future_block
    {color : Bool} {R Rows L J f C : bSet 𝔹} {Γ : 𝔹}
    (Hproper : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hdiag : Γ ≤ diagonalClosure omegaOne J)
    (Hfuture : Γ ≤ oppositeSectionsColarge color R J omegaOne Rows L)
    (Hcommon : Γ ≤ futureCommonBlockRows (rowSections color R Rows) L f C) :
    Γ ≤ ⨅ σ, ⨅ A, _root_.imp (pair σ A ∈ᴮ C) (colarge omegaOne J A) := by
  apply le_iInf
  intro σ
  apply le_iInf
  intro A
  rw [← deduction]
  exact futureCommonBlockRows_colarge_apply (inf_le_left.trans Hcommon)
    (rowNormalIdealDataOn_rowSections (σ := σ)
      (inf_le_left.trans Hproper) (inf_le_left.trans Habsorb)
      (inf_le_left.trans Hclosure) (inf_le_left.trans Hdiag) (inf_le_left.trans Hfuture))
    inf_le_right

/-- Construct one new homogeneous block in the supplied future, with
strict global separation and co-large opposite-color cross rows. The two
exact-target failures are used to build the simultaneous future and to
eliminate the opposite branch; a successful block is never an input. -/
theorem exists_one_block_extension
    {color : Bool} {R J I B Rows S : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (Hproper : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hdiag : Γ ≤ diagonalClosure omegaOne J)
    (HB : Γ ≤ is_function I (bv_powerset omegaOne) B)
    (HBpos : Γ ≤ positiveValues omegaOne J I B)
    (Hdense : Γ ≤ denseValues omegaOne J I B) (HI : Γ ≤ injects_into I omegaOne)
    (HRows : Γ ≤ is_function omegaOne (bv_powerset (prod omegaOne omegaTwo)) Rows)
    (HrowInj : Γ ≤ ⨅ σ, ⨅ r, _root_.imp
      (σ ∈ᴮ omegaOne ⊓ pair σ r ∈ᴮ Rows)
      (is_injective_function omegaOne omegaTwo r))
    (HrowHom : Γ ≤ ⨅ σ, ⨅ r, _root_.imp
      (σ ∈ᴮ omegaOne ⊓ pair σ r ∈ᴮ Rows)
      (homogeneousUnion color R omegaOne omegaOne r r))
    (Hno : Γ ≤ (hasTwoBlock color R omegaOne bSet.omega omegaTwo)ᶜ)
    (HnoOpp : Γ ≤ (hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo)ᶜ)
    (HS : Γ ≤ S ⊆ᴮ omegaTwo) (HSlarge : Γ ≤ injects_into omegaTwo S) :
    ∃ f C : bSet 𝔹, Γ ≤ is_injective_function omegaOne S f ⊓
      (increasingOn omegaOne f ⊓
        (homogeneousUnion color R omegaOne omegaOne f f ⊓
          (rowsBeforeBlock Rows f ⊓
            (is_function omegaOne (bv_powerset omegaOne) C ⊓
              ((⨅ σ, ⨅ A, _root_.imp (pair σ A ∈ᴮ C) (colarge omegaOne J A)) ⊓
                commonRowCrossEdges color R Rows f C))))) := by
  obtain ⟨a, L, Hfuture⟩ := exists_large_simultaneous_future HCH Habsorb
    (Hproper.trans inf_le_left) Hclosure HB HBpos Hdense HI HRows injects_into_refl
    HrowInj HrowHom Hno HnoOpp HS HSlarge
  have Hbelow : Γ ≤ rowsBelow omegaOne Rows a :=
    Hfuture.trans (inf_le_right.trans inf_le_left)
  have HLS : Γ ≤ L ⊆ᴮ S :=
    Hfuture.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have HLlarge : Γ ≤ injects_into omegaTwo L :=
    Hfuture.trans (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))
  have Hlater : Γ ≤ ⨅ y, _root_.imp (y ∈ᴮ L) (a ∈ᴮ y) :=
    Hfuture.trans (inf_le_right.trans (inf_le_right.trans
      (inf_le_right.trans (inf_le_right.trans inf_le_left))))
  have Hsections : Γ ≤ oppositeSectionsColarge color R J omegaOne Rows L :=
    Hfuture.trans (inf_le_right.trans (inf_le_right.trans
      (inf_le_right.trans (inf_le_right.trans inf_le_right))))
  have HL : Γ ≤ L ⊆ᴮ omegaTwo := subset_trans' HLS HS
  have HsectionFunc : Γ ≤ is_function (prod omegaOne omegaTwo) (bv_powerset omegaOne)
      (rowSections color R Rows) := rowSections_is_function HRows
  have HsectionWeak : Γ ≤ is_func' (prod omegaOne L) (bv_powerset omegaOne)
      (rowSections color R Rows) :=
    is_func'_subset_of_is_func' (is_func'_of_is_function HsectionFunc) (prod_codomain_mono HL)
  have Hnormal : Γ ≤ normalRowAvailabilityOn (rowSections color R Rows) L :=
    normalRowAvailabilityOn_rowSections Hproper Habsorb Hclosure Hdiag Hsections
  obtain ⟨f, C, Hblock⟩ := exists_futureSuccessfulBlock_of_no_opposite
    (color := color) (R := R) HCH HL HLlarge HsectionWeak Hnormal HnoOpp
  have Hfinj : Γ ≤ is_injective_function omegaOne L f := Hblock.trans inf_le_left
  have Hinc : Γ ≤ increasingOn omegaOne f := Hblock.trans (inf_le_right.trans inf_le_left)
  have Hhom : Γ ≤ homogeneousUnion color R omegaOne omegaOne f f :=
    Hblock.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have Hcommon : Γ ≤ futureCommonBlockRows (rowSections color R Rows) L f C :=
    Hblock.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  exact ⟨f, C, le_inf (is_injective_function_codomain_mono HLS Hfinj)
    (le_inf Hinc (le_inf Hhom
      (le_inf (rowsBeforeBlock_of_bound Hbelow Hlater HL (Hfinj.trans inf_le_left))
        (le_inf (Hcommon.trans inf_le_left)
          (le_inf (commonRows_colarge_of_future_block
            Hproper Habsorb Hclosure Hdiag Hsections Hcommon)
            (commonRowCrossEdges_of_future_block HRows HrowInj HL
              (Hfinj.trans inf_le_left) Hcommon))))))⟩

end bSet.ErdosOneBlockExtension
