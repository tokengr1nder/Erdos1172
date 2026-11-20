/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSuccessfulRunBlock
public import Erdos1172.Part4InternalRelationGraph

@[expose] public section

/-!
# Actual section pullback from an arbitrary future

The original section graph need only be weakly total on `omegaOne × L`.
Its values are pulled back along one actual function from omega-two into
`L`. Row ideal data are guarded only by membership in `L`; no co-large
section or normal-row availability outside the future is assumed. The
same individual row ideals satisfy the existing global row-data predicate
for the pulled-back graph.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSectionPullback

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosRelationGraph ErdosIdeal ErdosColargeIntersection
open ErdosSimultaneousRowChoice ErdosSimultaneousRun ErdosSuccessfulRunBlock

def pulledSectionRel (e S q A : bSet 𝔹) : 𝔹 :=
  ⨆ σ, ⨆ t, q =ᴮ pair σ t ⊓
    ⨆ y, pair t y ∈ᴮ e ⊓ pair (pair σ y) A ∈ᴮ S

theorem pulledSectionRel_ext_index (e S A : bSet 𝔹) :
    B_ext (fun q => pulledSectionRel e S q A) :=
  B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
    B_ext_inf B_ext_bv_eq_left B_ext_const))

theorem pulledSectionRel_ext_value (e S q : bSet 𝔹) :
    B_ext (pulledSectionRel e S q) :=
  B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
    B_ext_inf B_ext_const (B_ext_iSup (h := fun _ =>
      B_ext_inf B_ext_const B_ext_pair_mem_right))))

theorem pulledSectionRel_pair (e S σ t A : bSet 𝔹) :
    pulledSectionRel e S (pair σ t) A =
      ⨆ y, pair t y ∈ᴮ e ⊓ pair (pair σ y) A ∈ᴮ S := by
  apply le_antisymm
  · unfold pulledSectionRel
    apply iSup_le
    intro τ
    apply iSup_le
    intro u
    rw [inf_iSup_eq]
    apply iSup_le
    intro y
    apply le_iSup_of_le y
    refine le_inf ?_ ?_
    · exact bv_rw' (ϕ := fun z => pair z y ∈ᴮ e)
        (eq_of_eq_pair_right' inf_le_left) (h_congr := B_ext_pair_mem_left)
        (H_new := inf_le_right.trans inf_le_left)
    · exact bv_rw' (ϕ := fun z => pair (pair z y) A ∈ᴮ S)
        (eq_of_eq_pair_left' inf_le_left)
        (h_congr := B_ext_pair_left B_ext_pair_mem_left)
        (H_new := inf_le_right.trans inf_le_right)
  · exact le_iSup_of_le σ (le_iSup_of_le t (le_inf bv_refl le_rfl))

def sectionPullback (e S : bSet 𝔹) : bSet 𝔹 :=
  relationGraph (prod omegaOne omegaTwo) (bv_powerset omegaOne) (pulledSectionRel e S)

theorem mem_sectionPullback_iff {e S q A : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair q A ∈ᴮ sectionPullback e S ↔
      Γ ≤ q ∈ᴮ prod omegaOne omegaTwo ∧ Γ ≤ A ∈ᴮ bv_powerset omegaOne ∧
        Γ ≤ pulledSectionRel e S q A :=
  mem_relationGraph_iff (pulledSectionRel_ext_index e S) (pulledSectionRel_ext_value e S)

theorem sectionPullback_pair_iff {e S σ t A : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair (pair σ t) A ∈ᴮ sectionPullback e S ↔
      Γ ≤ σ ∈ᴮ omegaOne ∧ Γ ≤ t ∈ᴮ omegaTwo ∧
        Γ ≤ A ∈ᴮ bv_powerset omegaOne ∧
          Γ ≤ ⨆ y, pair t y ∈ᴮ e ⊓ pair (pair σ y) A ∈ᴮ S := by
  rw [mem_sectionPullback_iff, pulledSectionRel_pair]
  constructor
  · rintro ⟨Hpair, HA, Hrel⟩
    exact ⟨(mem_prod_iff.mp Hpair).1, (mem_prod_iff.mp Hpair).2, HA, Hrel⟩
  · rintro ⟨Hσ, Ht, HA, Hrel⟩
    exact ⟨mem_prod Hσ Ht, HA, Hrel⟩

theorem sectionPullback_witness {e S σ t A : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ pair (pair σ t) A ∈ᴮ sectionPullback e S) :
    ∃ y : bSet 𝔹, Γ ≤ pair t y ∈ᴮ e ⊓ pair (pair σ y) A ∈ᴮ S :=
  exists_convert (sectionPullback_pair_iff.mp H).2.2.2
    (B_ext_inf B_ext_pair_mem_right (B_ext_pair_right B_ext_pair_mem_left))

theorem sectionPullback_subset {e S : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ sectionPullback e S ⊆ᴮ prod (prod omegaOne omegaTwo) (bv_powerset omegaOne) :=
  relationGraph_subset

private theorem codomain_of_weak_pair {D C f i A : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' D C f) (Hi : Γ ≤ i ∈ᴮ D) (Hpair : Γ ≤ pair i A ∈ᴮ f) :
    Γ ≤ A ∈ᴮ C := by
  have Hex : Γ ≤ ⨆ B, B ∈ᴮ C ⊓ pair i B ∈ᴮ f :=
    (le_inf ((is_total_of_is_func' Hf).trans (iInf_le _ i)) Hi).trans bv_imp_elim
  obtain ⟨B, HB⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Heq : Γ ≤ A =ᴮ B :=
    eq_of_is_func_of_eq (Hf.trans inf_le_left) bv_refl Hpair (HB.trans inf_le_right)
  exact mem_congr (bv_symm Heq) bv_refl (HB.trans inf_le_left)

/-- At a known value of the enumerating function, membership in the
pulled-back section graph is exactly membership in the original section.
Weak totality suffices to recover the output powerset guard. -/
theorem sectionPullback_pair_iff_of_value {L e S σ t y A : bSet 𝔹} {Γ : 𝔹}
    (He : Γ ≤ is_function omegaTwo L e)
    (HS : Γ ≤ is_func' (prod omegaOne L) (bv_powerset omegaOne) S)
    (Hσ : Γ ≤ σ ∈ᴮ omegaOne) (Hty : Γ ≤ pair t y ∈ᴮ e) :
    (Γ ≤ pair (pair σ t) A ∈ᴮ sectionPullback e S) ↔
      Γ ≤ pair (pair σ y) A ∈ᴮ S := by
  constructor
  · intro H
    obtain ⟨z, Hz⟩ := sectionPullback_witness H
    have Hzy : Γ ≤ z =ᴮ y :=
      eq_of_is_function_of_eq He bv_refl (Hz.trans inf_le_left) Hty
    exact mem_congr (pair_congr (pair_congr bv_refl Hzy) bv_refl) bv_refl
      (Hz.trans inf_le_right)
  · intro H
    have Ht := mem_domain_of_is_function Hty He
    have Hy := mem_codomain_of_is_function Hty He
    exact sectionPullback_pair_iff.mpr ⟨Hσ, Ht,
      codomain_of_weak_pair HS (mem_prod Hσ Hy) H, le_iSup_of_le y (le_inf Hty H)⟩

theorem sectionPullback_is_function {L e S : bSet 𝔹} {Γ : 𝔹}
    (He : Γ ≤ is_function omegaTwo L e)
    (HS : Γ ≤ is_func' (prod omegaOne L) (bv_powerset omegaOne) S) :
    Γ ≤ is_function (prod omegaOne omegaTwo) (bv_powerset omegaOne) (sectionPullback e S) := by
  apply relationGraph_is_function (P := pulledSectionRel e S)
    (pulledSectionRel_ext_index e S) (pulledSectionRel_ext_value e S)
  · apply le_iInf
    intro q
    rw [← deduction]
    let Δ := Γ ⊓ q ∈ᴮ prod omegaOne omegaTwo
    obtain ⟨σ, Hσ, t, Ht, Hq⟩ := mem_prod_iff₂.mp
      (show Δ ≤ q ∈ᴮ prod omegaOne omegaTwo from inf_le_right)
    have Hy : Δ ≤ ⨆ y, y ∈ᴮ L ⊓ pair t y ∈ᴮ e :=
      (le_inf (inf_le_left.trans ((is_total_of_is_function He).trans (iInf_le _ t))) Ht).trans
        bv_imp_elim
    obtain ⟨y, Hy⟩ := exists_convert Hy (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
    have HA : Δ ≤ ⨆ A, A ∈ᴮ bv_powerset omegaOne ⊓ pair (pair σ y) A ∈ᴮ S :=
      (le_inf (inf_le_left.trans ((is_total_of_is_func' HS).trans (iInf_le _ (pair σ y))))
        (mem_prod Hσ (Hy.trans inf_le_left))).trans bv_imp_elim
    obtain ⟨A, HA⟩ := exists_convert HA (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
    exact le_iSup_of_le A (le_inf (HA.trans inf_le_left)
      (le_iSup_of_le σ (le_iSup_of_le t (le_inf Hq
        (le_iSup_of_le y (le_inf (Hy.trans inf_le_right) (HA.trans inf_le_right)))))))
  · intro q₁ q₂ A B Δ HΔ Hq₁ Hq₂ _ _ Hrel₁ Hrel₂ Hq
    obtain ⟨σ, _, t, _, Hqt⟩ := mem_prod_iff₂.mp Hq₁
    obtain ⟨τ, _, u, _, Hqu⟩ := mem_prod_iff₂.mp Hq₂
    have Heq : Δ ≤ pair σ t =ᴮ pair τ u := bv_trans (bv_symm Hqt) (bv_trans Hq Hqu)
    have HrelA : Δ ≤ ⨆ y, pair t y ∈ᴮ e ⊓ pair (pair σ y) A ∈ᴮ S := by
      rw [← pulledSectionRel_pair]
      exact bv_rw'' (ϕ := fun q => pulledSectionRel e S q A) Hqt Hrel₁
        (pulledSectionRel_ext_index e S A)
    have HrelB : Δ ≤ ⨆ y, pair u y ∈ᴮ e ⊓ pair (pair τ y) B ∈ᴮ S := by
      rw [← pulledSectionRel_pair]
      exact bv_rw'' (ϕ := fun q => pulledSectionRel e S q B) Hqu Hrel₂
        (pulledSectionRel_ext_index e S B)
    obtain ⟨y, Hy⟩ := exists_convert HrelA
      (B_ext_inf B_ext_pair_mem_right (B_ext_pair_right B_ext_pair_mem_left))
    obtain ⟨z, Hz⟩ := exists_convert HrelB
      (B_ext_inf B_ext_pair_mem_right (B_ext_pair_right B_ext_pair_mem_left))
    have Hyz : Δ ≤ y =ᴮ z := eq_of_is_function_of_eq (HΔ.trans He)
      (eq_of_eq_pair_right' Heq) (Hy.trans inf_le_left) (Hz.trans inf_le_left)
    exact eq_of_is_func_of_eq (HΔ.trans (HS.trans inf_le_left))
      (pair_congr (eq_of_eq_pair_left' Heq) Hyz) (Hy.trans inf_le_right) (Hz.trans inf_le_right)

def rowIdealDataOn (S L σ J : bSet 𝔹) : 𝔹 :=
  properIdeal omegaOne J ⊓ (countableAbsorption omegaOne J ⊓
    (countableClosure J ⊓ (⨅ y, ⨅ A, _root_.imp
      (y ∈ᴮ L ⊓ pair (pair σ y) A ∈ᴮ S) (colarge omegaOne J A))))

def rowNormalIdealDataOn (S L σ J : bSet 𝔹) : 𝔹 :=
  rowIdealDataOn S L σ J ⊓ diagonalClosure omegaOne J

def normalRowAvailabilityOn (S L : bSet 𝔹) : 𝔹 :=
  ⨅ σ, _root_.imp (σ ∈ᴮ omegaOne) (⨆ J, rowNormalIdealDataOn S L σ J)

theorem rowIdealDataOn_omegaTwo (S σ J : bSet 𝔹) :
    rowIdealDataOn S omegaTwo σ J = rowIdealData S σ J := rfl

theorem rowNormalIdealDataOn_omegaTwo (S σ J : bSet 𝔹) :
    rowNormalIdealDataOn S omegaTwo σ J = rowNormalIdealData S σ J := rfl

theorem rowIdealDataOn_value {S L σ J y A : bSet 𝔹} {Γ : 𝔹}
    (Hdata : Γ ≤ rowIdealDataOn S L σ J) (Hy : Γ ≤ y ∈ᴮ L)
    (Hpair : Γ ≤ pair (pair σ y) A ∈ᴮ S) : Γ ≤ colarge omegaOne J A :=
  (le_inf ((Hdata.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))).trans
    ((iInf_le _ y).trans (iInf_le _ A))) (le_inf Hy Hpair)).trans bv_imp_elim

/-- The individual row ideal is unchanged. Only its section-value law is
reindexed, and only original values in `L` are used. -/
theorem rowIdealData_pullback {L e S σ J : bSet 𝔹} {Γ : 𝔹}
    (He : Γ ≤ is_function omegaTwo L e) (Hdata : Γ ≤ rowIdealDataOn S L σ J) :
    Γ ≤ rowIdealData (sectionPullback e S) σ J := by
  refine le_inf (Hdata.trans inf_le_left)
    (le_inf (Hdata.trans (inf_le_right.trans inf_le_left))
      (le_inf (Hdata.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))) ?_))
  apply le_iInf
  intro t
  apply le_iInf
  intro A
  rw [← deduction]
  obtain ⟨y, Hy⟩ := sectionPullback_witness
    (show Γ ⊓ (t ∈ᴮ omegaTwo ⊓ pair (pair σ t) A ∈ᴮ sectionPullback e S) ≤
      pair (pair σ t) A ∈ᴮ sectionPullback e S from inf_le_right.trans inf_le_right)
  exact rowIdealDataOn_value (inf_le_left.trans Hdata)
    (mem_codomain_of_is_function (Hy.trans inf_le_left) (inf_le_left.trans He))
    (Hy.trans inf_le_right)

theorem rowNormalIdealData_pullback {L e S σ J : bSet 𝔹} {Γ : 𝔹}
    (He : Γ ≤ is_function omegaTwo L e) (Hdata : Γ ≤ rowNormalIdealDataOn S L σ J) :
    Γ ≤ rowNormalIdealData (sectionPullback e S) σ J :=
  le_inf (rowIdealData_pullback He (Hdata.trans inf_le_left)) (Hdata.trans inf_le_right)

theorem normalRowAvailability_pullback {L e S : bSet 𝔹} {Γ : 𝔹}
    (He : Γ ≤ is_function omegaTwo L e) (Hrows : Γ ≤ normalRowAvailabilityOn S L) :
    Γ ≤ normalRowAvailability (sectionPullback e S) := by
  apply le_iInf
  intro σ
  rw [← deduction]
  let Δ := Γ ⊓ σ ∈ᴮ omegaOne
  have Hex : Δ ≤ ⨆ J, rowNormalIdealDataOn S L σ J :=
    (le_inf (inf_le_left.trans (Hrows.trans (iInf_le _ σ))) inf_le_right).trans bv_imp_elim
  apply (le_inf (le_refl Δ) Hex).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro J
  exact le_iSup_of_le J
    (rowNormalIdealData_pullback (inf_le_left.trans (inf_le_left.trans He)) inf_le_right)

end bSet.ErdosSectionPullback
