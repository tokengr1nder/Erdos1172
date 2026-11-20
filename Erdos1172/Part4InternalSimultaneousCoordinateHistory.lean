/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSimultaneousEntry

@[expose] public section

/-!
# Decoding all row coordinates of a stage history

A stored stage entry contains a vertex and a whole supported row function.
The fixed decoder reads the latter at every omega-one row coordinate.
Neither stage histories nor decoded rectangular histories are required to
be injective. All names, witnesses, and Boolean conditions are internal.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousHistory

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosRelationGraph ErdosSimultaneousEntry

def coordinateRel (P q w : bSet 𝔹) : 𝔹 :=
  ⨆ i, ⨆ σ, ⨆ y, ⨆ Z, q =ᴮ pair i σ ⊓
    (pair i (pair y Z) ∈ᴮ P ⊓ pair σ w ∈ᴮ Z)

def coordinateHistory (P : bSet 𝔹) : bSet 𝔹 :=
  relationGraph (prod omegaOne omegaOne) omegaOne (coordinateRel P)

def rowFunctions (P : bSet 𝔹) : 𝔹 :=
  ⨅ i, ⨅ y, ⨅ Z, _root_.imp (pair i (pair y Z) ∈ᴮ P)
    (is_function omegaOne omegaOne Z)

theorem rowFunctions_apply {P i y Z : bSet 𝔹} {Γ : 𝔹}
    (Hrows : Γ ≤ rowFunctions P) (Hpair : Γ ≤ pair i (pair y Z) ∈ᴮ P) :
    Γ ≤ is_function omegaOne omegaOne Z :=
  (le_inf (Hrows.trans ((iInf_le _ i).trans ((iInf_le _ y).trans (iInf_le _ Z))))
    Hpair).trans bv_imp_elim

private theorem coordinateRel_ext_left (P w : bSet 𝔹) :
    B_ext (fun q => coordinateRel P q w) :=
  B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ => B_ext_iSup
    (h := fun _ => B_ext_iSup
      (h := fun _ => B_ext_inf B_ext_bv_eq_left B_ext_const))))

private theorem coordinateRel_ext_right (P q : bSet 𝔹) :
    B_ext (coordinateRel P q) :=
  B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ => B_ext_iSup
    (h := fun _ => B_ext_iSup (h := fun _ =>
      B_ext_inf B_ext_const (B_ext_inf B_ext_const B_ext_pair_mem_right)))))

private theorem entry_ext_vertex (P i Z : bSet 𝔹) :
    B_ext (fun y => pair i (pair y Z) ∈ᴮ P) :=
  B_ext_pair_left (ϕ := fun e => pair i e ∈ᴮ P) B_ext_pair_mem_right

private theorem entry_ext_rows (P i y : bSet 𝔹) :
    B_ext (fun Z => pair i (pair y Z) ∈ᴮ P) :=
  B_ext_pair_right (ϕ := fun e => pair i e ∈ᴮ P) B_ext_pair_mem_right

/-- At an actual coordinate pair the existential coordinate code can be
eliminated by internal pair equality. -/
theorem coordinateRel_pair (P i σ w : bSet 𝔹) :
    coordinateRel P (pair i σ) w =
      ⨆ y, ⨆ Z, pair i (pair y Z) ∈ᴮ P ⊓ pair σ w ∈ᴮ Z := by
  apply le_antisymm
  · unfold coordinateRel
    apply iSup_le
    intro j
    apply iSup_le
    intro τ
    apply iSup_le
    intro y
    apply iSup_le
    intro Z
    apply le_iSup_of_le y
    apply le_iSup_of_le Z
    refine le_inf ?_ ?_
    · exact bv_rw' (ϕ := fun a => pair a (pair y Z) ∈ᴮ P)
        (eq_of_eq_pair_left' inf_le_left) (h_congr := B_ext_pair_mem_left)
        (H_new := inf_le_right.trans inf_le_left)
    · exact bv_rw' (ϕ := fun a => pair a w ∈ᴮ Z)
        (eq_of_eq_pair_right' inf_le_left) (h_congr := B_ext_pair_mem_left)
        (H_new := inf_le_right.trans inf_le_right)
  · apply iSup_le
    intro y
    apply iSup_le
    intro Z
    exact le_iSup_of_le i (le_iSup_of_le σ (le_iSup_of_le y
      (le_iSup_of_le Z (le_inf bv_refl le_rfl))))

theorem mem_coordinateHistory_iff {P q w : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair q w ∈ᴮ coordinateHistory P ↔
      Γ ≤ q ∈ᴮ prod omegaOne omegaOne ∧ Γ ≤ w ∈ᴮ omegaOne ∧
        Γ ≤ coordinateRel P q w :=
  mem_relationGraph_iff (coordinateRel_ext_left P) (coordinateRel_ext_right P)

theorem coordinateHistory_subset {P : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ coordinateHistory P ⊆ᴮ prod (prod omegaOne omegaOne) omegaOne :=
  relationGraph_subset

theorem coordinateHistory_pair_iff {P i σ w : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair (pair i σ) w ∈ᴮ coordinateHistory P ↔
      Γ ≤ i ∈ᴮ omegaOne ∧ Γ ≤ σ ∈ᴮ omegaOne ∧ Γ ≤ w ∈ᴮ omegaOne ∧
        Γ ≤ ⨆ y, ⨆ Z, pair i (pair y Z) ∈ᴮ P ⊓ pair σ w ∈ᴮ Z := by
  rw [mem_coordinateHistory_iff, coordinateRel_pair]
  constructor
  · rintro ⟨Hcoord, Hw, Hrel⟩
    exact ⟨(mem_prod_iff.mp Hcoord).1, (mem_prod_iff.mp Hcoord).2, Hw, Hrel⟩
  · rintro ⟨Hi, Hσ, Hw, Hrel⟩
    exact ⟨mem_prod Hi Hσ, Hw, Hrel⟩

theorem coordinateHistory_witness {P i σ w : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ pair (pair i σ) w ∈ᴮ coordinateHistory P) :
    ∃ y Z : bSet 𝔹, Γ ≤ pair i (pair y Z) ∈ᴮ P ∧ Γ ≤ pair σ w ∈ᴮ Z := by
  obtain ⟨y, Hy⟩ := exists_convert (coordinateHistory_pair_iff.mp H).2.2.2
    (B_ext_iSup (h := fun Z => B_ext_inf (entry_ext_vertex P i Z) B_ext_const))
  obtain ⟨Z, HZ⟩ := exists_convert Hy
    (B_ext_inf (entry_ext_rows P i y) B_ext_mem_right)
  exact ⟨y, Z, HZ.trans inf_le_left, HZ.trans inf_le_right⟩

theorem coordinateHistory_apply {P i σ w y Z : bSet 𝔹} {Γ : 𝔹}
    (Hi : Γ ≤ i ∈ᴮ omegaOne) (Hσ : Γ ≤ σ ∈ᴮ omegaOne)
    (Hw : Γ ≤ w ∈ᴮ omegaOne)
    (Hentry : Γ ≤ pair i (pair y Z) ∈ᴮ P) (Hrow : Γ ≤ pair σ w ∈ᴮ Z) :
    Γ ≤ pair (pair i σ) w ∈ᴮ coordinateHistory P :=
  coordinateHistory_pair_iff.mpr ⟨Hi, Hσ, Hw,
    le_iSup_of_le y (le_iSup_of_le Z (le_inf Hentry Hrow))⟩

private theorem coordinateRel_mono {P Q q w : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ P ⊆ᴮ Q) (Hrel : Γ ≤ coordinateRel P q w) :
    Γ ≤ coordinateRel Q q w := by
  apply (le_inf (le_refl Γ) Hrel).trans
  rw [coordinateRel, inf_iSup_eq]
  apply iSup_le
  intro i
  rw [inf_iSup_eq]
  apply iSup_le
  intro σ
  rw [inf_iSup_eq]
  apply iSup_le
  intro y
  rw [inf_iSup_eq]
  apply iSup_le
  intro Z
  apply le_iSup_of_le i
  apply le_iSup_of_le σ
  apply le_iSup_of_le y
  apply le_iSup_of_le Z
  exact le_inf (inf_le_right.trans inf_le_left)
    (le_inf (mem_of_mem_subset (inf_le_left.trans Hsub)
      (inf_le_right.trans (inf_le_right.trans inf_le_left)))
      (inf_le_right.trans (inf_le_right.trans inf_le_right)))

theorem coordinateHistory_mono {P Q : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ P ⊆ᴮ Q) : Γ ≤ coordinateHistory P ⊆ᴮ coordinateHistory Q := by
  rw [subset_unfold']
  apply le_iInf
  intro p
  rw [← deduction]
  let Δ := Γ ⊓ p ∈ᴮ coordinateHistory P
  have Hp : Δ ≤ p ∈ᴮ coordinateHistory P := inf_le_right
  have Hsupport : Δ ≤ p ∈ᴮ prod (prod omegaOne omegaOne) omegaOne :=
    mem_of_mem_subset relationGraph_subset Hp
  obtain ⟨q, _, w, _, Hpq⟩ := mem_prod_iff₂.mp Hsupport
  have Hparts := mem_coordinateHistory_iff.mp (mem_congr Hpq bv_refl Hp)
  exact mem_congr (bv_symm Hpq) bv_refl (mem_coordinateHistory_iff.mpr
    ⟨Hparts.1, Hparts.2.1,
      coordinateRel_mono (inf_le_left.trans Hsub) Hparts.2.2⟩)

theorem coordinateHistory_congr_graph : B_congr (coordinateHistory (𝔹 := 𝔹)) := by
  intro P Q Γ H
  have Hsub : Γ ≤ (P ⊆ᴮ Q) ⊓ (Q ⊆ᴮ P) := by
    simpa only [eq_iff_subset_subset] using H
  exact subset_ext (coordinateHistory_mono (Hsub.trans inf_le_left))
    (coordinateHistory_mono (Hsub.trans inf_le_right))

private theorem coordinate_output_eq {P i j σ τ v w : bSet 𝔹} {Γ : 𝔹}
    (Hfunc : Γ ≤ is_func P) (Hrows : Γ ≤ rowFunctions P)
    (Hv : Γ ≤ pair (pair i σ) v ∈ᴮ coordinateHistory P)
    (Hw : Γ ≤ pair (pair j τ) w ∈ᴮ coordinateHistory P)
    (Hij : Γ ≤ i =ᴮ j) (Hστ : Γ ≤ σ =ᴮ τ) : Γ ≤ v =ᴮ w := by
  obtain ⟨y, Z, Hentry, HvZ⟩ := coordinateHistory_witness Hv
  obtain ⟨z, W, Hother, HwW⟩ := coordinateHistory_witness Hw
  have HZW : Γ ≤ Z =ᴮ W := eq_of_eq_pair_right'
    (eq_of_is_func_of_eq Hfunc Hij Hentry Hother)
  exact eq_of_is_function_of_eq (rowFunctions_apply Hrows Hentry) Hστ HvZ
    (mem_congr bv_refl (bv_symm HZW) HwW)

theorem coordinateHistory_is_func {P : bSet 𝔹} {Γ : 𝔹}
    (Hfunc : Γ ≤ is_func P) (Hrows : Γ ≤ rowFunctions P) :
    Γ ≤ is_func (coordinateHistory P) := by
  apply le_iInf
  intro q₁
  apply le_iInf
  intro q₂
  apply le_iInf
  intro v
  apply le_iInf
  intro w
  rw [← deduction, ← deduction]
  let Δ := (Γ ⊓ (pair q₁ v ∈ᴮ coordinateHistory P ⊓
    pair q₂ w ∈ᴮ coordinateHistory P)) ⊓ q₁ =ᴮ q₂
  have HΔ : Δ ≤ Γ := inf_le_left.trans inf_le_left
  have Hv : Δ ≤ pair q₁ v ∈ᴮ coordinateHistory P :=
    inf_le_left.trans (inf_le_right.trans inf_le_left)
  have Hw : Δ ≤ pair q₂ w ∈ᴮ coordinateHistory P :=
    inf_le_left.trans (inf_le_right.trans inf_le_right)
  obtain ⟨i, _, σ, _, Hq₁⟩ := mem_prod_iff₂.mp (mem_coordinateHistory_iff.mp Hv).1
  obtain ⟨j, _, τ, _, Hq₂⟩ := mem_prod_iff₂.mp (mem_coordinateHistory_iff.mp Hw).1
  have Hcoords : Δ ≤ pair i σ =ᴮ pair j τ :=
    bv_trans (bv_symm Hq₁) (bv_trans inf_le_right Hq₂)
  exact coordinate_output_eq (HΔ.trans Hfunc) (HΔ.trans Hrows)
    (mem_congr (pair_congr Hq₁ bv_refl) bv_refl Hv)
    (mem_congr (pair_congr Hq₂ bv_refl) bv_refl Hw)
    (eq_of_eq_pair_left' Hcoords) (eq_of_eq_pair_right' Hcoords)

/-- Every old stage entry supplies every row coordinate. The input history
may contain later support, which does not enter the guarded totality law. -/
theorem coordinateHistory_is_func'_prefix {δ P : bSet 𝔹} {Γ : 𝔹}
    (Hδ : Γ ≤ δ ⊆ᴮ omegaOne) (HP : Γ ≤ is_func' δ entrySpace P)
    (Hrows : Γ ≤ rowFunctions P) :
    Γ ≤ is_func' (prod δ omegaOne) omegaOne (coordinateHistory P) := by
  refine le_inf (coordinateHistory_is_func (HP.trans inf_le_left) Hrows) ?_
  apply le_iInf
  intro q
  rw [← deduction]
  let Δ := Γ ⊓ q ∈ᴮ prod δ omegaOne
  have HΔ : Δ ≤ Γ := inf_le_left
  obtain ⟨i, Hi, σ, Hσ, Hq⟩ := mem_prod_iff₂.mp
    (show Δ ≤ q ∈ᴮ prod δ omegaOne from inf_le_right)
  have Hex : Δ ≤ ⨆ e, e ∈ᴮ entrySpace ⊓ pair i e ∈ᴮ P :=
    (le_inf (HΔ.trans ((HP.trans inf_le_right).trans (iInf_le _ i))) Hi).trans
      bv_imp_elim
  obtain ⟨e, He⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  obtain ⟨y, _, Z, _, Heq⟩ := mem_prod_iff₂.mp (He.trans inf_le_left)
  have Hentry : Δ ≤ pair i (pair y Z) ∈ᴮ P :=
    mem_congr (pair_congr bv_refl Heq) bv_refl (He.trans inf_le_right)
  have HZ : Δ ≤ is_function omegaOne omegaOne Z :=
    rowFunctions_apply (HΔ.trans Hrows) Hentry
  have Hexw : Δ ≤ ⨆ w, w ∈ᴮ omegaOne ⊓ pair σ w ∈ᴮ Z :=
    (le_inf ((is_total_of_is_function HZ).trans (iInf_le _ σ)) Hσ).trans bv_imp_elim
  obtain ⟨w, Hw⟩ := exists_convert Hexw (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  apply le_iSup_of_le w
  refine le_inf (Hw.trans inf_le_left) ?_
  exact mem_congr (pair_congr (bv_symm Hq) bv_refl) bv_refl
    (coordinateHistory_apply (mem_of_mem_subset (HΔ.trans Hδ) Hi) Hσ
      (Hw.trans inf_le_left) Hentry (Hw.trans inf_le_right))

/-- This law is preserved by arbitrary internal unions, without a chain premise. -/
theorem rowFunctions_union {C : bSet 𝔹} {Γ : 𝔹}
    (Hfamily : Γ ≤ ⨅ P, _root_.imp (P ∈ᴮ C) (rowFunctions P)) :
    Γ ≤ rowFunctions (bv_union C) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro y
  apply le_iInf
  intro Z
  rw [← deduction]
  let Δ := Γ ⊓ pair i (pair y Z) ∈ᴮ bv_union C
  obtain ⟨P, HP⟩ := exists_convert (mem_bv_union_iff.mp
    (show Δ ≤ pair i (pair y Z) ∈ᴮ bv_union C from inf_le_right))
    (B_ext_inf B_ext_mem_left B_ext_mem_right)
  have Hrows : Δ ≤ rowFunctions P :=
    (le_inf (inf_le_left.trans (Hfamily.trans (iInf_le _ P)))
      (HP.trans inf_le_left)).trans bv_imp_elim
  exact rowFunctions_apply Hrows (HP.trans inf_le_right)

/-- Adjoining an entry with a supported total row graph preserves the law,
even when its vertex or any row values repeat earlier values. -/
theorem rowFunctions_insert {P i y Z : bSet 𝔹} {Γ : 𝔹}
    (Hrows : Γ ≤ rowFunctions P) (HZ : Γ ≤ is_function omegaOne omegaOne Z) :
    Γ ≤ rowFunctions (bSet.insert1 (pair i (pair y Z)) P) := by
  apply le_iInf
  intro j
  apply le_iInf
  intro z
  apply le_iInf
  intro W
  rw [← deduction]
  let Δ := Γ ⊓ pair j (pair z W) ∈ᴮ bSet.insert1 (pair i (pair y Z)) P
  have Hsplit : Δ ≤ pair j (pair z W) =ᴮ pair i (pair y Z) ⊔
      pair j (pair z W) ∈ᴮ P := by
    rw [← mem_insert1]
    exact inf_le_right
  apply (le_inf (le_refl Δ) Hsplit).trans
  rw [inf_sup_left]
  apply sup_le
  · have HWZ : Δ ⊓ pair j (pair z W) =ᴮ pair i (pair y Z) ≤ W =ᴮ Z :=
      eq_of_eq_pair_right' (eq_of_eq_pair_right' inf_le_right)
    exact bv_rw' (ϕ := fun U => is_function omegaOne omegaOne U) HWZ
      (h_congr := B_ext_is_function_right)
      (H_new := (inf_le_left.trans inf_le_left).trans HZ)
  · exact rowFunctions_apply ((inf_le_left.trans inf_le_left).trans Hrows) inf_le_right

end bSet.ErdosSimultaneousHistory
