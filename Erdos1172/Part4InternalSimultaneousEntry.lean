/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSimultaneousRowChoice
public import Erdos1172.Part4InternalSimultaneousVertex

@[expose] public section

/-!
# A complete deterministic next simultaneous entry

An entry consists of a vertex and the entire omega-one row-choice graph.
The graph is supported and total, but need not be injective: distinct rows
may have the same least value. The exact least-choice law determines that
graph uniquely. Its equality fixes the next-vertex candidate set, and
least-or-sentinel uniqueness then fixes the vertex. Existence and uniqueness
hold at the original arbitrary Boolean condition, with no successful-run
or nonempty-future-candidate premise.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousEntry

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosOrdinalLeast ErdosOrdinalFallback
open ErdosSimultaneousCandidates ErdosSimultaneousRowChoice ErdosSimultaneousVertex

def entrySpace : bSet 𝔹 :=
  prod omegaTwo (bv_powerset (prod omegaOne omegaOne))

def entryValid (color : Bool) (δ R S Y X top y Z : bSet 𝔹) : 𝔹 :=
  is_function omegaOne omegaOne Z ⊓
    (simultaneousRowLaw δ S Y X top Z ⊓
      leastOrTop (futureCandidates color δ R S Y X Z top) top y)

theorem entryValid_ext_value (color : Bool) (δ R S Y X top Z : bSet 𝔹) :
    B_ext (fun y => entryValid color δ R S Y X top y Z) :=
  B_ext_inf B_ext_const (B_ext_inf B_ext_const
    (leastOrTop_ext_value (futureCandidates color δ R S Y X Z top) top))

theorem entryValid_ext_rows (color : Bool) (δ R S Y X top y : bSet 𝔹) :
    B_ext (entryValid color δ R S Y X top y) :=
  B_ext_inf B_ext_is_function_right
    (B_ext_inf (simultaneousRowLaw_ext_graph δ S Y X top)
      (B_ext_term (ϕ := fun C => leastOrTop C top y)
        (t := fun Z => futureCandidates color δ R S Y X Z top)
        (leastOrTop_ext_set top y) (futureCandidates_congr_current color δ R S Y X top)))

private theorem rowLaw_graph_subset {δ S Y X top Z W : bSet 𝔹} {Γ : 𝔹}
    (HZ : Γ ≤ is_function omegaOne omegaOne Z)
    (HW : Γ ≤ is_function omegaOne omegaOne W)
    (HZlaw : Γ ≤ simultaneousRowLaw δ S Y X top Z)
    (HWlaw : Γ ≤ simultaneousRowLaw δ S Y X top W) : Γ ≤ Z ⊆ᴮ W := by
  rw [subset_unfold']
  apply le_iInf
  intro p
  rw [← deduction]
  let Δ := Γ ⊓ p ∈ᴮ Z
  have HΔ : Δ ≤ Γ := inf_le_left
  have Hprod : Δ ≤ p ∈ᴮ prod omegaOne omegaOne :=
    mem_of_mem_subset (HΔ.trans (subset_prod_of_is_function HZ)) inf_le_right
  obtain ⟨σ, Hσ, v, _, Hp⟩ := mem_prod_iff₂.mp Hprod
  have HpairZ : Δ ≤ pair σ v ∈ᴮ Z := mem_congr Hp bv_refl inf_le_right
  have Hex : Δ ≤ ⨆ w, w ∈ᴮ omegaOne ⊓ pair σ w ∈ᴮ W :=
    (le_inf (HΔ.trans ((is_total_of_is_function HW).trans (iInf_le _ σ))) Hσ).trans
      bv_imp_elim
  obtain ⟨w, Hw⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hvw : Δ ≤ v =ᴮ w := leastIn_unique
    (simultaneousRowLaw_apply (HΔ.trans HZlaw) Hσ HpairZ)
    (simultaneousRowLaw_apply (HΔ.trans HWlaw) Hσ (Hw.trans inf_le_right))
  have HpairW : Δ ≤ pair σ v ∈ᴮ W :=
    bv_rw' (ϕ := fun z => pair σ z ∈ᴮ W) Hvw
      (H_new := Hw.trans inf_le_right) (h_congr := B_ext_pair_mem_right)
  exact mem_congr (bv_symm Hp) bv_refl HpairW

/-- Supported total row graphs obeying the same least-choice law agree.
No injectivity assumption on the row graph is made or needed. -/
theorem simultaneousRowLaw_graph_unique {δ S Y X top Z W : bSet 𝔹} {Γ : 𝔹}
    (HZ : Γ ≤ is_function omegaOne omegaOne Z)
    (HW : Γ ≤ is_function omegaOne omegaOne W)
    (HZlaw : Γ ≤ simultaneousRowLaw δ S Y X top Z)
    (HWlaw : Γ ≤ simultaneousRowLaw δ S Y X top W) : Γ ≤ Z =ᴮ W :=
  subset_ext (rowLaw_graph_subset HZ HW HZlaw HWlaw)
    (rowLaw_graph_subset HW HZ HWlaw HZlaw)

/-- Equality of whole entries follows from exact row and vertex laws,
including on Boolean pieces where the next vertex is the sentinel. -/
theorem entryValid_unique
    {color : Bool} {δ R S Y X top y z Z W : bSet 𝔹} {Γ : 𝔹}
    (Hentry : Γ ≤ entryValid color δ R S Y X top y Z)
    (Hother : Γ ≤ entryValid color δ R S Y X top z W) :
    Γ ≤ y =ᴮ z ⊓ Z =ᴮ W := by
  have HZW : Γ ≤ Z =ᴮ W := simultaneousRowLaw_graph_unique
    (Hentry.trans inf_le_left) (Hother.trans inf_le_left)
    (Hentry.trans (inf_le_right.trans inf_le_left))
    (Hother.trans (inf_le_right.trans inf_le_left))
  have Hcandidates : Γ ≤ futureCandidates color δ R S Y X Z top =ᴮ
      futureCandidates color δ R S Y X W top :=
    futureCandidates_congr_current color δ R S Y X top HZW
  exact le_inf (leastOrTop_unique_of_eq Hcandidates
    (Hentry.trans (inf_le_right.trans inf_le_right))
    (Hother.trans (inf_le_right.trans inf_le_right))) HZW

theorem entryValid_mem_entrySpace
    {color : Bool} {δ R S Y X top y Z : bSet 𝔹} {Γ : 𝔹}
    (Hy : Γ ≤ y ∈ᴮ omegaTwo) (Hentry : Γ ≤ entryValid color δ R S Y X top y Z) :
    Γ ≤ pair y Z ∈ᴮ (entrySpace : bSet 𝔹) :=
  prod_mem Hy (mem_powerset_iff.mpr
    (subset_prod_of_is_function (Hentry.trans inf_le_left)))

/-- A full next entry exists, with all row coordinates and the vertex
bounded. The proper ideals may vary over rows by an internal existential. -/
theorem exists_bounded_next_entry
    {color : Bool} {δ R S Y X top : bSet 𝔹} {Γ : 𝔹}
    (Hδ : Γ ≤ δ ∈ᴮ omegaOne) (Htop : Γ ≤ top ∈ᴮ omegaTwo)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (HY : Γ ≤ is_func' δ omegaTwo Y)
    (HX : Γ ≤ is_func' (prod δ omegaOne) omegaOne X)
    (Hrows : Γ ≤ ⨅ σ, _root_.imp (σ ∈ᴮ omegaOne) (⨆ J, rowIdealData S σ J)) :
    ∃ y Z : bSet 𝔹, Γ ≤ y ∈ᴮ omegaTwo ⊓ entryValid color δ R S Y X top y Z := by
  obtain ⟨Z, HZ⟩ := exists_simultaneous_row_choices Hδ Htop HS HY HX Hrows
  obtain ⟨y, Hy⟩ := exists_next_vertex (color := color) (δ := δ) (R := R)
    (S := S) (Y := Y) (X := X) (Z := Z) Htop
  exact ⟨y, Z, le_inf (Hy.trans inf_le_left)
    (le_inf (HZ.trans inf_le_left)
      (le_inf (HZ.trans inf_le_right) (Hy.trans inf_le_right)))⟩

/-- The constructed entry is a member of one fixed actual set of possible
entries, suitable for set-sized prefix recursion. -/
theorem exists_next_entry
    {color : Bool} {δ R S Y X top : bSet 𝔹} {Γ : 𝔹}
    (Hδ : Γ ≤ δ ∈ᴮ omegaOne) (Htop : Γ ≤ top ∈ᴮ omegaTwo)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (HY : Γ ≤ is_func' δ omegaTwo Y)
    (HX : Γ ≤ is_func' (prod δ omegaOne) omegaOne X)
    (Hrows : Γ ≤ ⨅ σ, _root_.imp (σ ∈ᴮ omegaOne) (⨆ J, rowIdealData S σ J)) :
    ∃ y Z : bSet 𝔹, Γ ≤ pair y Z ∈ᴮ (entrySpace : bSet 𝔹) ⊓
      entryValid color δ R S Y X top y Z := by
  obtain ⟨y, Z, H⟩ := exists_bounded_next_entry (color := color) (R := R)
    Hδ Htop HS HY HX Hrows
  exact ⟨y, Z, le_inf (entryValid_mem_entrySpace (H.trans inf_le_left)
    (H.trans inf_le_right)) (H.trans inf_le_right)⟩

end bSet.ErdosSimultaneousEntry
