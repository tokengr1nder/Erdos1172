/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSimultaneousEntry

@[expose] public section

/-!
The vertex decoder is a fixed bounded graph, independent of any selected
prefix domain. It reads the first coordinate of each stored entry. Global
functionality follows from functionality of the entry graph, while weak
totality is proved only on the guarded prefix. Later graph support is
retained and does not require an externally coherent family of names.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousHistory

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosRelationGraph ErdosSimultaneousEntry

def vertexRel (P i y : bSet 𝔹) : 𝔹 :=
  ⨆ Z, pair i (pair y Z) ∈ᴮ P

def vertexHistory (P : bSet 𝔹) : bSet 𝔹 :=
  relationGraph omegaOne omegaTwo (vertexRel P)

theorem vertexRel_ext_index (P y : bSet 𝔹) : B_ext (fun i => vertexRel P i y) :=
  B_ext_iSup (h := fun _ => B_ext_pair_mem_left)

theorem vertexRel_ext_value (P i : bSet 𝔹) : B_ext (vertexRel P i) :=
  B_ext_iSup (h := fun _ =>
    B_ext_pair_left (ϕ := fun e => pair i e ∈ᴮ P) B_ext_pair_mem_right)

theorem vertexRel_witness {P i y : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ vertexRel P i y) :
    ∃ Z : bSet 𝔹, Γ ≤ pair i (pair y Z) ∈ᴮ P :=
  exists_convert H
    (B_ext_pair_right (ϕ := fun e => pair i e ∈ᴮ P) B_ext_pair_mem_right)

theorem mem_vertexHistory_iff {P i y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair i y ∈ᴮ vertexHistory P ↔
      Γ ≤ i ∈ᴮ omegaOne ∧ Γ ≤ y ∈ᴮ omegaTwo ∧ Γ ≤ vertexRel P i y :=
  mem_relationGraph_iff (vertexRel_ext_index P) (vertexRel_ext_value P)

/-- The original condition is preserved when the entry's row component
is extracted from the internal existential. -/
theorem vertexHistory_witness {P i y : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ pair i y ∈ᴮ vertexHistory P) :
    ∃ Z : bSet 𝔹, Γ ≤ pair i (pair y Z) ∈ᴮ P :=
  vertexRel_witness (mem_vertexHistory_iff.mp H).2.2

theorem vertexHistory_pair_of_entry {P i y Z : bSet 𝔹} {Γ : 𝔹}
    (Hi : Γ ≤ i ∈ᴮ omegaOne) (Hy : Γ ≤ y ∈ᴮ omegaTwo)
    (Hentry : Γ ≤ pair i (pair y Z) ∈ᴮ P) :
    Γ ≤ pair i y ∈ᴮ vertexHistory P :=
  mem_vertexHistory_iff.mpr ⟨Hi, Hy, le_iSup_of_le Z Hentry⟩

theorem vertexHistory_subset {P : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ vertexHistory P ⊆ᴮ prod omegaOne omegaTwo :=
  relationGraph_subset

theorem vertexHistory_mono {P Q : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ P ⊆ᴮ Q) : Γ ≤ vertexHistory P ⊆ᴮ vertexHistory Q := by
  rw [subset_unfold']
  apply le_iInf
  intro e
  rw [← deduction]
  let Δ := Γ ⊓ e ∈ᴮ vertexHistory P
  have Hprod : Δ ≤ e ∈ᴮ prod omegaOne omegaTwo :=
    mem_of_mem_subset vertexHistory_subset inf_le_right
  obtain ⟨i, Hi, y, Hy, He⟩ := mem_prod_iff₂.mp Hprod
  have Hpair : Δ ≤ pair i y ∈ᴮ vertexHistory P := mem_congr He bv_refl inf_le_right
  obtain ⟨Z, Hentry⟩ := vertexHistory_witness Hpair
  have HpairQ : Δ ≤ pair i y ∈ᴮ vertexHistory Q := vertexHistory_pair_of_entry Hi Hy
    (mem_of_mem_subset (inf_le_left.trans Hsub) Hentry)
  exact mem_congr (bv_symm He) bv_refl HpairQ

/-- Congruence is unconditional: it does not require functional or total
entry graphs, or a specific representation of a prefix. -/
theorem vertexHistory_congr : B_congr (vertexHistory : bSet 𝔹 → bSet 𝔹) := by
  intro P Q Γ H
  exact subset_ext (vertexHistory_mono (subset_of_eq H))
    (vertexHistory_mono (subset_of_eq (bv_symm H)))

theorem vertexHistory_value_eq {P i j y z : bSet 𝔹} {Γ : 𝔹}
    (HPfunc : Γ ≤ is_func P) (Hij : Γ ≤ i =ᴮ j)
    (Hiy : Γ ≤ pair i y ∈ᴮ vertexHistory P)
    (Hjz : Γ ≤ pair j z ∈ᴮ vertexHistory P) : Γ ≤ y =ᴮ z := by
  obtain ⟨Y, HiY⟩ := vertexHistory_witness Hiy
  obtain ⟨Z, HjZ⟩ := vertexHistory_witness Hjz
  exact eq_of_eq_pair_left' (eq_of_is_func_of_eq HPfunc Hij HiY HjZ)

/-- Taking the first component of entries preserves global functionality.
The row components need not themselves be functions for this statement. -/
theorem vertexHistory_is_func {P : bSet 𝔹} {Γ : 𝔹}
    (HPfunc : Γ ≤ is_func P) : Γ ≤ is_func (vertexHistory P) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro j
  apply le_iInf
  intro y
  apply le_iInf
  intro z
  rw [← deduction, ← deduction]
  exact vertexHistory_value_eq (inf_le_left.trans (inf_le_left.trans HPfunc))
    inf_le_right (inf_le_left.trans (inf_le_right.trans inf_le_left))
    (inf_le_left.trans (inf_le_right.trans inf_le_right))

/-- Weak totality on a prefix suffices. The fixed decoder may also retain
pairs at later omega-one coordinates; no prefix support is silently imposed. -/
theorem vertexHistory_is_func' {δ P : bSet 𝔹} {Γ : 𝔹}
    (Hδ : Γ ≤ δ ⊆ᴮ omegaOne) (HP : Γ ≤ is_func' δ entrySpace P) :
    Γ ≤ is_func' δ omegaTwo (vertexHistory P) := by
  refine le_inf (vertexHistory_is_func (HP.trans inf_le_left)) ?_
  apply le_iInf
  intro i
  rw [← deduction]
  let Δ := Γ ⊓ i ∈ᴮ δ
  have Hex : Δ ≤ ⨆ e, e ∈ᴮ entrySpace ⊓ pair i e ∈ᴮ P :=
    (le_inf (inf_le_left.trans ((HP.trans inf_le_right).trans (iInf_le _ i)))
      inf_le_right).trans bv_imp_elim
  obtain ⟨e, He⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hprod : Δ ≤ e ∈ᴮ prod omegaTwo (bv_powerset (prod omegaOne omegaOne)) :=
    He.trans inf_le_left
  obtain ⟨y, Hy, Z, _, HePair⟩ := mem_prod_iff₂.mp Hprod
  have Hentry : Δ ≤ pair i (pair y Z) ∈ᴮ P :=
    bv_rw'' (ϕ := fun a => pair i a ∈ᴮ P) HePair (He.trans inf_le_right)
      B_ext_pair_mem_right
  exact le_iSup_of_le y (le_inf Hy (vertexHistory_pair_of_entry
    (mem_of_mem_subset (inf_le_left.trans Hδ) inf_le_right) Hy Hentry))

end bSet.ErdosSimultaneousHistory
