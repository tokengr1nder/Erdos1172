/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalClubs
public import Erdos1172.Part4InternalOmegaTwo
public import Erdos1172.Part4InternalRelationGraph

@[expose] public section

/-!
# The actual internal diagonal intersection of closed sets

Every graph value at an index below the candidate is constrained. Closure
requires neither functionality nor totality of the family and has no CH
premise. The common-upper-point helper keeps arbitrary internal ordinals
and all Boolean case distinctions at the original condition.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosClubs

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo

def diagonalClub (F : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun a => ⨅ i, ⨅ C,
    _root_.imp (i ∈ᴮ a ⊓ pair i C ∈ᴮ F) (a ∈ᴮ C)) omegaTwo

theorem mem_diagonalClub_iff {F a : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ a ∈ᴮ diagonalClub F ↔
      Γ ≤ a ∈ᴮ omegaTwo ∧ Γ ≤ ⨅ i, ⨅ C,
        _root_.imp (i ∈ᴮ a ⊓ pair i C ∈ᴮ F) (a ∈ᴮ C) :=
  ErdosRelationGraph.mem_comprehend_and
    (B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_inf B_ext_mem_right B_ext_const)
        (h₂ := B_ext_mem_left))))

theorem diagonalClub_subset {F : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ diagonalClub F ⊆ᴮ omegaTwo :=
  comprehend_subset (ϕ := fun a => ⨅ i, ⨅ C,
    _root_.imp (i ∈ᴮ a ⊓ pair i C ∈ᴮ F) (a ∈ᴮ C)) omegaTwo

theorem diagonalClub_apply {F a i C : bSet 𝔹} {Γ : 𝔹}
    (Ha : Γ ≤ a ∈ᴮ diagonalClub F) (Hi : Γ ≤ i ∈ᴮ a)
    (HC : Γ ≤ pair i C ∈ᴮ F) : Γ ≤ a ∈ᴮ C :=
  (le_inf ((mem_diagonalClub_iff.mp Ha).2.trans
    ((iInf_le _ i).trans (iInf_le _ C))) (le_inf Hi HC)).trans bv_imp_elim

/-- A point of an unbounded set above two prescribed ordinal members.
The final witness is one actual name at the original Boolean condition. -/
theorem exists_unbounded_above_two {κ C a b : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ) (HU : Γ ≤ unboundedIn κ C)
    (Ha : Γ ≤ a ∈ᴮ κ) (Hb : Γ ≤ b ∈ᴮ κ) :
    ∃ z : bSet 𝔹, Γ ≤ (z ∈ᴮ C ⊓ z ∈ᴮ κ) ⊓ (a ∈ᴮ z ⊓ b ∈ᴮ z) := by
  have Hex : Γ ≤ ⨆ z, (z ∈ᴮ C ⊓ z ∈ᴮ κ) ⊓ (a ∈ᴮ z ⊓ b ∈ᴮ z) := by
    have Htri := epsilon_trichotomy_of_Ord Ha Hb Hκ
    apply (le_inf (le_refl Γ) Htri).trans
    rw [inf_sup_left, inf_sup_left]
    apply sup_le
    · apply sup_le
      · obtain ⟨z, Hz⟩ := exists_unbounded_above (inf_le_left.trans HU)
          (inf_le_left.trans Hb)
        exact le_iSup_of_le z (le_inf (Hz.trans inf_le_left)
          (le_inf (mem_congr (bv_symm inf_le_right) bv_refl (Hz.trans inf_le_right))
            (Hz.trans inf_le_right)))
      · obtain ⟨z, Hz⟩ := exists_unbounded_above (inf_le_left.trans HU)
          (inf_le_left.trans Hb)
        exact le_iSup_of_le z (le_inf (Hz.trans inf_le_left)
          (le_inf (mem_of_mem_Ord inf_le_right (Hz.trans inf_le_right)
            (Ord_of_mem_Ord (Hz.trans (inf_le_left.trans inf_le_right))
              (inf_le_left.trans Hκ))) (Hz.trans inf_le_right)))
    · obtain ⟨z, Hz⟩ := exists_unbounded_above (inf_le_left.trans HU)
        (inf_le_left.trans Ha)
      exact le_iSup_of_le z (le_inf (Hz.trans inf_le_left)
        (le_inf (Hz.trans inf_le_right)
          (mem_of_mem_Ord inf_le_right (Hz.trans inf_le_right)
            (Ord_of_mem_Ord (Hz.trans (inf_le_left.trans inf_le_right))
              (inf_le_left.trans Hκ)))))
  exact exists_convert Hex
    (B_ext_inf (B_ext_inf B_ext_mem_left B_ext_mem_left)
      (B_ext_inf B_ext_mem_right B_ext_mem_right))

/-- Diagonal intersections of all guarded closed values are closed.
No family-function, cardinal arithmetic, or unboundedness premise on the
individual values is needed for this direction. -/
theorem closedIn_diagonalClub {F : bSet 𝔹} {Γ : 𝔹}
    (Hclosed : Γ ≤ ⨅ i, ⨅ C, _root_.imp
      (i ∈ᴮ omegaTwo ⊓ pair i C ∈ᴮ F) (closedIn omegaTwo C)) :
    Γ ≤ closedIn omegaTwo (diagonalClub F) := by
  apply le_iInf
  intro a
  rw [← deduction]
  let Δ := Γ ⊓ ((a ∈ᴮ omegaTwo ⊓ (a =ᴮ (∅ : bSet 𝔹))ᶜ) ⊓
    unboundedIn a (diagonalClub F))
  have HΔ : Δ ≤ Γ := inf_le_left
  have Ha : Δ ≤ a ∈ᴮ omegaTwo := inf_le_right.trans (inf_le_left.trans inf_le_left)
  have Hne : Δ ≤ (a =ᴮ (∅ : bSet 𝔹))ᶜ :=
    inf_le_right.trans (inf_le_left.trans inf_le_right)
  have HU : Δ ≤ unboundedIn a (diagonalClub F) := inf_le_right.trans inf_le_right
  apply mem_diagonalClub_iff.mpr
  refine ⟨Ha, ?_⟩
  apply le_iInf
  intro i
  apply le_iInf
  intro C
  rw [← deduction]
  let Λ := Δ ⊓ (i ∈ᴮ a ⊓ pair i C ∈ᴮ F)
  have HΛ : Λ ≤ Δ := inf_le_left
  have Hi : Λ ≤ i ∈ᴮ a := inf_le_right.trans inf_le_left
  have HC : Λ ≤ pair i C ∈ᴮ F := inf_le_right.trans inf_le_right
  have Hiκ : Λ ≤ i ∈ᴮ omegaTwo := mem_of_mem_Ord Hi (HΛ.trans Ha) omegaTwo_Ord
  have HclosedC : Λ ≤ closedIn omegaTwo C :=
    (le_inf (HΛ.trans (HΔ.trans
      (Hclosed.trans ((iInf_le _ i).trans (iInf_le _ C)))))
      (le_inf Hiκ HC)).trans bv_imp_elim
  have HUC : Λ ≤ unboundedIn a C := by
    apply le_iInf
    intro t
    rw [← deduction]
    let Θ := Λ ⊓ t ∈ᴮ a
    have HΘ : Θ ≤ Λ := inf_le_left
    obtain ⟨z, Hz⟩ := exists_unbounded_above_two
      (Ord_of_mem_Ord (HΘ.trans (HΛ.trans Ha)) omegaTwo_Ord)
      (HΘ.trans (HΛ.trans HU)) (HΘ.trans Hi) inf_le_right
    have HzC : Θ ≤ z ∈ᴮ C := diagonalClub_apply
      (Hz.trans (inf_le_left.trans inf_le_left))
      (Hz.trans (inf_le_right.trans inf_le_left)) (HΘ.trans HC)
    exact le_iSup_of_le z (le_inf
      (le_inf HzC (Hz.trans (inf_le_left.trans inf_le_right)))
      (Hz.trans (inf_le_right.trans inf_le_right)))
  exact closedIn_apply HclosedC (HΛ.trans Ha) (HΛ.trans Hne) HUC

end bSet.ErdosClubs
