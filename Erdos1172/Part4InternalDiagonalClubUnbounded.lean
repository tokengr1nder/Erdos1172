/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalDiagonalClubs
public import Erdos1172.Part4InternalClubIntersection

@[expose] public section

/-!
# Unboundedness of the internal omega-two diagonal club

At each step an actual point is chosen in the intersection of all clubs
indexed below the current ordinal. The supremum of the constructed
omega-sequence is a limit point of every club indexed below it. Two
Boolean numeral joins handle arbitrary mixed indices and test bounds;
no external witness numeral, successful run, or stationary-set principle
is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosClubs

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIndexedIntersection ErdosOmegaTwoSequenceSup

/-- The family below an actual omega-two member is internally omega-one
small, so its full club intersection supplies the next point. -/
theorem exists_diagonal_step {F a : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HF : Γ ≤ is_func' omegaTwo (bv_powerset omegaTwo) F)
    (Hclubs : Γ ≤ ⨅ i, ⨅ C, _root_.imp (i ∈ᴮ omegaTwo ⊓ pair i C ∈ᴮ F) (club omegaTwo C))
    (Ha : Γ ≤ a ∈ᴮ omegaTwo) :
    ∃ b : bSet 𝔹, Γ ≤ b ∈ᴮ omegaTwo ⊓ (a ∈ᴮ b ⊓ b ∈ᴮ indexedIntersection omegaTwo F a) := by
  have HaSub : Γ ≤ a ⊆ᴮ omegaTwo := subset_of_mem_Ord Ha omegaTwo_Ord
  have Hrestricted : Γ ≤ ⨅ i, ⨅ C, _root_.imp (i ∈ᴮ a ⊓ pair i C ∈ᴮ F) (club omegaTwo C) := by
    apply le_iInf
    intro i
    apply le_iInf
    intro C
    rw [← deduction]
    exact (le_inf (inf_le_left.trans
      (Hclubs.trans ((iInf_le _ i).trans (iInf_le _ C))))
      (le_inf (mem_of_mem_subset (inf_le_left.trans HaSub)
        (inf_le_right.trans inf_le_left)) (inf_le_right.trans inf_le_right))).trans
      bv_imp_elim
  obtain ⟨b, Hb⟩ := exists_common_above HCH (is_func'_subset_of_is_func' HF HaSub)
    (omegaTwo_member_injects Ha) Hrestricted Ha
  exact ⟨b, le_inf (Hb.trans (inf_le_left.trans inf_le_right))
    (le_inf (Hb.trans inf_le_right) (Hb.trans (inf_le_left.trans inf_le_left)))⟩

private theorem sequence_mem_of_lt {v : ℕ → bSet 𝔹} {Γ : 𝔹}
    (Hv : ∀ n, Γ ≤ v n ∈ᴮ omegaTwo)
    (Hstep : ∀ n, Γ ≤ v n ∈ᴮ v (n + 1))
    {m n : ℕ} (Hmn : m < n) : Γ ≤ v m ∈ᴮ v n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases H : m = n
      · subst m
        exact Hstep n
      · exact mem_of_mem_Ord (ih (by omega)) (Hstep n)
          (Ord_of_mem_Ord (Hv (n + 1)) omegaTwo_Ord)

/-- Prefix-intersection hits make every club indexed below the supremum
unbounded below that supremum. Both numeral disjunctions are distributed
under their current Boolean conditions. -/
theorem sequenceSup_unbounded_of_prefix_intersections
    {v : ℕ → bSet 𝔹} {F i C : bSet 𝔹} {Γ : 𝔹}
    (Hv : ∀ n, Γ ≤ v n ∈ᴮ omegaTwo)
    (Hstep : ∀ n, Γ ≤ v n ∈ᴮ v (n + 1))
    (Hhits : ∀ n, Γ ≤ v (n + 1) ∈ᴮ indexedIntersection omegaTwo F (v n))
    (Hi : Γ ≤ i ∈ᴮ sequenceSup v) (Hpair : Γ ≤ pair i C ∈ᴮ F) :
    Γ ≤ unboundedIn (sequenceSup v) C := by
  have Hindices : Γ ≤ ⨆ n : ℕ, i ∈ᴮ v n := (mem_sequenceSup_iff Hv).mp Hi
  apply (le_inf (le_refl Γ) Hindices).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro n
  apply le_iInf
  intro t
  rw [← deduction]
  let Δ := (Γ ⊓ i ∈ᴮ v n) ⊓ t ∈ᴮ sequenceSup v
  have Htests : Δ ≤ ⨆ m : ℕ, t ∈ᴮ v m :=
    (mem_sequenceSup_iff (fun k => inf_le_left.trans (inf_le_left.trans (Hv k)))).mp
      inf_le_right
  apply (le_inf (le_refl Δ) Htests).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro m
  let Λ := Δ ⊓ t ∈ᴮ v m
  have HΛ : Λ ≤ Γ := inf_le_left.trans (inf_le_left.trans inf_le_left)
  let k := n + m + 1
  have Hin : Λ ≤ i ∈ᴮ v n := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have Hik : Λ ≤ i ∈ᴮ v k := mem_of_mem_Ord Hin
    (HΛ.trans (sequence_mem_of_lt Hv Hstep (show n < k by dsimp [k]; omega)))
    (Ord_of_mem_Ord (HΛ.trans (Hv k)) omegaTwo_Ord)
  have Htnext : Λ ≤ t ∈ᴮ v (k + 1) := mem_of_mem_Ord
    (show Λ ≤ t ∈ᴮ v m from inf_le_right)
    (HΛ.trans (sequence_mem_of_lt Hv Hstep (show m < k + 1 by dsimp [k]; omega)))
    (Ord_of_mem_Ord (HΛ.trans (Hv (k + 1))) omegaTwo_Ord)
  have HnextC : Λ ≤ v (k + 1) ∈ᴮ C :=
    (le_inf (HΛ.trans ((mem_indexedIntersection_iff.mp (Hhits k)).2.trans
      ((iInf_le _ i).trans (iInf_le _ C)))) (le_inf Hik (HΛ.trans Hpair))).trans
      bv_imp_elim
  have HnextSup : Λ ≤ v (k + 1) ∈ᴮ sequenceSup v :=
    HΛ.trans (sequence_value_mem_sup Hv Hstep (k + 1))
  exact le_iSup_of_le (v (k + 1)) (le_inf (le_inf HnextC HnextSup) Htnext)

/-- A strictly later member of the actual diagonal intersection is
constructed at the original Boolean condition. -/
theorem exists_diagonal_above {F a : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HF : Γ ≤ is_func' omegaTwo (bv_powerset omegaTwo) F)
    (Hclubs : Γ ≤ ⨅ i, ⨅ C, _root_.imp (i ∈ᴮ omegaTwo ⊓ pair i C ∈ᴮ F) (club omegaTwo C))
    (Ha : Γ ≤ a ∈ᴮ omegaTwo) :
    ∃ b : bSet 𝔹, Γ ≤ (b ∈ᴮ diagonalClub F ⊓ b ∈ᴮ omegaTwo) ⊓ a ∈ᴮ b := by
  classical
  have step (x : {x : bSet 𝔹 // Γ ≤ x ∈ᴮ omegaTwo}) :
      ∃ y : {y : bSet 𝔹 // Γ ≤ y ∈ᴮ omegaTwo},
        Γ ≤ x.val ∈ᴮ y.val ⊓ y.val ∈ᴮ indexedIntersection omegaTwo F x.val := by
    obtain ⟨y, Hy⟩ := exists_diagonal_step HCH HF Hclubs x.property
    exact ⟨⟨y, Hy.trans inf_le_left⟩, Hy.trans inf_le_right⟩
  let next (x : {x : bSet 𝔹 // Γ ≤ x ∈ᴮ omegaTwo}) := Classical.choose (step x)
  have Hnext (x : {x : bSet 𝔹 // Γ ≤ x ∈ᴮ omegaTwo}) :
      Γ ≤ x.val ∈ᴮ (next x).val ⊓ (next x).val ∈ᴮ indexedIntersection omegaTwo F x.val :=
    Classical.choose_spec (step x)
  let seq : ℕ → {x : bSet 𝔹 // Γ ≤ x ∈ᴮ omegaTwo} := fun n => Nat.rec ⟨a, Ha⟩ (fun _ x => next x) n
  let v (n : ℕ) : bSet 𝔹 := (seq n).val
  have Hv (n : ℕ) : Γ ≤ v n ∈ᴮ omegaTwo := (seq n).property
  have Hstep (n : ℕ) : Γ ≤ v n ∈ᴮ v (n + 1) ⊓
      v (n + 1) ∈ᴮ indexedIntersection omegaTwo F (v n) := by
    change Γ ≤ (seq n).val ∈ᴮ (next (seq n)).val ⊓
      (next (seq n)).val ∈ᴮ indexedIntersection omegaTwo F (seq n).val
    exact Hnext (seq n)
  have Hinc (n : ℕ) : Γ ≤ v n ∈ᴮ v (n + 1) := (Hstep n).trans inf_le_left
  have Hhits (n : ℕ) : Γ ≤ v (n + 1) ∈ᴮ indexedIntersection omegaTwo F (v n) :=
    (Hstep n).trans inf_le_right
  have Hsup : Γ ≤ sequenceSup v ∈ᴮ omegaTwo := sequenceSup_mem_omegaTwo HCH Hv
  have Hne : Γ ≤ (sequenceSup v =ᴮ (∅ : bSet 𝔹))ᶜ := sequenceSup_nonempty Hv Hinc
  have Hdiag : Γ ≤ sequenceSup v ∈ᴮ diagonalClub F := by
    apply mem_diagonalClub_iff.mpr
    refine ⟨Hsup, ?_⟩
    apply le_iInf
    intro i
    apply le_iInf
    intro C
    rw [← deduction]
    let Δ := Γ ⊓ (i ∈ᴮ sequenceSup v ⊓ pair i C ∈ᴮ F)
    have Hi : Δ ≤ i ∈ᴮ omegaTwo := mem_of_mem_Ord
      (inf_le_right.trans inf_le_left) (inf_le_left.trans Hsup) omegaTwo_Ord
    have HC : Δ ≤ club omegaTwo C :=
      (le_inf (inf_le_left.trans (Hclubs.trans ((iInf_le _ i).trans (iInf_le _ C))))
        (le_inf Hi (inf_le_right.trans inf_le_right))).trans bv_imp_elim
    exact closedIn_apply (club_closed HC) (inf_le_left.trans Hsup)
      (inf_le_left.trans Hne)
      (sequenceSup_unbounded_of_prefix_intersections
        (fun n => inf_le_left.trans (Hv n)) (fun n => inf_le_left.trans (Hinc n))
        (fun n => inf_le_left.trans (Hhits n))
        (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right))
  have Habove : Γ ≤ a ∈ᴮ sequenceSup v := by
    change Γ ≤ v 0 ∈ᴮ sequenceSup v
    exact sequence_value_mem_sup Hv Hinc 0
  exact ⟨sequenceSup v, le_inf (le_inf Hdiag Hsup) Habove⟩

theorem unboundedIn_diagonalClub {F : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HF : Γ ≤ is_func' omegaTwo (bv_powerset omegaTwo) F)
    (Hclubs : Γ ≤ ⨅ i, ⨅ C, _root_.imp (i ∈ᴮ omegaTwo ⊓ pair i C ∈ᴮ F) (club omegaTwo C)) :
    Γ ≤ unboundedIn omegaTwo (diagonalClub F) := by
  apply le_iInf
  intro a
  rw [← deduction]
  obtain ⟨b, Hb⟩ := exists_diagonal_above (inf_le_left.trans HCH)
    (inf_le_left.trans HF) (inf_le_left.trans Hclubs)
    (show Γ ⊓ a ∈ᴮ omegaTwo ≤ a ∈ᴮ omegaTwo from inf_le_right)
  exact le_iSup_of_le b Hb

/-- Internal CH and the actual total club-valued graph imply that its
diagonal intersection is an internal omega-two club. -/
theorem club_diagonalClub {F : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HF : Γ ≤ is_func' omegaTwo (bv_powerset omegaTwo) F)
    (Hclubs : Γ ≤ ⨅ i, ⨅ C, _root_.imp (i ∈ᴮ omegaTwo ⊓ pair i C ∈ᴮ F) (club omegaTwo C)) :
    Γ ≤ club omegaTwo (diagonalClub F) := by
  refine le_inf diagonalClub_subset (le_inf (unboundedIn_diagonalClub HCH HF Hclubs) ?_)
  apply closedIn_diagonalClub
  apply le_iInf
  intro i
  apply le_iInf
  intro C
  rw [← deduction]
  exact club_closed ((le_inf
    (inf_le_left.trans (Hclubs.trans ((iInf_le _ i).trans (iInf_le _ C))))
    inf_le_right).trans bv_imp_elim)

end bSet.ErdosClubs
