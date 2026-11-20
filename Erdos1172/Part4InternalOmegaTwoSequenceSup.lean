/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalOmegaTwoBounded
public import Erdos1172.Part4InternalCountableImage

@[expose] public section

/-!
# Suprema of actual internal omega-sequence graphs

The bounded range includes all mixed internal values of the sequence graph.
Its union is a member of omega-two under CH. Increasing steps put every
sequence value strictly below the union and make it nonempty. Cofinality
is expressed as a Boolean join over numeral indices; no external index
witness is extracted from that join.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosOmegaTwoSequenceSup

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosOmegaSequence ErdosCountableImage ErdosOmegaTwoBounded

def sequenceRange (v : ℕ → bSet 𝔹) : bSet 𝔹 :=
  image bSet.omega omegaTwo (sequenceGraph v)

def sequenceSup (v : ℕ → bSet 𝔹) : bSet 𝔹 :=
  bv_union (sequenceRange v)

theorem sequence_value_mem_range {v : ℕ → bSet 𝔹} {Γ : 𝔹}
    (Hv : ∀ n, Γ ≤ v n ∈ᴮ omegaTwo) (n : ℕ) :
    Γ ≤ v n ∈ᴮ sequenceRange v :=
  mem_image sequenceGraph_pair of_nat_mem_omega (Hv n)

/-- Bounded image membership accounts for arbitrary Boolean mixtures of
the displayed values, rather than asserting an external witness index. -/
theorem mem_sequenceRange_iff {v : ℕ → bSet 𝔹} {x : bSet 𝔹} {Γ : 𝔹}
    (Hv : ∀ n, Γ ≤ v n ∈ᴮ omegaTwo) :
    (Γ ≤ x ∈ᴮ sequenceRange v) ↔ Γ ≤ ⨆ n : ℕ, x =ᴮ v n := by
  constructor
  · intro Hx
    have Hrange := (mem_image_iff.mp Hx).2
    obtain ⟨i, Hi⟩ := exists_convert Hrange
      (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    have Hgraph := Hi.trans inf_le_right
    rw [mem_sequenceGraph] at Hgraph
    apply Hgraph.trans
    apply iSup_le
    intro n
    exact le_iSup_of_le n.down (eq_of_eq_pair_right' le_rfl)
  · intro Hx
    apply (le_inf (le_refl Γ) Hx).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro n
    exact mem_congr (bv_symm inf_le_right) bv_refl
      (inf_le_left.trans (sequence_value_mem_range Hv n))

/-- The union membership law is exact under the local value bounds. -/
theorem mem_sequenceSup_iff {v : ℕ → bSet 𝔹} {a : bSet 𝔹} {Γ : 𝔹}
    (Hv : ∀ n, Γ ≤ v n ∈ᴮ omegaTwo) :
    (Γ ≤ a ∈ᴮ sequenceSup v) ↔ Γ ≤ ⨆ n : ℕ, a ∈ᴮ v n := by
  constructor
  · intro Ha
    obtain ⟨x, Hx⟩ := exists_convert (mem_bv_union_iff.mp Ha)
      (B_ext_inf B_ext_mem_left B_ext_mem_right)
    have Hindices := (mem_sequenceRange_iff Hv).mp (Hx.trans inf_le_left)
    apply (le_inf (le_refl Γ) Hindices).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro n
    exact le_iSup_of_le n
      (mem_congr bv_refl inf_le_right (inf_le_left.trans (Hx.trans inf_le_right)))
  · intro Ha
    apply (le_inf (le_refl Γ) Ha).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro n
    exact mem_bv_union_iff.mpr (le_iSup_of_le (v n)
      (le_inf (inf_le_left.trans (sequence_value_mem_range Hv n)) inf_le_right))

theorem sequenceRange_countable {v : ℕ → bSet 𝔹} {Γ : 𝔹}
    (Hv : ∀ n, Γ ≤ v n ∈ᴮ omegaTwo) :
    Γ ≤ injects_into (sequenceRange v) bSet.omega :=
  image_countable_of_function (sequenceGraph_is_function Hv) injects_into_refl

/-- Countability of the actual image supplies the small-family premise
of internal omega-two boundedness. Increasingness is unnecessary here. -/
theorem sequenceSup_mem_omegaTwo {v : ℕ → bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (Hv : ∀ n, Γ ≤ v n ∈ᴮ omegaTwo) :
    Γ ≤ sequenceSup v ∈ᴮ omegaTwo :=
  union_mem_omegaTwo HCH image_subset
    (injects_into_trans (sequenceRange_countable Hv)
      (injects_into_of_subset (subset_of_mem_Ord omega_mem_omegaOne omegaOne_Ord)))

theorem sequence_value_mem_sup {v : ℕ → bSet 𝔹} {Γ : 𝔹}
    (Hv : ∀ n, Γ ≤ v n ∈ᴮ omegaTwo)
    (Hstep : ∀ n, Γ ≤ v n ∈ᴮ v (n + 1)) (n : ℕ) :
    Γ ≤ v n ∈ᴮ sequenceSup v :=
  (mem_sequenceSup_iff Hv).mpr (le_iSup_of_le (n + 1) (Hstep n))

theorem sequenceSup_nonempty {v : ℕ → bSet 𝔹} {Γ : 𝔹}
    (Hv : ∀ n, Γ ≤ v n ∈ᴮ omegaTwo)
    (Hstep : ∀ n, Γ ≤ v n ∈ᴮ v (n + 1)) :
    Γ ≤ (sequenceSup v =ᴮ (∅ : bSet 𝔹))ᶜ :=
  nonempty_of_exists_mem (sequenceSup v)
    (le_iSup_of_le (v 0) (sequence_value_mem_sup Hv Hstep 0))

/-- Internal witnesses in every successive interval are unbounded below
the supremum. The target is the exact unboundedness value, without importing
a club predicate. The interval witnesses and numeral joins remain local. -/
theorem interval_points_cofinal {v : ℕ → bSet 𝔹} {C : bSet 𝔹} {Γ : 𝔹}
    (Hv : ∀ n, Γ ≤ v n ∈ᴮ omegaTwo)
    (Hinterval : ∀ n, Γ ≤ ⨆ c, c ∈ᴮ C ⊓ (v n ∈ᴮ c ⊓ c ∈ᴮ v (n + 1))) :
    Γ ≤ ⨅ a, _root_.imp (a ∈ᴮ sequenceSup v)
      (⨆ c, (c ∈ᴮ C ⊓ c ∈ᴮ sequenceSup v) ⊓ a ∈ᴮ c) := by
  apply le_iInf
  intro a
  rw [← deduction]
  let Δ := Γ ⊓ a ∈ᴮ sequenceSup v
  have Hindices : Δ ≤ ⨆ n : ℕ, a ∈ᴮ v n :=
    (mem_sequenceSup_iff (fun n => inf_le_left.trans (Hv n))).mp inf_le_right
  apply (le_inf (le_refl Δ) Hindices).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro n
  let Λ := Δ ⊓ a ∈ᴮ v n
  have Hpoints : Λ ≤ ⨆ c, c ∈ᴮ C ⊓ (v n ∈ᴮ c ⊓ c ∈ᴮ v (n + 1)) :=
    inf_le_left.trans (inf_le_left.trans (Hinterval n))
  apply (le_inf (le_refl Λ) Hpoints).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro c
  let Θ := Λ ⊓ (c ∈ᴮ C ⊓ (v n ∈ᴮ c ⊓ c ∈ᴮ v (n + 1)))
  have HΘ : Θ ≤ Γ := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have Hcnext : Θ ≤ c ∈ᴮ v (n + 1) :=
    inf_le_right.trans (inf_le_right.trans inf_le_right)
  have HcOrd : Θ ≤ Ord c := Ord_of_mem_Ord Hcnext
    (Ord_of_mem_Ord (HΘ.trans (Hv (n + 1))) omegaTwo_Ord)
  have Hac : Θ ≤ a ∈ᴮ c := mem_of_mem_Ord
    (inf_le_left.trans inf_le_right)
    (inf_le_right.trans (inf_le_right.trans inf_le_left)) HcOrd
  have Hcsup : Θ ≤ c ∈ᴮ sequenceSup v :=
    (mem_sequenceSup_iff (fun m => HΘ.trans (Hv m))).mpr
      (le_iSup_of_le (n + 1) Hcnext)
  exact le_iSup_of_le c (le_inf
    (le_inf (inf_le_right.trans inf_le_left) Hcsup) Hac)

end bSet.ErdosOmegaTwoSequenceSup
