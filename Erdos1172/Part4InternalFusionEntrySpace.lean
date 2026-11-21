/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalRelationGraph
public import Erdos1172.Part4InternalOmegaTwo

@[expose] public section

/-!
# Fixed bounded entries and decoders for the second fusion run

An entry stores a whole block (possibly empty), the entire current row
function graph, and the accumulated active point set. The ambient spaces
are powersets, not sets of countable objects: boundedness of the operators
does not assume the history is a valid reachable prefix.

Every decoder is a fixed separation graph. Changing the condition or a
proof of prefix functionality never changes the decoded name. Actual
prefix support is proved from the original graph, and flattened row
coordinates use the very same stored row graph.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionEntrySpace

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosRelationGraph

def indexCodes : bSet 𝔹 := bv_powerset (prod omegaOne omegaOne)

def entrySpace : bSet 𝔹 :=
  prod (bv_powerset omegaTwo) (prod indexCodes (bv_powerset omegaTwo))

def entry (A Z U : bSet 𝔹) : bSet 𝔹 := pair A (pair Z U)

theorem mem_entrySpace_iff {A Z U : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ entry A Z U ∈ᴮ entrySpace ↔
      Γ ≤ A ⊆ᴮ omegaTwo ∧ Γ ≤ Z ⊆ᴮ prod omegaOne omegaOne ∧ Γ ≤ U ⊆ᴮ omegaTwo := by
  change (Γ ≤ pair A (pair Z U) ∈ᴮ
    prod (bv_powerset omegaTwo) (prod indexCodes (bv_powerset omegaTwo))) ↔ _
  rw [mem_prod_iff, mem_prod_iff]
  exact and_congr mem_powerset_iff (and_congr mem_powerset_iff mem_powerset_iff)

theorem entrySpace_witness {q : bSet 𝔹} {Γ : 𝔹}
    (Hq : Γ ≤ q ∈ᴮ entrySpace) :
    ∃ A Z U : bSet 𝔹, Γ ≤ A ⊆ᴮ omegaTwo ∧ Γ ≤ Z ⊆ᴮ prod omegaOne omegaOne ∧
      Γ ≤ U ⊆ᴮ omegaTwo ∧ Γ ≤ q =ᴮ entry A Z U := by
  obtain ⟨A, HA, t, Ht, Hq⟩ := mem_prod_iff₂.mp Hq
  obtain ⟨Z, HZ, U, HU, Ht⟩ := mem_prod_iff₂.mp Ht
  exact ⟨A, Z, U, mem_powerset_iff.mp HA, mem_powerset_iff.mp HZ,
    mem_powerset_iff.mp HU, bv_trans Hq (pair_congr bv_refl Ht)⟩

def blockRel (q A : bSet 𝔹) : 𝔹 := ⨆ Z, ⨆ U, q =ᴮ entry A Z U
def indexRel (q Z : bSet 𝔹) : 𝔹 := ⨆ A, ⨆ U, q =ᴮ entry A Z U
def activeRel (q U : bSet 𝔹) : 𝔹 := ⨆ A, ⨆ Z, q =ᴮ entry A Z U

private theorem blockRel_ext_input (A : bSet 𝔹) : B_ext (fun q => blockRel q A) :=
  B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ => B_ext_bv_eq_left))

private theorem blockRel_ext_output (q : bSet 𝔹) : B_ext (blockRel q) :=
  B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
    B_ext_pair_left B_ext_bv_eq_right))

private theorem indexRel_ext_input (Z : bSet 𝔹) : B_ext (fun q => indexRel q Z) :=
  B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ => B_ext_bv_eq_left))

private theorem indexRel_ext_output (q : bSet 𝔹) : B_ext (indexRel q) :=
  B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
    B_ext_pair_left (B_ext_pair_right B_ext_bv_eq_right)))

private theorem activeRel_ext_input (U : bSet 𝔹) : B_ext (fun q => activeRel q U) :=
  B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ => B_ext_bv_eq_left))

private theorem activeRel_ext_output (q : bSet 𝔹) : B_ext (activeRel q) :=
  B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
    B_ext_pair_right (B_ext_pair_right B_ext_bv_eq_right)))

private theorem blockRel_witness {q A : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ blockRel q A) : ∃ Z U : bSet 𝔹, Γ ≤ q =ᴮ entry A Z U := by
  obtain ⟨Z, HZ⟩ := exists_convert H (B_ext_iSup (h := fun _ =>
    B_ext_pair_left (B_ext_pair_right B_ext_bv_eq_right)))
  exact ⟨Z, exists_convert HZ (B_ext_pair_right (B_ext_pair_right B_ext_bv_eq_right))⟩

private theorem indexRel_witness {q Z : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ indexRel q Z) : ∃ A U : bSet 𝔹, Γ ≤ q =ᴮ entry A Z U := by
  obtain ⟨A, HA⟩ := exists_convert H (B_ext_iSup (h := fun _ =>
    B_ext_pair_left B_ext_bv_eq_right))
  exact ⟨A, exists_convert HA (B_ext_pair_right (B_ext_pair_right B_ext_bv_eq_right))⟩

private theorem activeRel_witness {q U : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ activeRel q U) : ∃ A Z : bSet 𝔹, Γ ≤ q =ᴮ entry A Z U := by
  obtain ⟨A, HA⟩ := exists_convert H (B_ext_iSup (h := fun _ =>
    B_ext_pair_left B_ext_bv_eq_right))
  exact ⟨A, exists_convert HA (B_ext_pair_left (B_ext_pair_right B_ext_bv_eq_right))⟩

def blockProjection : bSet 𝔹 := relationGraph entrySpace (bv_powerset omegaTwo) blockRel
def indexProjection : bSet 𝔹 := relationGraph entrySpace indexCodes indexRel
def activeProjection : bSet 𝔹 := relationGraph entrySpace (bv_powerset omegaTwo) activeRel

theorem blockProjection_is_function {Γ : 𝔹} :
    Γ ≤ is_function entrySpace (bv_powerset omegaTwo) (blockProjection : bSet 𝔹) := by
  apply relationGraph_is_function blockRel_ext_input blockRel_ext_output
  · apply le_iInf
    intro q
    rw [← deduction]
    obtain ⟨A, Z, U, HA, _, _, Hq⟩ := entrySpace_witness
      (show Γ ⊓ q ∈ᴮ entrySpace ≤ q ∈ᴮ entrySpace from inf_le_right)
    exact le_iSup_of_le A (le_inf (mem_powerset_iff.mpr HA) (le_iSup_of_le Z (le_iSup_of_le U Hq)))
  · intro q t A B Δ _ _ _ _ _ Hq Ht Heq
    obtain ⟨Z, U, Hq⟩ := blockRel_witness Hq
    obtain ⟨W, V, Ht⟩ := blockRel_witness Ht
    exact eq_of_eq_pair_left' (bv_trans (bv_symm Hq) (bv_trans Heq Ht))

theorem activeProjection_is_function {Γ : 𝔹} :
    Γ ≤ is_function entrySpace (bv_powerset omegaTwo) (activeProjection : bSet 𝔹) := by
  apply relationGraph_is_function activeRel_ext_input activeRel_ext_output
  · apply le_iInf
    intro q
    rw [← deduction]
    obtain ⟨A, Z, U, _, _, HU, Hq⟩ := entrySpace_witness
      (show Γ ⊓ q ∈ᴮ entrySpace ≤ q ∈ᴮ entrySpace from inf_le_right)
    exact le_iSup_of_le U (le_inf (mem_powerset_iff.mpr HU) (le_iSup_of_le A (le_iSup_of_le Z Hq)))
  · intro q t U V Δ _ _ _ _ _ Hq Ht Heq
    obtain ⟨A, Z, Hq⟩ := activeRel_witness Hq
    obtain ⟨B, W, Ht⟩ := activeRel_witness Ht
    exact eq_of_eq_pair_right' (eq_of_eq_pair_right' (bv_trans (bv_symm Hq) (bv_trans Heq Ht)))

theorem blockProjection_pair {A Z U : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ entry A Z U ∈ᴮ entrySpace) :
    Γ ≤ pair (entry A Z U) A ∈ᴮ blockProjection :=
  (mem_relationGraph_iff blockRel_ext_input blockRel_ext_output).mpr
    ⟨H, mem_powerset_iff.mpr (mem_entrySpace_iff.mp H).1, le_iSup_of_le Z (le_iSup_of_le U bv_refl)⟩

theorem indexProjection_pair {A Z U : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ entry A Z U ∈ᴮ entrySpace) :
    Γ ≤ pair (entry A Z U) Z ∈ᴮ indexProjection :=
  (mem_relationGraph_iff indexRel_ext_input indexRel_ext_output).mpr
    ⟨H, mem_powerset_iff.mpr (mem_entrySpace_iff.mp H).2.1,
      le_iSup_of_le A (le_iSup_of_le U bv_refl)⟩

theorem activeProjection_pair {A Z U : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ entry A Z U ∈ᴮ entrySpace) :
    Γ ≤ pair (entry A Z U) U ∈ᴮ activeProjection :=
  (mem_relationGraph_iff activeRel_ext_input activeRel_ext_output).mpr
    ⟨H, mem_powerset_iff.mpr (mem_entrySpace_iff.mp H).2.2,
      le_iSup_of_le A (le_iSup_of_le Z bv_refl)⟩

def decodeRel (π T i x : bSet 𝔹) : 𝔹 :=
  ⨆ q, pair i q ∈ᴮ T ⊓ pair q x ∈ᴮ π

def decodeHistory (C π T : bSet 𝔹) : bSet 𝔹 :=
  relationGraph omegaOne C (decodeRel π T)

private theorem decodeRel_ext_input (π T x : bSet 𝔹) :
    B_ext (fun i => decodeRel π T i x) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_pair_mem_left B_ext_const)

private theorem decodeRel_ext_output (π T i : bSet 𝔹) :
    B_ext (decodeRel π T i) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_pair_mem_right)

private theorem decode_pair_iff {C π T i x : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair i x ∈ᴮ decodeHistory C π T ↔ Γ ≤ i ∈ᴮ omegaOne ∧ Γ ≤ x ∈ᴮ C ∧ Γ ≤ decodeRel π T i x :=
  mem_relationGraph_iff (decodeRel_ext_input π T) (decodeRel_ext_output π T)

private theorem decode_witness {C π T i x : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ pair i x ∈ᴮ decodeHistory C π T) :
    ∃ q : bSet 𝔹, Γ ≤ pair i q ∈ᴮ T ∧ Γ ≤ pair q x ∈ᴮ π := by
  obtain ⟨q, Hq⟩ := exists_convert (decode_pair_iff.mp H).2.2
    (B_ext_inf B_ext_pair_mem_right B_ext_pair_mem_left)
  exact ⟨q, Hq.trans inf_le_left, Hq.trans inf_le_right⟩

private theorem decode_pair {C π T i q x : bSet 𝔹} {Γ : 𝔹}
    (Hi : Γ ≤ i ∈ᴮ omegaOne) (Hx : Γ ≤ x ∈ᴮ C)
    (Hpair : Γ ≤ pair i q ∈ᴮ T) (Hπ : Γ ≤ pair q x ∈ᴮ π) :
    Γ ≤ pair i x ∈ᴮ decodeHistory C π T :=
  decode_pair_iff.mpr ⟨Hi, Hx, le_iSup_of_le q (le_inf Hpair Hπ)⟩

private theorem decode_mono {C π T Q : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ T ⊆ᴮ Q) : Γ ≤ decodeHistory C π T ⊆ᴮ decodeHistory C π Q := by
  rw [subset_unfold']
  apply le_iInf
  intro z
  rw [← deduction]
  let Δ := Γ ⊓ z ∈ᴮ decodeHistory C π T
  have Hz : Δ ≤ z ∈ᴮ prod omegaOne C := mem_of_mem_subset relationGraph_subset inf_le_right
  obtain ⟨i, Hi, x, Hx, Heq⟩ := mem_prod_iff₂.mp Hz
  obtain ⟨q, Hq, Hπ⟩ := decode_witness (C := C)
    (mem_congr Heq bv_refl (show Δ ≤ z ∈ᴮ decodeHistory C π T from inf_le_right))
  exact mem_congr (bv_symm Heq) bv_refl
    (decode_pair Hi Hx (mem_of_mem_subset (inf_le_left.trans Hsub) Hq) Hπ)

private theorem decode_congr (C π : bSet 𝔹) : B_congr (decodeHistory C π) := by
  intro T Q Γ H
  exact subset_ext (decode_mono (subset_of_eq H)) (decode_mono (subset_of_eq (bv_symm H)))

private theorem decode_function {ξ C π T : bSet 𝔹} {Γ : 𝔹}
    (Hξ : Γ ≤ ξ ⊆ᴮ omegaOne) (HT : Γ ≤ is_function ξ entrySpace T)
    (Hπ : Γ ≤ is_function entrySpace C π) :
    Γ ≤ is_function ξ C (decodeHistory C π T) := by
  refine le_inf (le_inf ?_ ?_) ?_
  · apply le_iInf
    intro i
    apply le_iInf
    intro j
    apply le_iInf
    intro x
    apply le_iInf
    intro y
    rw [← deduction, ← deduction]
    let Δ := (Γ ⊓ (pair i x ∈ᴮ decodeHistory C π T ⊓ pair j y ∈ᴮ decodeHistory C π T)) ⊓ i =ᴮ j
    have HΔ : Δ ≤ Γ := inf_le_left.trans inf_le_left
    obtain ⟨q, Hq, Hqx⟩ := decode_witness (show Δ ≤ pair i x ∈ᴮ decodeHistory C π T from
        inf_le_left.trans (inf_le_right.trans inf_le_left))
    obtain ⟨r, Hr, Hry⟩ := decode_witness (show Δ ≤ pair j y ∈ᴮ decodeHistory C π T from
        inf_le_left.trans (inf_le_right.trans inf_le_right))
    exact eq_of_is_function_of_eq (HΔ.trans Hπ)
      (eq_of_is_function_of_eq (HΔ.trans HT) inf_le_right Hq Hr) Hqx Hry
  · apply le_iInf
    intro i
    rw [← deduction]
    let Δ := Γ ⊓ i ∈ᴮ ξ
    have Hex : Δ ≤ ⨆ q, q ∈ᴮ entrySpace ⊓ pair i q ∈ᴮ T :=
      (le_inf (inf_le_left.trans ((is_total_of_is_function HT).trans (iInf_le _ i)))
        inf_le_right).trans bv_imp_elim
    obtain ⟨q, Hq⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
    have Hexx : Δ ≤ ⨆ x, x ∈ᴮ C ⊓ pair q x ∈ᴮ π :=
      (le_inf (inf_le_left.trans ((is_total_of_is_function Hπ).trans (iInf_le _ q)))
        (Hq.trans inf_le_left)).trans bv_imp_elim
    obtain ⟨x, Hx⟩ := exists_convert Hexx (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
    exact le_iSup_of_le x (le_inf (Hx.trans inf_le_left)
      (decode_pair (mem_of_mem_subset (inf_le_left.trans Hξ) inf_le_right)
        (Hx.trans inf_le_left) (Hq.trans inf_le_right) (Hx.trans inf_le_right)))
  · rw [subset_unfold']
    apply le_iInf
    intro z
    rw [← deduction]
    let Δ := Γ ⊓ z ∈ᴮ decodeHistory C π T
    obtain ⟨i, _, x, Hx, Heq⟩ := mem_prod_iff₂.mp
      (show Δ ≤ z ∈ᴮ prod omegaOne C from mem_of_mem_subset relationGraph_subset inf_le_right)
    obtain ⟨q, Hq, _⟩ := decode_witness (C := C)
      (mem_congr Heq bv_refl (show Δ ≤ z ∈ᴮ decodeHistory C π T from inf_le_right))
    exact mem_congr (bv_symm Heq) bv_refl
      (mem_prod (mem_domain_of_is_function Hq (inf_le_left.trans HT)) Hx)

def blockHistory (T : bSet 𝔹) : bSet 𝔹 :=
  decodeHistory (bv_powerset omegaTwo) blockProjection T

def indexFamily (T : bSet 𝔹) : bSet 𝔹 := decodeHistory indexCodes indexProjection T

def activeFamily (T : bSet 𝔹) : bSet 𝔹 :=
  decodeHistory (bv_powerset omegaTwo) activeProjection T

theorem blockHistory_congr : B_congr (blockHistory : bSet 𝔹 → bSet 𝔹) := decode_congr _ _
theorem activeFamily_congr : B_congr (activeFamily : bSet 𝔹 → bSet 𝔹) := decode_congr _ _

theorem blockHistory_is_function {ξ T : bSet 𝔹} {Γ : 𝔹}
    (Hξ : Γ ≤ ξ ⊆ᴮ omegaOne) (HT : Γ ≤ is_function ξ entrySpace T) :
    Γ ≤ is_function ξ (bv_powerset omegaTwo) (blockHistory T) :=
  decode_function Hξ HT blockProjection_is_function

theorem activeFamily_is_function {ξ T : bSet 𝔹} {Γ : 𝔹}
    (Hξ : Γ ≤ ξ ⊆ᴮ omegaOne) (HT : Γ ≤ is_function ξ entrySpace T) :
    Γ ≤ is_function ξ (bv_powerset omegaTwo) (activeFamily T) :=
  decode_function Hξ HT activeProjection_is_function

theorem blockHistory_pair {ξ T i A Z U : bSet 𝔹} {Γ : 𝔹}
    (Hξ : Γ ≤ ξ ⊆ᴮ omegaOne) (HT : Γ ≤ is_function ξ entrySpace T)
    (Hp : Γ ≤ pair i (entry A Z U) ∈ᴮ T) : Γ ≤ pair i A ∈ᴮ blockHistory T := by
  have Hentry := mem_codomain_of_is_function Hp HT
  exact decode_pair (mem_of_mem_subset Hξ (mem_domain_of_is_function Hp HT))
    (mem_powerset_iff.mpr (mem_entrySpace_iff.mp Hentry).1) Hp (blockProjection_pair Hentry)

theorem indexFamily_pair {ξ T i A Z U : bSet 𝔹} {Γ : 𝔹}
    (Hξ : Γ ≤ ξ ⊆ᴮ omegaOne) (HT : Γ ≤ is_function ξ entrySpace T)
    (Hp : Γ ≤ pair i (entry A Z U) ∈ᴮ T) : Γ ≤ pair i Z ∈ᴮ indexFamily T := by
  have Hentry := mem_codomain_of_is_function Hp HT
  exact decode_pair (mem_of_mem_subset Hξ (mem_domain_of_is_function Hp HT))
    (mem_powerset_iff.mpr (mem_entrySpace_iff.mp Hentry).2.1) Hp (indexProjection_pair Hentry)

theorem activeFamily_pair {ξ T i A Z U : bSet 𝔹} {Γ : 𝔹}
    (Hξ : Γ ≤ ξ ⊆ᴮ omegaOne) (HT : Γ ≤ is_function ξ entrySpace T)
    (Hp : Γ ≤ pair i (entry A Z U) ∈ᴮ T) : Γ ≤ pair i U ∈ᴮ activeFamily T := by
  have Hentry := mem_codomain_of_is_function Hp HT
  exact decode_pair (mem_of_mem_subset Hξ (mem_domain_of_is_function Hp HT))
    (mem_powerset_iff.mpr (mem_entrySpace_iff.mp Hentry).2.2) Hp (activeProjection_pair Hentry)

theorem blockHistory_witness {T i A : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ pair i A ∈ᴮ blockHistory T) :
    ∃ Z U : bSet 𝔹, Γ ≤ pair i (entry A Z U) ∈ᴮ T := by
  obtain ⟨q, Hq, Hπ⟩ := decode_witness H
  obtain ⟨Z, U, Heq⟩ := blockRel_witness
    ((mem_relationGraph_iff blockRel_ext_input blockRel_ext_output).mp Hπ).2.2
  exact ⟨Z, U, mem_congr (pair_congr bv_refl Heq) bv_refl Hq⟩

theorem indexFamily_witness {T i Z : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ pair i Z ∈ᴮ indexFamily T) :
    ∃ A U : bSet 𝔹, Γ ≤ pair i (entry A Z U) ∈ᴮ T := by
  obtain ⟨q, Hq, Hπ⟩ := decode_witness H
  obtain ⟨A, U, Heq⟩ := indexRel_witness
    ((mem_relationGraph_iff indexRel_ext_input indexRel_ext_output).mp Hπ).2.2
  exact ⟨A, U, mem_congr (pair_congr bv_refl Heq) bv_refl Hq⟩

theorem activeFamily_witness {T i U : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ pair i U ∈ᴮ activeFamily T) :
    ∃ A Z : bSet 𝔹, Γ ≤ pair i (entry A Z U) ∈ᴮ T := by
  obtain ⟨q, Hq, Hπ⟩ := decode_witness H
  obtain ⟨A, Z, Heq⟩ := activeRel_witness
    ((mem_relationGraph_iff activeRel_ext_input activeRel_ext_output).mp Hπ).2.2
  exact ⟨A, Z, mem_congr (pair_congr bv_refl Heq) bv_refl Hq⟩

def rowFunctions (T : bSet 𝔹) : 𝔹 :=
  ⨅ i, ⨅ A, ⨅ Z, ⨅ U, _root_.imp (pair i (entry A Z U) ∈ᴮ T)
    (is_function omegaOne omegaOne Z)

theorem rowFunctions_apply {T i A Z U : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ rowFunctions T) (Hp : Γ ≤ pair i (entry A Z U) ∈ᴮ T) :
    Γ ≤ is_function omegaOne omegaOne Z :=
  (le_inf (H.trans ((iInf_le _ i).trans ((iInf_le _ A).trans
    ((iInf_le _ Z).trans (iInf_le _ U))))) Hp).trans bv_imp_elim

def coordinateRel (T q v : bSet 𝔹) : 𝔹 :=
  ⨆ i, ⨆ ν, ⨆ Z, q =ᴮ pair i ν ⊓
    (pair i Z ∈ᴮ indexFamily T ⊓ pair ν v ∈ᴮ Z)

def coordinateHistory (T : bSet 𝔹) : bSet 𝔹 :=
  relationGraph (prod omegaOne omegaOne) omegaOne (coordinateRel T)

private theorem coordinateRel_ext_input (T v : bSet 𝔹) :
    B_ext (fun q => coordinateRel T q v) :=
  B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ => B_ext_iSup
    (h := fun _ => B_ext_inf B_ext_bv_eq_left B_ext_const)))

private theorem coordinateRel_ext_output (T q : bSet 𝔹) :
    B_ext (coordinateRel T q) :=
  B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ => B_ext_iSup
    (h := fun _ => B_ext_inf B_ext_const (B_ext_inf B_ext_const B_ext_pair_mem_right))))

private theorem coordinateRel_pair (T i ν v : bSet 𝔹) :
    coordinateRel T (pair i ν) v = ⨆ Z, pair i Z ∈ᴮ indexFamily T ⊓ pair ν v ∈ᴮ Z := by
  apply le_antisymm
  · unfold coordinateRel
    apply iSup_le
    intro j
    apply iSup_le
    intro μ
    apply iSup_le
    intro Z
    apply le_iSup_of_le Z
    refine le_inf ?_ ?_
    · exact bv_rw' (ϕ := fun k => pair k Z ∈ᴮ indexFamily T)
        (eq_of_eq_pair_left' inf_le_left) (h_congr := B_ext_pair_mem_left)
        (H_new := inf_le_right.trans inf_le_left)
    · exact bv_rw' (ϕ := fun k => pair k v ∈ᴮ Z)
        (eq_of_eq_pair_right' inf_le_left) (h_congr := B_ext_pair_mem_left)
        (H_new := inf_le_right.trans inf_le_right)
  · apply iSup_le
    intro Z
    exact le_iSup_of_le i (le_iSup_of_le ν (le_iSup_of_le Z (le_inf bv_refl le_rfl)))

private theorem coordinate_pair_general {T q v : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair q v ∈ᴮ coordinateHistory T ↔
      Γ ≤ q ∈ᴮ prod omegaOne omegaOne ∧ Γ ≤ v ∈ᴮ omegaOne ∧ Γ ≤ coordinateRel T q v :=
  mem_relationGraph_iff (coordinateRel_ext_input T) (coordinateRel_ext_output T)

theorem coordinateHistory_pair_iff {T i ν v : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair (pair i ν) v ∈ᴮ coordinateHistory T ↔
      Γ ≤ i ∈ᴮ omegaOne ∧ Γ ≤ ν ∈ᴮ omegaOne ∧ Γ ≤ v ∈ᴮ omegaOne ∧
        Γ ≤ ⨆ Z, pair i Z ∈ᴮ indexFamily T ⊓ pair ν v ∈ᴮ Z := by
  rw [coordinate_pair_general, coordinateRel_pair]
  constructor
  · rintro ⟨Hq, Hv, Hrel⟩
    exact ⟨(mem_prod_iff.mp Hq).1, (mem_prod_iff.mp Hq).2, Hv, Hrel⟩
  · rintro ⟨Hi, Hν, Hv, Hrel⟩
    exact ⟨mem_prod Hi Hν, Hv, Hrel⟩

private theorem coordinate_family_witness {T i ν v : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ pair (pair i ν) v ∈ᴮ coordinateHistory T) :
    ∃ Z : bSet 𝔹, Γ ≤ pair i Z ∈ᴮ indexFamily T ∧ Γ ≤ pair ν v ∈ᴮ Z := by
  obtain ⟨Z, HZ⟩ := exists_convert (coordinateHistory_pair_iff.mp H).2.2.2
    (B_ext_inf B_ext_pair_mem_right B_ext_mem_right)
  exact ⟨Z, HZ.trans inf_le_left, HZ.trans inf_le_right⟩

theorem coordinateHistory_witness {T i ν v : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ pair (pair i ν) v ∈ᴮ coordinateHistory T) :
    ∃ A Z U : bSet 𝔹, Γ ≤ pair i (entry A Z U) ∈ᴮ T ∧ Γ ≤ pair ν v ∈ᴮ Z := by
  obtain ⟨Z, HZ, Hv⟩ := coordinate_family_witness H
  obtain ⟨A, U, Hentry⟩ := indexFamily_witness HZ
  exact ⟨A, Z, U, Hentry, Hv⟩

theorem coordinateHistory_subset {T : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ coordinateHistory T ⊆ᴮ prod (prod omegaOne omegaOne) omegaOne :=
  relationGraph_subset

theorem coordinateHistory_pair {ξ T i ν v A Z U : bSet 𝔹} {Γ : 𝔹}
    (Hξ : Γ ≤ ξ ⊆ᴮ omegaOne) (HT : Γ ≤ is_function ξ entrySpace T)
    (Hentry : Γ ≤ pair i (entry A Z U) ∈ᴮ T)
    (HZ : Γ ≤ is_function omegaOne omegaOne Z) (Hv : Γ ≤ pair ν v ∈ᴮ Z) :
    Γ ≤ pair (pair i ν) v ∈ᴮ coordinateHistory T :=
  coordinateHistory_pair_iff.mpr
    ⟨mem_of_mem_subset Hξ (mem_domain_of_is_function Hentry HT),
      mem_domain_of_is_function Hv HZ, mem_codomain_of_is_function Hv HZ,
      le_iSup_of_le Z (le_inf (indexFamily_pair Hξ HT Hentry) Hv)⟩

private theorem coordinate_mono {T Q : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ T ⊆ᴮ Q) : Γ ≤ coordinateHistory T ⊆ᴮ coordinateHistory Q := by
  rw [subset_unfold']
  apply le_iInf
  intro p
  rw [← deduction]
  let Δ := Γ ⊓ p ∈ᴮ coordinateHistory T
  have Hp : Δ ≤ p ∈ᴮ coordinateHistory T := inf_le_right
  obtain ⟨q, Hq, v, Hv, Heq⟩ := mem_prod_iff₂.mp (mem_of_mem_subset coordinateHistory_subset Hp)
  obtain ⟨i, Hi, ν, Hν, Hqeq⟩ := mem_prod_iff₂.mp Hq
  have Heq' : Δ ≤ p =ᴮ pair (pair i ν) v := bv_trans Heq (pair_congr Hqeq bv_refl)
  obtain ⟨Z, HZ, HvZ⟩ := coordinate_family_witness (mem_congr Heq' bv_refl Hp)
  exact mem_congr (bv_symm Heq') bv_refl (coordinateHistory_pair_iff.mpr
    ⟨Hi, Hν, Hv, le_iSup_of_le Z (le_inf
      (mem_of_mem_subset (decode_mono (inf_le_left.trans Hsub)) HZ) HvZ)⟩)

theorem coordinateHistory_congr : B_congr (coordinateHistory : bSet 𝔹 → bSet 𝔹) := by
  intro T Q Γ H
  exact subset_ext (coordinate_mono (subset_of_eq H)) (coordinate_mono (subset_of_eq (bv_symm H)))

/-- The flattened graph has the actual rectangular prefix as its support,
not just weak totality on that prefix. -/
theorem coordinateHistory_is_function {ξ T : bSet 𝔹} {Γ : 𝔹}
    (Hξ : Γ ≤ ξ ⊆ᴮ omegaOne) (HT : Γ ≤ is_function ξ entrySpace T)
    (Hrows : Γ ≤ rowFunctions T) :
    Γ ≤ is_function (prod ξ omegaOne) omegaOne (coordinateHistory T) := by
  refine le_inf (le_inf ?_ ?_) ?_
  · apply le_iInf
    intro q
    apply le_iInf
    intro r
    apply le_iInf
    intro v
    apply le_iInf
    intro w
    rw [← deduction, ← deduction]
    let Δ := (Γ ⊓ (pair q v ∈ᴮ coordinateHistory T ⊓ pair r w ∈ᴮ coordinateHistory T)) ⊓ q =ᴮ r
    have HΔ : Δ ≤ Γ := inf_le_left.trans inf_le_left
    have Hv : Δ ≤ pair q v ∈ᴮ coordinateHistory T :=
      inf_le_left.trans (inf_le_right.trans inf_le_left)
    have Hw : Δ ≤ pair r w ∈ᴮ coordinateHistory T :=
      inf_le_left.trans (inf_le_right.trans inf_le_right)
    obtain ⟨i, _, ν, _, Hq⟩ := mem_prod_iff₂.mp (coordinate_pair_general.mp Hv).1
    obtain ⟨j, _, μ, _, Hr⟩ := mem_prod_iff₂.mp (coordinate_pair_general.mp Hw).1
    obtain ⟨A, Z, U, Hi, HvZ⟩ := coordinateHistory_witness
      (mem_congr (pair_congr Hq bv_refl) bv_refl Hv)
    obtain ⟨B, W, V, Hj, HwW⟩ := coordinateHistory_witness
      (mem_congr (pair_congr Hr bv_refl) bv_refl Hw)
    have Hcoords : Δ ≤ pair i ν =ᴮ pair j μ := bv_trans (bv_symm Hq) (bv_trans inf_le_right Hr)
    have HZW : Δ ≤ Z =ᴮ W := eq_of_eq_pair_left' (eq_of_eq_pair_right'
      (eq_of_is_function_of_eq (HΔ.trans HT) (eq_of_eq_pair_left' Hcoords) Hi Hj))
    exact eq_of_is_function_of_eq (rowFunctions_apply (HΔ.trans Hrows) Hi)
      (eq_of_eq_pair_right' Hcoords) HvZ (mem_congr bv_refl (bv_symm HZW) HwW)
  · apply le_iInf
    intro q
    rw [← deduction]
    let Δ := Γ ⊓ q ∈ᴮ prod ξ omegaOne
    have HΔ : Δ ≤ Γ := inf_le_left
    obtain ⟨i, Hi, ν, Hν, Hq⟩ := mem_prod_iff₂.mp (show Δ ≤ q ∈ᴮ prod ξ omegaOne from inf_le_right)
    have Hex : Δ ≤ ⨆ e, e ∈ᴮ entrySpace ⊓ pair i e ∈ᴮ T :=
      (le_inf (HΔ.trans ((is_total_of_is_function HT).trans (iInf_le _ i))) Hi).trans bv_imp_elim
    obtain ⟨e, He⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
    obtain ⟨A, Z, U, _, _, _, Heq⟩ := entrySpace_witness (He.trans inf_le_left)
    have Hentry : Δ ≤ pair i (entry A Z U) ∈ᴮ T :=
      mem_congr (pair_congr bv_refl Heq) bv_refl (He.trans inf_le_right)
    have HZ : Δ ≤ is_function omegaOne omegaOne Z := rowFunctions_apply (HΔ.trans Hrows) Hentry
    have Hexv : Δ ≤ ⨆ v, v ∈ᴮ omegaOne ⊓ pair ν v ∈ᴮ Z :=
      (le_inf ((is_total_of_is_function HZ).trans (iInf_le _ ν)) Hν).trans bv_imp_elim
    obtain ⟨v, Hv⟩ := exists_convert Hexv (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
    exact le_iSup_of_le v (le_inf (Hv.trans inf_le_left)
      (mem_congr (pair_congr (bv_symm Hq) bv_refl) bv_refl
        (coordinateHistory_pair (HΔ.trans Hξ) (HΔ.trans HT) Hentry HZ (Hv.trans inf_le_right))))
  · rw [subset_unfold']
    apply le_iInf
    intro p
    rw [← deduction]
    let Δ := Γ ⊓ p ∈ᴮ coordinateHistory T
    have Hp : Δ ≤ p ∈ᴮ coordinateHistory T := inf_le_right
    obtain ⟨q, Hq, v, Hv, Heq⟩ := mem_prod_iff₂.mp (mem_of_mem_subset coordinateHistory_subset Hp)
    obtain ⟨i, _, ν, Hν, Hqeq⟩ := mem_prod_iff₂.mp Hq
    have Heq' : Δ ≤ p =ᴮ pair (pair i ν) v := bv_trans Heq (pair_congr Hqeq bv_refl)
    obtain ⟨A, Z, U, Hentry, _⟩ := coordinateHistory_witness (mem_congr Heq' bv_refl Hp)
    exact mem_congr (bv_symm Heq') bv_refl
      (mem_prod (mem_prod (mem_domain_of_is_function Hentry (inf_le_left.trans HT)) Hν) Hv)

end bSet.ErdosFusionEntrySpace
