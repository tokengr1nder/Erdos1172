/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalClubIntersectionStep
public import Erdos1172.Part4InternalOmegaTwoSequenceSup

@[expose] public section

/-!
# Small indexed intersections of internal omega-two clubs

Bounded internal choice gives simultaneous interval witnesses for every
value of the arbitrary internally small indexed family. An actual sequence
of names is constructed by recursion, and its internal graph supremum is
in every guarded club value. The Boolean cofinality law includes mixed
internal members; no ground enumeration of the club family is assumed.
Strict growth also covers empty indexing families. No stationarity or
pressing-down conclusion is asserted here.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosClubs

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIndexedIntersection ErdosOmegaTwoSequenceSup

/-- An actual common point above the supplied bound, at the original
Boolean condition. In particular the family need not be nonempty. -/
theorem exists_common_above {Q F a : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HF : Γ ≤ is_func' Q (bv_powerset omegaTwo) F)
    (HQ : Γ ≤ injects_into Q omegaOne)
    (Hclubs : Γ ≤ ⨅ q, ⨅ C, _root_.imp (q ∈ᴮ Q ⊓ pair q C ∈ᴮ F) (club omegaTwo C))
    (Ha : Γ ≤ a ∈ᴮ omegaTwo) :
    ∃ b : bSet 𝔹, Γ ≤ (b ∈ᴮ indexedIntersection omegaTwo F Q ⊓ b ∈ᴮ omegaTwo) ⊓ a ∈ᴮ b := by
  classical
  have Hvalues : Γ ≤ ⨅ q, ⨅ C, _root_.imp (q ∈ᴮ Q ⊓ pair q C ∈ᴮ F) (unboundedIn omegaTwo C) := by
    apply le_iInf
    intro q
    apply le_iInf
    intro C
    rw [← deduction]
    exact club_unbounded ((le_inf
      (inf_le_left.trans (Hclubs.trans ((iInf_le _ q).trans (iInf_le _ C))))
      inf_le_right).trans bv_imp_elim)
  have step (x : {x : bSet 𝔹 // Γ ≤ x ∈ᴮ omegaTwo}) :
      ∃ y : {y : bSet 𝔹 // Γ ≤ y ∈ᴮ omegaTwo},
        Γ ≤ x.val ∈ᴮ y.val ⊓ intervalHits Q F x.val y.val := by
    obtain ⟨y, Hy⟩ := exists_simultaneous_bound HCH HF HQ Hvalues x.property
    exact ⟨⟨y, Hy.trans inf_le_left⟩, Hy.trans inf_le_right⟩
  let next (x : {x : bSet 𝔹 // Γ ≤ x ∈ᴮ omegaTwo}) := Classical.choose (step x)
  have Hnext (x : {x : bSet 𝔹 // Γ ≤ x ∈ᴮ omegaTwo}) :
      Γ ≤ x.val ∈ᴮ (next x).val ⊓ intervalHits Q F x.val (next x).val :=
    Classical.choose_spec (step x)
  let seq : ℕ → {x : bSet 𝔹 // Γ ≤ x ∈ᴮ omegaTwo} := fun n => Nat.rec ⟨a, Ha⟩ (fun _ x => next x) n
  let v (n : ℕ) : bSet 𝔹 := (seq n).val
  have Hv (n : ℕ) : Γ ≤ v n ∈ᴮ omegaTwo := (seq n).property
  have Hstep (n : ℕ) : Γ ≤ v n ∈ᴮ v (n + 1) ⊓ intervalHits Q F (v n) (v (n + 1)) := by
    change Γ ≤ (seq n).val ∈ᴮ (next (seq n)).val ⊓ intervalHits Q F (seq n).val (next (seq n)).val
    exact Hnext (seq n)
  have Hinc (n : ℕ) : Γ ≤ v n ∈ᴮ v (n + 1) := (Hstep n).trans inf_le_left
  have Hsup : Γ ≤ sequenceSup v ∈ᴮ omegaTwo := sequenceSup_mem_omegaTwo HCH Hv
  have Hne : Γ ≤ (sequenceSup v =ᴮ (∅ : bSet 𝔹))ᶜ := sequenceSup_nonempty Hv Hinc
  have Hcommon : Γ ≤ sequenceSup v ∈ᴮ indexedIntersection omegaTwo F Q := by
    apply mem_indexedIntersection_iff.mpr
    refine ⟨Hsup, ?_⟩
    apply le_iInf
    intro q
    apply le_iInf
    intro C
    rw [← deduction]
    let Δ := Γ ⊓ (q ∈ᴮ Q ⊓ pair q C ∈ᴮ F)
    have HC : Δ ≤ club omegaTwo C :=
      (le_inf (inf_le_left.trans
        (Hclubs.trans ((iInf_le _ q).trans (iInf_le _ C)))) inf_le_right).trans bv_imp_elim
    have Hinterval (n : ℕ) : Δ ≤ ⨆ z,
        z ∈ᴮ C ⊓ (v n ∈ᴮ z ⊓ z ∈ᴮ v (n + 1)) :=
      (le_inf (inf_le_left.trans ((Hstep n).trans
        (inf_le_right.trans ((iInf_le _ q).trans (iInf_le _ C)))))
        inf_le_right).trans bv_imp_elim
    have HU : Δ ≤ unboundedIn (sequenceSup v) C :=
      interval_points_cofinal (fun n => inf_le_left.trans (Hv n)) Hinterval
    exact closedIn_apply (club_closed HC) (inf_le_left.trans Hsup) (inf_le_left.trans Hne) HU
  have Habove : Γ ≤ a ∈ᴮ sequenceSup v := by
    change Γ ≤ v 0 ∈ᴮ sequenceSup v
    exact sequence_value_mem_sup Hv Hinc 0
  exact ⟨sequenceSup v, le_inf (le_inf Hcommon Hsup) Habove⟩

/-- The constructed common bounds prove strict unboundedness of the
actual bounded intersection, for arbitrary internal indexing names. -/
theorem unboundedIn_indexedIntersection {Q F : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HF : Γ ≤ is_func' Q (bv_powerset omegaTwo) F)
    (HQ : Γ ≤ injects_into Q omegaOne)
    (Hclubs : Γ ≤ ⨅ q, ⨅ C, _root_.imp (q ∈ᴮ Q ⊓ pair q C ∈ᴮ F) (club omegaTwo C)) :
    Γ ≤ unboundedIn omegaTwo (indexedIntersection omegaTwo F Q) := by
  apply le_iInf
  intro a
  rw [← deduction]
  obtain ⟨b, Hb⟩ := exists_common_above (inf_le_left.trans HCH)
    (inf_le_left.trans HF) (inf_le_left.trans HQ) (inf_le_left.trans Hclubs)
    (show Γ ⊓ a ∈ᴮ omegaTwo ≤ a ∈ᴮ omegaTwo from inf_le_right)
  exact le_iSup_of_le b Hb

/-- Under internal CH, the intersection of an internally omega-one-small
indexed family of omega-two clubs is an omega-two club. -/
theorem club_indexedIntersection {Q F : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HF : Γ ≤ is_func' Q (bv_powerset omegaTwo) F)
    (HQ : Γ ≤ injects_into Q omegaOne)
    (Hclubs : Γ ≤ ⨅ q, ⨅ C, _root_.imp (q ∈ᴮ Q ⊓ pair q C ∈ᴮ F) (club omegaTwo C)) :
    Γ ≤ club omegaTwo (indexedIntersection omegaTwo F Q) := by
  refine le_inf indexedIntersection_subset
    (le_inf (unboundedIn_indexedIntersection HCH HF HQ Hclubs) ?_)
  apply closedIn_indexedIntersection
  apply le_iInf
  intro q
  apply le_iInf
  intro C
  rw [← deduction]
  exact club_closed ((le_inf
    (inf_le_left.trans (Hclubs.trans ((iInf_le _ q).trans (iInf_le _ C))))
    inf_le_right).trans bv_imp_elim)

end bSet.ErdosClubs
