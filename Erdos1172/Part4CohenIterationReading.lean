/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4CohenIteration

@[expose] public section

/-!
# Fixed-base local decisions in the actual Cohen iteration

A reading value records canonical conditions whose entire completed cone
lies below a prescribed Boolean value. Disjoint completed values have
disjoint readings of the same internal name. Every locally valid condition
has an actual mixed extension which decides a value or its complement at
the unchanged first-stage Boolean context.

The proof derives decision density from the actual regular completion and
then applies Boolean fullness to its cover. It does not choose one external
decision branch at that context, assert closure of the external iteration
preorder, or assert preservation of omega-one.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172CohenIteration

open bSet Erdos1172PosetCompletion

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- The first-stage Boolean cover of canonical representatives whose
completed cones lie below `c`. -/
def reads {K : bSet B} (c : Algebra K) (q : bSet B) : B :=
  ⨆ p : {p : Conditions K // condition p ≤ c},
    p.val.value ⊓ (q =ᴮ Erdos1172BooleanNameIteration.name p.val)

theorem reads_ext {K : bSet B} (c : Algebra K) : B_ext (reads c) := by
  unfold reads
  exact B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_bv_eq_left)

theorem reads_mono {K q : bSet B} {c d : Algebra K} (Hcd : c ≤ d) :
    reads c q ≤ reads d q := by
  apply iSup_le
  intro p
  exact le_iSup_of_le ⟨p.val, p.property.trans Hcd⟩ le_rfl

theorem value_le_reads {K : bSet B} {c : Algebra K} {p : Conditions K}
    (Hp : condition p ≤ c) :
    p.value ≤ reads c (Erdos1172BooleanNameIteration.name p) :=
  le_iSup_of_le ⟨p, Hp⟩ (le_inf le_rfl bv_refl)

theorem reads_le_mem_conditions {K q : bSet B} {c : Algebra K} :
    reads c q ≤ q ∈ᴮ ErdosCohen.conditions K := by
  apply iSup_le
  intro p
  exact bv_rw' (ϕ := fun r => r ∈ᴮ ErdosCohen.conditions K) inf_le_right
    (h_congr := B_ext_mem_left)
    (H_new := inf_le_left.trans (Erdos1172BooleanNameIteration.name_mem p.val))

/-- Two disjoint completed cones cannot read the same name on overlapping
positive first-stage pieces: shrinking one representative gives an actual
common strengthening of both. -/
theorem reads_inf_eq_bot {K q : bSet B} {c d : Algebra K}
    (Hcd : c ⊓ d = ⊥) : reads c q ⊓ reads d q = ⊥ := by
  unfold reads
  rw [iSup_inf_eq]
  apply le_antisymm ?_ bot_le
  apply iSup_le
  intro p
  rw [inf_iSup_eq]
  apply iSup_le
  intro r
  let b : B := (p.val.value ⊓ (q =ᴮ Erdos1172BooleanNameIteration.name p.val)) ⊓
    (r.val.value ⊓ (q =ᴮ Erdos1172BooleanNameIteration.name r.val))
  change b ≤ ⊥
  by_cases Hb : b = ⊥
  · exact Hb.le
  · let s : Conditions K := Erdos1172BooleanNameIteration.shrink p.val b Hb
      (inf_le_left.trans inf_le_left)
    have Hsp : s ≤ p.val :=
      Erdos1172BooleanNameIteration.shrink_le p.val b Hb
        (inf_le_left.trans inf_le_left)
    have Hsr : s ≤ r.val := by
      refine ⟨inf_le_right.trans inf_le_left, ?_⟩
      change b ≤ Erdos1172BooleanNameIteration.name r.val ⊆ᴮ
        Erdos1172BooleanNameIteration.name p.val
      exact subset_of_eq (bv_trans (bv_symm (inf_le_right.trans inf_le_right))
        (inf_le_left.trans inf_le_right))
    have Hs : condition s ≤ c ⊓ d :=
      le_inf ((condition_mono Hsp).trans p.property)
        ((condition_mono Hsr).trans r.property)
    exact False.elim (condition_ne_bot s (bot_unique (Hs.trans Hcd.le)))

theorem reads_inf_compl_eq_bot {K : bSet B} (c : Algebra K) (q : bSet B) :
    reads c q ⊓ reads cᶜ q = ⊥ :=
  reads_inf_eq_bot inf_compl_eq_bot

/-- Ordinary decision density is derived from the regular completion,
not included as a hypothesis on the iteration. -/
private theorem exists_deciding_condition {K : bSet B}
    (p : Conditions K) (c : Algebra K) :
    ∃ r : Conditions K, r ≤ p ∧ (condition r ≤ c ∨ condition r ≤ cᶜ) := by
  classical
  by_cases Hzero : condition p ⊓ c = ⊥
  · exact ⟨p, le_rfl, Or.inr
      (le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr Hzero.le))⟩
  · obtain ⟨q, Hq⟩ := exists_condition_le Hzero
    have Hqp : q ∈ ((condition p).val : LowerSet (Conditions K)) :=
      condition_le_iff.mp (Hq.trans inf_le_left)
    obtain ⟨r, Hrq, Hrp⟩ := (mem_condition_iff p q).mp Hqp q le_rfl
    exact ⟨r, Hrp, Or.inl ((condition_mono Hrq).trans (Hq.trans inf_le_right))⟩

/-- Every positive residual of the context contains a canonical deciding
extension, so their Boolean existential covers the entire original context. -/
theorem deciding_name_extension_cover {K q : bSet B} {Γ : B}
    (Hq : Γ ≤ q ∈ᴮ ErdosCohen.conditions K) (c : Algebra K) :
    Γ ≤ ⨆ r : bSet B, r ∈ᴮ ErdosCohen.conditions K ⊓
      (q ⊆ᴮ r ⊓ (reads c r ⊔ reads cᶜ r)) := by
  classical
  let V : B := ⨆ r : bSet B, r ∈ᴮ ErdosCohen.conditions K ⊓
    (q ⊆ᴮ r ⊓ (reads c r ⊔ reads cᶜ r))
  change Γ ≤ V
  by_contra Hnot
  have Hpositive : Γ ⊓ Vᶜ ≠ ⊥ := by
    intro Hzero
    apply Hnot
    have H : Γ ≤ (Vᶜ)ᶜ :=
      le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr Hzero.le)
    simpa only [compl_compl] using H
  obtain ⟨p, Hpb, Hpeq⟩ :=
    Erdos1172BooleanNameIteration.exists_canonical_refinement Hpositive
      (inf_le_left.trans Hq)
  obtain ⟨r, Hrp, Hdecision⟩ := exists_deciding_condition p c
  have Hsub : r.value ≤ q ⊆ᴮ Erdos1172BooleanNameIteration.name r :=
    subset_trans' (subset_of_eq (Hrp.1.trans Hpeq)) Hrp.2
  have Hread : r.value ≤
      reads c (Erdos1172BooleanNameIteration.name r) ⊔
        reads cᶜ (Erdos1172BooleanNameIteration.name r) := by
    rcases Hdecision with Hleft | Hright
    · exact (value_le_reads Hleft).trans le_sup_left
    · exact (value_le_reads Hright).trans le_sup_right
  have HrV : r.value ≤ V :=
    le_iSup_of_le (Erdos1172BooleanNameIteration.name r)
      (le_inf (Erdos1172BooleanNameIteration.name_mem r) (le_inf Hsub Hread))
  have HrnotV : r.value ≤ Vᶜ := Hrp.1.trans (Hpb.trans inf_le_right)
  exact r.nonzero (bot_unique ((le_inf HrV HrnotV).trans inf_compl_eq_bot.le))

/-- Fullness produces one actual mixed extension at the unchanged context.
The result is a Boolean disjunction of readings, not an external branch. -/
theorem exists_deciding_name_extension {K q : bSet B} {Γ : B}
    (Hq : Γ ≤ q ∈ᴮ ErdosCohen.conditions K) (c : Algebra K) :
    ∃ r : bSet B, Γ ≤ r ∈ᴮ ErdosCohen.conditions K ∧
      Γ ≤ q ⊆ᴮ r ∧ Γ ≤ reads c r ⊔ reads cᶜ r := by
  obtain ⟨r, Hr⟩ := exists_convert (deciding_name_extension_cover Hq c)
    (B_ext_inf B_ext_mem_left (B_ext_inf B_ext_subset_right
      (B_ext_sup (h₁ := reads_ext c) (h₂ := reads_ext cᶜ))))
  exact ⟨r, Hr.trans inf_le_left, Hr.trans (inf_le_right.trans inf_le_left),
    Hr.trans (inf_le_right.trans inf_le_right)⟩

theorem exists_deciding_condition_extension {K q : bSet B} {Γ : B}
    (Hq : Γ ≤ ErdosCohen.condition K q) (c : Algebra K) :
    ∃ r : bSet B, Γ ≤ ErdosCohen.condition K r ∧
      Γ ≤ q ⊆ᴮ r ∧ Γ ≤ reads c r ⊔ reads cᶜ r := by
  obtain ⟨r, Hr, Hsub, Hread⟩ :=
    exists_deciding_name_extension (ErdosCohen.mem_conditions_iff.mpr Hq) c
  exact ⟨r, ErdosCohen.mem_conditions_iff.mp Hr, Hsub, Hread⟩

end Erdos1172CohenIteration
