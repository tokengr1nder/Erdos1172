/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4CohenCountableFusion
public import Erdos1172.Part4CohenReadingBridge

@[expose] public section

/-!
# Actual relative binary readings below strengthened Cohen conditions

Countable fusion is carried out at the original first-stage value. Only
afterwards is its mixed extension refined to one canonical condition.
The readings of this final condition give a single sequence of first-stage
Boolean coefficients with the stated agreement below its completed cone.

The concluding supremum expresses a dense local cover by such sequences.
It does not select one coefficient sequence globally or assert preservation
of arbitrary cardinals, full GCH, or an anonymous quotient theorem.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172CohenIteration

open bSet Erdos1172PosetCompletion

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- A local decision gives actual agreement with its first-stage reading
coefficient below the completed condition. The opposite reading is disjoint
from that coefficient, so no Boolean branch is chosen externally. -/
theorem condition_le_binary_reading_of_decision {K : bSet B}
    (p : Conditions K) (c : Algebra K)
    (Hdecision : p.value ≤ reads c (Erdos1172BooleanNameIteration.name p) ⊔
      reads cᶜ (Erdos1172BooleanNameIteration.name p)) :
    condition p ≤
      (c ⊓ firstStageHom K (reads c (Erdos1172BooleanNameIteration.name p))) ⊔
      (cᶜ ⊓ (firstStageHom K (reads c (Erdos1172BooleanNameIteration.name p)))ᶜ) := by
  have Hother : reads cᶜ (Erdos1172BooleanNameIteration.name p) ≤
      (reads c (Erdos1172BooleanNameIteration.name p))ᶜ :=
    le_compl_iff_disjoint_right.mpr
      (disjoint_iff_inf_le.mpr
        (reads_inf_compl_eq_bot c (Erdos1172BooleanNameIteration.name p)).le).symm
  have Hother' : firstStageHom K (reads cᶜ (Erdos1172BooleanNameIteration.name p)) ≤
      (firstStageHom K (reads c (Erdos1172BooleanNameIteration.name p)))ᶜ := by
    simpa only [firstStageHom_compl] using OrderHomClass.mono (firstStageHom K) Hother
  have Hcover : condition p ≤
      firstStageHom K (reads c (Erdos1172BooleanNameIteration.name p)) ⊔
        firstStageHom K (reads cᶜ (Erdos1172BooleanNameIteration.name p)) := by
    rw [← map_sup]
    exact (condition_le_firstStageHom_iff K p _).mpr Hdecision
  calc
    condition p ≤ condition p ⊓
        (firstStageHom K (reads c (Erdos1172BooleanNameIteration.name p)) ⊔
          firstStageHom K (reads cᶜ (Erdos1172BooleanNameIteration.name p))) :=
      le_inf le_rfl Hcover
    _ = (condition p ⊓ firstStageHom K
          (reads c (Erdos1172BooleanNameIteration.name p))) ⊔
        (condition p ⊓ firstStageHom K
          (reads cᶜ (Erdos1172BooleanNameIteration.name p))) := inf_sup_left _ _ _
    _ ≤ (c ⊓ firstStageHom K (reads c (Erdos1172BooleanNameIteration.name p))) ⊔
        (cᶜ ⊓ (firstStageHom K (reads c (Erdos1172BooleanNameIteration.name p)))ᶜ) :=
      sup_le_sup
        (le_inf (condition_inf_firstStageHom_reads_le p c) inf_le_right)
        (le_inf (condition_inf_firstStageHom_reads_le p cᶜ) (inf_le_right.trans Hother'))

/-- Every actual condition has an actual strengthening on whose cone a
countable binary sequence is read by one first-stage coefficient sequence. -/
theorem exists_relative_binary_reading {K : bSet B}
    (p : Conditions K)
    (HK : (⊤ : B) ≤ ErdosHartogs.hartogsProperty omega K)
    (c : ℕ → Algebra K) :
    ∃ t : Conditions K, t ≤ p ∧ ∃ b : ℕ → B, ∀ n : ℕ,
      condition t ≤ (c n ⊓ firstStageHom K (b n)) ⊔ ((c n)ᶜ ⊓ (firstStageHom K (b n))ᶜ) := by
  obtain ⟨r, Hr, Hsub, Hread⟩ := exists_countable_deciding_extension
    (le_top.trans HK)
    (ErdosCohen.mem_conditions_iff.mp (Erdos1172BooleanNameIteration.name_mem p)) c
  obtain ⟨t, Htp, Htv, Hreq⟩ :=
    Erdos1172BooleanNameIteration.exists_extension_refinement p p.nonzero le_rfl
      (ErdosCohen.mem_conditions_iff.mpr Hr) Hsub
  refine ⟨t, Htp, (fun n => reads (c n) (Erdos1172BooleanNameIteration.name t)), ?_⟩
  intro n
  apply condition_le_binary_reading_of_decision
  exact bv_rw'' Hreq (Htv.trans (Hread n))
    (B_ext_sup (h₁ := reads_ext (c n)) (h₂ := reads_ext (c n)ᶜ))

/-- The actual relative readings densely cover the whole completed
iteration. The first-stage sequence may vary between Boolean pieces. -/
theorem iSup_iInf_relative_binary_reading_eq_top {K : bSet B}
    (HK : (⊤ : B) ≤ ErdosHartogs.hartogsProperty omega K)
    (c : ℕ → Algebra K) :
    (⨆ b : ℕ → B, ⨅ n : ℕ,
      (c n ⊓ firstStageHom K (b n)) ⊔ ((c n)ᶜ ⊓ (firstStageHom K (b n))ᶜ)) = ⊤ := by
  let D : Set (Conditions K) := {t | ∃ b : ℕ → B, ∀ n : ℕ,
    condition t ≤ (c n ⊓ firstStageHom K (b n)) ⊔ ((c n)ᶜ ⊓ (firstStageHom K (b n))ᶜ)}
  have Hdense : ∀ p : Conditions K, ∃ t ∈ D, t ≤ p := by
    intro p
    obtain ⟨t, Htp, b, Hb⟩ := exists_relative_binary_reading p HK c
    exact ⟨t, ⟨b, Hb⟩, Htp⟩
  apply eq_top_iff.mpr
  rw [← iSup_condition_eq_top_of_dense D Hdense]
  apply iSup_le
  intro t
  obtain ⟨b, Hb⟩ := t.property
  exact le_iSup_of_le b (le_iInf Hb)

end Erdos1172CohenIteration
