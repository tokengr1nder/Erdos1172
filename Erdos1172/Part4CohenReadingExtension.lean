/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4CohenIterationReading

@[expose] public section

/-!
# Local readings persist under actual graph strengthening

An extension which remains an internal Cohen condition retains every
reading of the old graph on the original Boolean context. Canonical
representatives of the new graph need only exist on positive refinements;
the proof uses their cover and never chooses a single representative at
the unchanged context. In particular, a countable union which has been
proved to be a condition can retain all earlier decisions.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172CohenIteration

open bSet Erdos1172PosetCompletion

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- Readings are locally monotone under graph strengthening, provided the
new graph is an actual internal condition. -/
theorem reads_mono_of_subset {K q r : bSet B} {Γ : B} {c : Algebra K}
    (Hsub : Γ ≤ q ⊆ᴮ r) (Hr : Γ ≤ r ∈ᴮ ErdosCohen.conditions K) :
    Γ ⊓ reads c q ≤ reads c r := by
  classical
  change Γ ⊓ (⨆ p : {p : Conditions K // condition p ≤ c},
    p.val.value ⊓ (q =ᴮ Erdos1172BooleanNameIteration.name p.val)) ≤ reads c r
  rw [inf_iSup_eq]
  apply iSup_le
  intro p
  let Δ : B := Γ ⊓
    (p.val.value ⊓ (q =ᴮ Erdos1172BooleanNameIteration.name p.val))
  change Δ ≤ reads c r
  by_contra Hnot
  have Hpositive : Δ ⊓ (reads c r)ᶜ ≠ ⊥ := by
    intro Hzero
    apply Hnot
    have H : Δ ≤ ((reads c r)ᶜ)ᶜ :=
      le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr Hzero.le)
    simpa only [compl_compl] using H
  have Hcontext : Δ ⊓ (reads c r)ᶜ ≤ Γ :=
    inf_le_left.trans inf_le_left
  have Hvalue : Δ ⊓ (reads c r)ᶜ ≤ p.val.value :=
    inf_le_left.trans (inf_le_right.trans inf_le_left)
  have Heq : Δ ⊓ (reads c r)ᶜ ≤
      q =ᴮ Erdos1172BooleanNameIteration.name p.val :=
    inf_le_left.trans (inf_le_right.trans inf_le_right)
  have Hextension : Δ ⊓ (reads c r)ᶜ ≤
      Erdos1172BooleanNameIteration.name p.val ⊆ᴮ r :=
    subset_trans' (subset_of_eq (bv_symm Heq)) (Hcontext.trans Hsub)
  obtain ⟨t, Htp, Htb, Hteq⟩ :=
    Erdos1172BooleanNameIteration.exists_extension_refinement p.val Hpositive
      Hvalue (Hcontext.trans Hr) Hextension
  have Hcone : condition t ≤ c := (condition_mono Htp).trans p.property
  have Hread : t.value ≤ reads c r :=
    le_iSup_of_le ⟨t, Hcone⟩ (le_inf le_rfl Hteq)
  have Hnotread : t.value ≤ (reads c r)ᶜ := Htb.trans inf_le_right
  exact t.nonzero (bot_unique ((le_inf Hread Hnotread).trans inf_compl_eq_bot.le))

/-- A mixed binary decision also persists, without selecting which branch
holds at the whole context. -/
theorem reads_decision_of_extension {K q r : bSet B} {Γ : B} {c : Algebra K}
    (Hsub : Γ ≤ q ⊆ᴮ r) (Hr : Γ ≤ r ∈ᴮ ErdosCohen.conditions K)
    (Hdecision : Γ ≤ reads c q ⊔ reads cᶜ q) :
    Γ ≤ reads c r ⊔ reads cᶜ r := by
  calc
    Γ ≤ Γ ⊓ (reads c q ⊔ reads cᶜ q) := le_inf le_rfl Hdecision
    _ = (Γ ⊓ reads c q) ⊔ (Γ ⊓ reads cᶜ q) := inf_sup_left _ _ _
    _ ≤ reads c r ⊔ reads cᶜ r :=
      sup_le ((reads_mono_of_subset Hsub Hr).trans le_sup_left)
        ((reads_mono_of_subset Hsub Hr).trans le_sup_right)

end Erdos1172CohenIteration
