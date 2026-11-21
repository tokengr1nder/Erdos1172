/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4CohenIteration
public import Erdos1172.Part4CohenIterationDensity

@[expose] public section

/-!
# Actual Boolean bit values of the internal Cohen iteration

Each bit value is the supremum of the cones of actual iteration conditions
which decide the corresponding assignment. Opposite assignments have no
common strengthening, by the local functionality of the strengthening's
graph. The proved coordinate-decision density gives total binary coverage.
Neither a generic filter nor a supplied density assumption is used.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172CohenIteration

open bSet Erdos1172PosetCompletion

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- The second-stage Boolean value of an assignment, defined from the actual
canonical-label conditions rather than an assumed generic subset. -/
def bitValue (K a y : bSet B) : Algebra K :=
  ⨆ p : {p : Conditions K //
      p.value ≤ pair a y ∈ᴮ Erdos1172BooleanNameIteration.name p},
    condition p.val

theorem condition_le_bitValue {K a y : bSet B} {p : Conditions K}
    (Hp : p.value ≤ pair a y ∈ᴮ Erdos1172BooleanNameIteration.name p) :
    condition p ≤ bitValue K a y :=
  le_iSup (fun q : {q : Conditions K //
      q.value ≤ pair a y ∈ᴮ Erdos1172BooleanNameIteration.name q} =>
    condition q.val) ⟨p, Hp⟩

/-- A genuine common strengthening transports both assignments into its
actual functional graph, contradicting its nonzero first-stage value. -/
theorem condition_inf_eq_bot_of_distinct_decisions
    {K a y z : bSet B} {p q : Conditions K}
    (Hp : p.value ≤ pair a y ∈ᴮ Erdos1172BooleanNameIteration.name p)
    (Hq : q.value ≤ pair a z ∈ᴮ Erdos1172BooleanNameIteration.name q)
    (Hneq : (⊤ : B) ≤ (y =ᴮ z)ᶜ) :
    condition p ⊓ condition q = ⊥ := by
  classical
  by_contra Hnonzero
  obtain ⟨r, Hrp, Hrq⟩ := (condition_inf_ne_bot_iff p q).mp Hnonzero
  have Hry : r.value ≤ pair a y ∈ᴮ Erdos1172BooleanNameIteration.name r :=
    mem_of_mem_subset Hrp.2 (Hrp.1.trans Hp)
  have Hrz : r.value ≤ pair a z ∈ᴮ Erdos1172BooleanNameIteration.name r :=
    mem_of_mem_subset Hrq.2 (Hrq.1.trans Hq)
  have Hrcondition : r.value ≤
      ErdosCohen.condition K (Erdos1172BooleanNameIteration.name r) :=
    ErdosCohen.mem_conditions_iff.mp (Erdos1172BooleanNameIteration.name_mem r)
  have Hrfunc : r.value ≤ is_func (Erdos1172BooleanNameIteration.name r) :=
    Hrcondition.trans (inf_le_right.trans inf_le_left)
  have Hyz : r.value ≤ y =ᴮ z := eq_of_is_func_of_eq Hrfunc bv_refl Hry Hrz
  exact r.nonzero (bot_unique (bv_absurd _ Hyz (le_top.trans Hneq)))

theorem bitValue_inf_eq_bot {K a y z : bSet B}
    (Hneq : (⊤ : B) ≤ (y =ᴮ z)ᶜ) :
    bitValue K a y ⊓ bitValue K a z = ⊥ := by
  unfold bitValue
  erw [iSup_inf_eq]
  apply le_antisymm ?_ bot_le
  apply iSup_le
  intro p
  erw [inf_iSup_eq]
  apply iSup_le
  intro q
  exact (condition_inf_eq_bot_of_distinct_decisions p.property q.property Hneq).le

theorem bitValue_zero_inf_one_eq_bot (K a : bSet B) : bitValue K a 0 ⊓ bitValue K a 1 = ⊥ := by
  apply bitValue_inf_eq_bot
  rw [← imp_bot, ← deduction]
  exact bot_of_zero_eq_one inf_le_right

end Erdos1172CohenIteration
