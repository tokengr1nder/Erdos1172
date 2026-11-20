/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanNameIteration
public import Erdos1172.Part4InternalCohenExtension

@[expose] public section

/-!
# Coordinate-decision density for the actual Cohen-name iteration

The internal extension theorem supplies a mixed partial graph and a mixed
binary value at the original first-stage condition. Canonical-label density
then gives a positive iteration strengthening representing that graph.
A further positive refinement chooses a canonical binary child, hence an
actual zero or one. No mixed name is treated as a fixed child without this
refinement, and no dense-set hypothesis is supplied to the final theorem.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch

universe u

namespace Erdos1172CohenIteration

open bSet ErdosCohen Erdos1172BooleanNameIteration

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- The internal extension and the canonical refinement both preserve the
local first-stage hypotheses; only the final canonical label may shrink it. -/
theorem exists_deciding_extension_local {K a : bSet B}
    (p : Condition (conditions K))
    (HK : p.value ≤ ErdosHartogs.hartogsProperty omega K)
    (Ha : p.value ≤ a ∈ᴮ K) :
    ∃ r : Condition (conditions K), r ≤ p ∧
      ∃ y : bSet B, r.value ≤ y ∈ᴮ two ∧ r.value ≤ pair a y ∈ᴮ name r := by
  have Hp : p.value ≤ ErdosCohen.condition K (name p) :=
    mem_conditions_iff.mp (name_mem p)
  have Hext : B_ext (fun q : bSet B => ErdosCohen.condition K q ⊓
      (name p ⊆ᴮ q ⊓ ⨆ y : bSet B, y ∈ᴮ two ⊓ pair a y ∈ᴮ q)) :=
    B_ext_inf (condition_ext_graph K)
      (B_ext_inf B_ext_subset_right
        (B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_mem_right)))
  obtain ⟨q, Hq⟩ := exists_convert (condition_extension_decides HK Hp Ha) Hext
  obtain ⟨y, Hy⟩ := exists_convert (Hq.trans (inf_le_right.trans inf_le_right))
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  obtain ⟨r, Hrp, Hrv, Hrq⟩ := exists_extension_refinement p p.nonzero le_rfl
    (mem_conditions_iff.mpr (Hq.trans inf_le_left))
    (Hq.trans (inf_le_right.trans inf_le_left))
  refine ⟨r, Hrp, y, Hrv.trans (Hy.trans inf_le_left), ?_⟩
  exact bv_rw'' Hrq (Hrv.trans (Hy.trans inf_le_right))
    (show B_ext (fun q : bSet B => pair a y ∈ᴮ q) from B_ext_mem_right)

theorem exists_deciding_extension {K a : bSet B}
    (HK : (⊤ : B) ≤ ErdosHartogs.hartogsProperty omega K)
    (Ha : (⊤ : B) ≤ a ∈ᴮ K) (p : Condition (conditions K)) :
    ∃ r : Condition (conditions K), r ≤ p ∧
      ∃ y : bSet B, r.value ≤ y ∈ᴮ two ∧ r.value ≤ pair a y ∈ᴮ name r :=
  exists_deciding_extension_local p (le_top.trans HK) (le_top.trans Ha)

/-- The binary label is chosen only after a further nonzero refinement. -/
theorem exists_deciding_label_extension {K a : bSet B}
    (HK : (⊤ : B) ≤ ErdosHartogs.hartogsProperty omega K)
    (Ha : (⊤ : B) ≤ a ∈ᴮ K) (p : Condition (conditions K)) :
    ∃ r : Condition (conditions K), r ≤ p ∧
      ∃ i : (two : bSet B).type,
        r.value ≤ pair a ((two : bSet B).func i) ∈ᴮ name r := by
  obtain ⟨r, Hrp, y, Hy, Hpair⟩ := exists_deciding_extension HK Ha p
  obtain ⟨t, Htr, Hty⟩ := exists_canonical_refinement r.nonzero Hy
  let s := shrink r t.value t.nonzero Htr
  refine ⟨s, (shrink_le r t.value t.nonzero Htr).trans Hrp, t.index, ?_⟩
  exact bv_rw'' Hty (Htr.trans Hpair)
    (show B_ext (fun y : bSet B => pair a y ∈ᴮ name r) from B_ext_pair_mem_right)

/-- These are the actual two canonical children, not an extraction from a
Boolean membership assertion at an unchanged condition. -/
theorem two_child_eq_zero_or_one (i : (two : bSet B).type) :
    (two : bSet B).func i = (0 : bSet B) ∨
      (two : bSet B).func i = (1 : bSet B) := by
  cases i with
  | none => exact Or.inr rfl
  | some j =>
    cases j with
    | none => exact Or.inl rfl
    | some h => exact PEmpty.elim h

def decidesCoordinate {K : bSet B} (a : bSet B)
    (p : Condition (conditions K)) : Prop :=
  (p.value ≤ pair a (0 : bSet B) ∈ᴮ name p) ∨
    (p.value ≤ pair a (1 : bSet B) ∈ᴮ name p)

theorem exists_binary_deciding_extension {K a : bSet B}
    (HK : (⊤ : B) ≤ ErdosHartogs.hartogsProperty omega K)
    (Ha : (⊤ : B) ≤ a ∈ᴮ K) (p : Condition (conditions K)) :
    ∃ r : Condition (conditions K), r ≤ p ∧ decidesCoordinate a r := by
  obtain ⟨r, Hrp, i, Hi⟩ := exists_deciding_label_extension HK Ha p
  refine ⟨r, Hrp, ?_⟩
  rcases two_child_eq_zero_or_one i with Hzero | Hone
  · exact Or.inl (Hzero ▸ Hi)
  · exact Or.inr (Hone ▸ Hi)

theorem coordinate_decision_dense {K a : bSet B}
    (HK : (⊤ : B) ≤ ErdosHartogs.hartogsProperty omega K)
    (Ha : (⊤ : B) ≤ a ∈ᴮ K) :
    ∀ p : Condition (conditions K),
      ∃ r ∈ {r : Condition (conditions K) | decidesCoordinate a r}, r ≤ p := by
  intro p
  obtain ⟨r, Hrp, Hr⟩ := exists_binary_deciding_extension HK Ha p
  exact ⟨r, Hr, Hrp⟩

/-- The constructed coordinate-decision dense set covers the full iteration
completion, with no generic filter or cardinal-preservation assertion. -/
theorem iSup_deciding_condition_eq_top {K a : bSet B}
    (HK : (⊤ : B) ≤ ErdosHartogs.hartogsProperty omega K)
    (Ha : (⊤ : B) ≤ a ∈ᴮ K) :
    (⨆ p : {p : Condition (conditions K) // decidesCoordinate a p},
      Erdos1172PosetCompletion.condition p.val) = ⊤ :=
  Erdos1172PosetCompletion.iSup_condition_eq_top_of_dense
    {p : Condition (conditions K) | decidesCoordinate a p}
    (coordinate_decision_dense HK Ha)

end Erdos1172CohenIteration
