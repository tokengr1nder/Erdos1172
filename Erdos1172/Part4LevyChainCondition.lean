/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyCompatibility
public import Erdos1172.Part4PosetBooleanCompletion
public import Mathlib.SetTheory.Cardinal.Pigeonhole

@[expose] public section

/-!
# The chain condition of the actual finite-support collapse

For a regular uncountable cardinal, a finite-support product of factors
smaller than that cardinal has no antichain of that cardinality. The proof
here uses the concrete collapse compatibility operations: induction on a
uniform finite support bound, with an exact coordinate-value fiber followed
by erasure, or a condition with disjoint support.

The resulting bound is also proved for arbitrary indexed disjoint positive
families in the regular Boolean completion. This is a chain-condition
theorem, not a cardinal-preservation or generic-extension theorem.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace Erdos1172LevyCollapse

open Erdos1172PosetCompletion
open scoped Cardinal Erdos1172LevyCollapse

variable {I : Type u} {A : I → Type u} {κ : Cardinal.{u}}

/-- The actual number of nonempty coordinates of a condition. -/
def supportSize (p : ProductCondition A) : ℕ := by
  classical
  exact p.support.card

/-- A uniformly bounded-support family of at least κ conditions contains
two compatible entries at distinct indices. No injectivity of the family
is required, so passing to coordinate-value fibers loses no information. -/
theorem compatible_pair_of_bounded_support
    (hκ : κ.IsRegular)
    (hfactor : ∀ i, Cardinal.mk (Erdos1172Collapse.Condition (A i)) < κ)
    (n : ℕ) :
    ∀ {J : Type u} (f : J → ProductCondition A),
      κ ≤ Cardinal.mk J →
      (∀ j, supportSize (f j) ≤ n) →
      ∃ j k, j ≠ k ∧ Compatible (f j) (f k) := by
  classical
  induction n with
  | zero =>
      intro J f hJ hs
      let : Nontrivial J := Cardinal.one_lt_iff_nontrivial.mp
        ((Cardinal.one_lt_aleph0.trans_le hκ.aleph0_le).trans_le hJ)
      obtain ⟨j, k, hjk⟩ := exists_pair_ne J
      have htop : ∀ t, f t = ⊤ := by
        intro t
        change f t = (0 : ProductCondition A)
        apply DFinsupp.support_eq_empty.mp
        apply Finset.card_eq_zero.mp
        exact Nat.eq_zero_of_le_zero (hs t)
      refine ⟨j, k, hjk, ?_⟩
      rw [htop j, htop k]
      exact compatible_refl ⊤
  | succ n ih =>
      intro J f hJ hs
      by_cases hlarge : ∃ i : I,
          κ ≤ Cardinal.mk {j : J // i ∈ (f j).support}
      · obtain ⟨i, hi⟩ := hlarge
        let D := {j : J // i ∈ (f j).support}
        let value : D → Erdos1172Collapse.Condition (A i) := fun j => f j.val i
        have hsmallValue : Cardinal.mk (Erdos1172Collapse.Condition (A i)) <
            κ.ord.cof := by
          rw [hκ.cof_ord]
          exact hfactor i
        obtain ⟨q, hq⟩ := Cardinal.infinite_pigeonhole_card value κ hi
          hκ.aleph0_le hsmallValue
        let T := value ⁻¹' {q}
        let erased : T → ProductCondition A := fun j => (f j.val.val).erase i
        have herased : ∀ j, supportSize (erased j) ≤ n := by
          intro j
          change ((f j.val.val).erase i).support.card ≤ n
          rw [DFinsupp.support_erase]
          have hmem : i ∈ (f j.val.val).support := j.val.property
          have hcard := Finset.card_erase_add_one hmem
          have hbound : (f j.val.val).support.card ≤ n + 1 := hs j.val.val
          omega
        obtain ⟨j, k, hjk, hcomp⟩ := ih erased hq herased
        have hne : j.val.val ≠ k.val.val := by
          intro h
          apply hjk
          apply Subtype.ext
          exact Subtype.ext h
        have hval : f j.val.val i = f k.val.val i := by
          have hj : value j.val = q := j.property
          have hk : value k.val = q := k.property
          exact hj.trans hk.symm
        exact ⟨j.val.val, k.val.val, hne,
          compatible_of_erase_eq i hval hcomp⟩
      · have hsmall : ∀ i : I,
            Cardinal.mk {j : J // i ∈ (f j).support} < κ := by
          intro i
          exact lt_of_not_ge (fun hi => hlarge ⟨i, hi⟩)
        let : Nontrivial J := Cardinal.one_lt_iff_nontrivial.mp
          ((Cardinal.one_lt_aleph0.trans_le hκ.aleph0_le).trans_le hJ)
        let j₀ : J := Classical.choice (inferInstance : Nonempty J)
        let touching : Set J :=
          ⋃ i : (f j₀).support, {j | i.val ∈ (f j).support}
        have hsupport : Cardinal.mk ((f j₀).support) < κ :=
          Cardinal.mk_lt_aleph0.trans_le hκ.aleph0_le
        have htouching : Cardinal.mk touching < κ :=
          (Cardinal.card_iUnion_lt_iff_forall_of_isRegular hκ hsupport).mpr
            (fun i => hsmall i.val)
        let bad : Set J := touching ∪ {j₀}
        have hbad : Cardinal.mk bad < κ := by
          apply (Cardinal.mk_union_le touching {j₀}).trans_lt
          apply Cardinal.add_lt_of_lt hκ.aleph0_le htouching
          rw [Cardinal.mk_singleton]
          exact Cardinal.one_lt_aleph0.trans_le hκ.aleph0_le
        have houtside : ∃ k : J, k ∉ bad := by
          by_contra! h
          have he : bad = Set.univ := Set.Subset.antisymm
            (Set.subset_univ _) (fun k _ => h k)
          have hcard : Cardinal.mk J < κ := by
            simpa only [he, Cardinal.mk_univ] using hbad
          exact (not_lt_of_ge hJ) hcard
        obtain ⟨k, hk⟩ := houtside
        have hjk : j₀ ≠ k := by
          intro he
          apply hk
          exact Or.inr (Set.mem_singleton_iff.mpr he.symm)
        refine ⟨j₀, k, hjk, compatible_of_disjoint_supports ?_⟩
        apply Set.disjoint_left.mpr
        intro i hi hj
        have hi' : i ∈ (f j₀).support :=
          (DFinsupp.mem_support_toFun (f j₀) i).mpr hi
        have hj' : i ∈ (f k).support :=
          (DFinsupp.mem_support_toFun (f k) i).mpr hj
        apply hk
        exact Or.inl (Set.mem_iUnion.mpr ⟨⟨i, hi'⟩, hj'⟩)

/-- A genuinely arbitrary κ-sized indexed family, without an externally
supplied uniform bound on its finite supports. -/
theorem product_compatible_pair
    (hκ : κ.IsRegular) (hunc : Cardinal.aleph0 < κ)
    (hfactor : ∀ i, Cardinal.mk (Erdos1172Collapse.Condition (A i)) < κ)
    {J : Type u} (f : J → ProductCondition A) (hJ : κ ≤ Cardinal.mk J) :
    ∃ j k, j ≠ k ∧ Compatible (f j) (f k) := by
  classical
  let size : J → ULift.{u} ℕ := fun j => ⟨supportSize (f j)⟩
  have hsize : Cardinal.mk (ULift.{u} ℕ) < κ.ord.cof := by
    simpa only [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0,
      hκ.cof_ord] using hunc
  obtain ⟨n, hn⟩ := Cardinal.infinite_pigeonhole_card size κ hJ
    hκ.aleph0_le hsize
  have hbound : ∀ j : size ⁻¹' {n}, supportSize (f j.val) ≤ n.down := by
    intro j
    have hj : size j.val = n := j.property
    exact le_of_eq (congrArg ULift.down hj)
  obtain ⟨j, k, hjk, hcomp⟩ := compatible_pair_of_bounded_support hκ hfactor n.down
    (fun j : size ⁻¹' {n} => f j.val) hn hbound
  exact ⟨j.val, k.val, (fun he => hjk (Subtype.ext he)), hcomp⟩

/-- The bound holds for arbitrary indexed disjoint positive Boolean values,
by selecting an actual condition below each value. -/
theorem completion_disjoint_family_cardinal_lt
    (hκ : κ.IsRegular) (hunc : Cardinal.aleph0 < κ)
    (hfactor : ∀ i, Cardinal.mk (Erdos1172Collapse.Condition (A i)) < κ)
    {J : Type u} (b : J → Completion (ProductCondition A))
    (hpos : ∀ j, b j ≠ ⊥)
    (hdisj : ∀ j k, j ≠ k → b j ⊓ b k = ⊥) :
    Cardinal.mk J < κ := by
  classical
  choose p hp using fun j => exists_condition_le (hpos j)
  by_contra h
  obtain ⟨j, k, hjk, r, hrj, hrk⟩ := product_compatible_pair hκ hunc hfactor p
    (le_of_not_gt h)
  have hr : condition r ≤ b j ⊓ b k :=
    le_inf ((condition_mono hrj).trans (hp j))
      ((condition_mono hrk).trans (hp k))
  exact condition_ne_bot r (bot_unique (hr.trans_eq (hdisj j k hjk)))

/-- Concrete Boolean κ-cc for the below-κ collapse, with no supplied
chain-condition or cardinal-preservation premise. -/
theorem below_completion_disjoint_family_cardinal_lt (κ : Cardinal.{u})
    (hκ : κ.IsRegular) (hunc : Cardinal.aleph0 < κ)
    {J : Type u} (b : J → Completion (BelowCondition κ))
    (hpos : ∀ j, b j ≠ ⊥)
    (hdisj : ∀ j k, j ≠ k → b j ⊓ b k = ⊥) :
    Cardinal.mk J < κ :=
  completion_disjoint_family_cardinal_lt hκ hunc (belowFactor_cardinal_lt κ hunc)
    b hpos hdisj

end Erdos1172LevyCollapse
