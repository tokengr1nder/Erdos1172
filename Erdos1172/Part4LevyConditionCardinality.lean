/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyCompatibility
public import Mathlib.Data.Finset.Image

@[expose] public section

/-!
# Cardinality of the actual finite-support collapse conditions

A condition is encoded by the finite graph of its nonempty coordinates.
The graph retains both the coordinate and its complete finite sequence.
The below-cardinal product consequently has at most κ conditions whenever
κ is uncountable. No regularity, strong-limit property, chain condition,
Boolean-name counting, or GCH premise is used in this cardinality bound.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace Erdos1172LevyCollapse

open scoped Erdos1172LevyCollapse

variable {I : Type u} {A : I → Type u}

/-- The actual finite graph of the nonzero (nonempty) coordinates. -/
def supportGraph (p : ProductCondition A) :
    Finset (Σ i : I, Erdos1172Collapse.Condition (A i)) := by
  classical
  exact p.support.attach.image (fun i => ⟨i.val, p i.val⟩)

theorem mem_supportGraph_iff (p : ProductCondition A) (i : I)
    (a : Erdos1172Collapse.Condition (A i)) :
    Sigma.mk i a ∈ supportGraph p ↔ a ≠ 0 ∧ p i = a := by
  classical
  unfold supportGraph
  constructor
  · intro h
    obtain ⟨⟨j, hj⟩, _, heq⟩ := Finset.mem_image.mp h
    have hji : j = i := congrArg Sigma.fst heq
    subst j
    have hval : p i = a := eq_of_heq (Sigma.mk.inj_iff.mp heq).2
    have hnonzero : p i ≠ 0 := DFinsupp.mem_support_iff.mp hj
    exact ⟨hval ▸ hnonzero, hval⟩
  · rintro ⟨ha, hval⟩
    have hi : i ∈ p.support := DFinsupp.mem_support_iff.mpr (hval.symm ▸ ha)
    refine Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_attach _ _, ?_⟩
    change (⟨i, p i⟩ : Σ j : I, Erdos1172Collapse.Condition (A j)) = ⟨i, a⟩
    rw [hval]

/-- Equality of the finite graphs recovers every coordinate, including
the omitted zero coordinates. -/
theorem supportGraph_injective : Function.Injective (supportGraph (A := A)) := by
  classical
  intro p q hpq
  apply DFinsupp.ext
  intro i
  by_cases hp : p i = 0
  · by_cases hq : q i = 0
    · exact hp.trans hq.symm
    · have hmem : Sigma.mk i (q i) ∈ supportGraph q :=
        (mem_supportGraph_iff q i (q i)).mpr ⟨hq, rfl⟩
      rw [← hpq] at hmem
      exact (mem_supportGraph_iff p i (q i)).mp hmem |>.2
  · have hmem : Sigma.mk i (p i) ∈ supportGraph p := (mem_supportGraph_iff p i (p i)).mpr ⟨hp, rfl⟩
    rw [hpq] at hmem
    exact ((mem_supportGraph_iff q i (p i)).mp hmem).2.symm

theorem productCondition_cardinal_le_finite_graphs :
    Cardinal.mk (ProductCondition A) ≤
      Cardinal.mk (Finset (Σ i : I, Erdos1172Collapse.Condition (A i))) :=
  Cardinal.mk_le_of_injective supportGraph_injective

/-- All coordinate/value pairs together have at most κ possible values. -/
theorem belowCoordinateValues_cardinal_le (κ : Cardinal.{u})
    (hκ : Cardinal.aleph0 < κ) :
    Cardinal.mk (Σ i : κ.ord.ToType, Erdos1172Collapse.Condition (Set.Iio i)) ≤ κ := by
  calc
    Cardinal.mk (Σ i : κ.ord.ToType,
        Erdos1172Collapse.Condition (Set.Iio i)) =
        Cardinal.sum (fun i : κ.ord.ToType =>
          Cardinal.mk (Erdos1172Collapse.Condition (Set.Iio i))) :=
      Cardinal.mk_sigma _
    _ ≤ Cardinal.sum (fun _ : κ.ord.ToType => κ) :=
      Cardinal.sum_le_sum _ _ (fun i => (belowFactor_cardinal_lt κ hκ i).le)
    _ = κ * κ := by rw [Cardinal.sum_const', Cardinal.mk_ord_toType]
    _ = κ := Cardinal.mul_eq_self hκ.le

/-- The actual finite-support below-κ collapse has at most κ conditions.
This bound needs uncountability but neither regularity nor inaccessibility. -/
theorem belowCondition_cardinal_le (κ : Cardinal.{u})
    (hκ : Cardinal.aleph0 < κ) : Cardinal.mk (BelowCondition κ) ≤ κ := by
  let W := Σ i : κ.ord.ToType, Erdos1172Collapse.Condition (Set.Iio i)
  have hindex : Cardinal.mk κ.ord.ToType ≤ Cardinal.mk W :=
    Cardinal.mk_le_of_injective (f := fun i : κ.ord.ToType =>
      (⟨i, ⊤⟩ : W)) (fun _ _ h => congrArg Sigma.fst h)
  have hW : Cardinal.aleph0 ≤ Cardinal.mk W := by
    rw [Cardinal.mk_ord_toType] at hindex
    exact hκ.le.trans hindex
  let : Infinite W := Cardinal.infinite_iff.mpr hW
  calc
    Cardinal.mk (BelowCondition κ) ≤ Cardinal.mk (Finset W) :=
      productCondition_cardinal_le_finite_graphs
    _ = Cardinal.mk W := Cardinal.mk_finset_of_infinite W
    _ ≤ κ := belowCoordinateValues_cardinal_le κ hκ

end Erdos1172LevyCollapse
