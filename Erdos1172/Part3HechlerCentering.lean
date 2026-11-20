/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3HechlerOrder

@[expose] public section

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3HechlerCentering

open ErdosRadoCHAsym (W1)
open Erdos1172Part3HechlerOrder

abbrev Stem : Type := {s : W1 → Option W1 // {i | s i ≠ none}.Countable}

def stemGraph (s : Stem) : Set (W1 × W1) := {p | s.val p.1 = some p.2}

theorem stemGraph_countable (s : Stem) : #(stemGraph s) ≤ ℵ₀ := by
  have hinj : Injective (fun p : stemGraph s =>
      (⟨p.val.1, by
        have h := p.property
        change s.val p.val.1 = some p.val.2 at h
        change s.val p.val.1 ≠ none
        rw [h]
        intro heq
        cases heq⟩ : {i | s.val i ≠ none})) := by
    intro p q heq
    apply Subtype.ext
    have hfst : p.val.1 = q.val.1 := congrArg Subtype.val heq
    apply Prod.ext hfst
    have hp := p.property
    have hq := q.property
    change s.val p.val.1 = some p.val.2 at hp
    change s.val q.val.1 = some q.val.2 at hq
    rw [hfst] at hp
    exact Option.some.inj (hp.symm.trans hq)
  exact (Cardinal.mk_le_of_injective hinj).trans
    (Cardinal.le_aleph0_iff_set_countable.mpr s.property)

theorem stemGraph_injective : Injective stemGraph := by
  intro s t heq
  apply Subtype.ext
  funext i
  cases hs : s.val i with
  | none =>
    cases ht : t.val i with
    | none => rfl
    | some v =>
      have hmem : (i, v) ∈ stemGraph s := by rw [heq]; exact ht
      change s.val i = some v at hmem
      rw [hs] at hmem
      cases hmem
  | some v =>
    have hmem : (i, v) ∈ stemGraph t := by rw [← heq]; exact hs
    exact hmem.symm

theorem mk_Stem_le (hCH : CH) : #Stem ≤ ℵ_ 1 := by
  let graphCode (s : Stem) : {t : Set (W1 × W1) // #t ≤ ℵ₀} :=
    ⟨stemGraph s, stemGraph_countable s⟩
  have hgraph : #Stem ≤ #{t : Set (W1 × W1) // #t ≤ ℵ₀} :=
    Cardinal.mk_le_of_injective (f := graphCode)
      (fun _ _ h => stemGraph_injective (congrArg Subtype.val h))
  have hprod : #(W1 × W1) = ℵ_ 1 := by
    simp only [Cardinal.mk_prod, Cardinal.lift_id, W1, Cardinal.mk_toType,
      Ordinal.card_omega, Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1)]
  apply hgraph.trans
  simpa only [hprod, max_eq_left (Cardinal.aleph0_le_aleph 1), hCH.aleph_one_power_aleph_zero]
    using Cardinal.mk_bounded_set_le (W1 × W1) ℵ₀

noncomputable def stemRank (hCH : CH) : Stem ↪ W1 := by
  exact Classical.choice ((Cardinal.le_def _ _).mp (by
    simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using mk_Stem_le hCH))

noncomputable def centerCode (hCH : CH) (p : Condition) : W1 :=
  stemRank hCH ⟨p.stem, p.stem_countable⟩

theorem exists_common_lower_of_same_stem (p0 : Condition) (C : Set Condition)
    (hC : C.Countable) (hstem : ∀ p ∈ C, p.stem = p0.stem) :
    ∃ q : Condition, ∀ p ∈ C, q ≤ p := by
  let q : Condition := ⟨p0.stem, p0.stem_countable, ⋃ p ∈ C, p.side,
    hC.biUnion (fun p _ => p.side_countable)⟩
  refine ⟨q, ?_⟩
  intro p hp
  refine ⟨?_, ?_, ?_⟩
  · intro i v hv
    change p0.stem i = some v
    rwa [hstem p hp] at hv
  · intro f hf
    exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hf⟩⟩
  · intro i hi v hv _ _
    change p0.stem i = some v at hv
    rw [hstem p hp] at hi
    rw [hi] at hv
    cases hv

/-- CH partitions the forcing order into omegaOne classes, each of which
has lower bounds for all its countable subsets. -/
theorem centerCode_countably_centered (hCH : CH) (C : Set Condition) (hC : C.Countable)
    (value : W1) (hvalue : ∀ p ∈ C, centerCode hCH p = value) :
    ∃ q : Condition, ∀ p ∈ C, q ≤ p := by
  by_cases hne : C.Nonempty
  · obtain ⟨p0, hp0⟩ := hne
    apply exists_common_lower_of_same_stem p0 C hC
    intro p hp
    have heq : (⟨p.stem, p.stem_countable⟩ : Stem) = ⟨p0.stem, p0.stem_countable⟩ :=
      (stemRank hCH).injective ((hvalue p hp).trans (hvalue p0 hp0).symm)
    exact congrArg Subtype.val heq
  · exact ⟨emptyCondition, fun _ hp => (hne ⟨_, hp⟩).elim⟩

theorem common_lower_of_same_code (hCH : CH) (p q : Condition)
    (heq : centerCode hCH p = centerCode hCH q) : ∃ r, r ≤ p ∧ r ≤ q := by
  have hstem : p.stem = q.stem := congrArg Subtype.val ((stemRank hCH).injective heq)
  obtain ⟨r, hr⟩ := exists_common_lower_of_same_stem q {p, q} (by simp)
    (by intro x hx; rcases hx with rfl | rfl <;> first | exact hstem | exact rfl)
  exact ⟨r, hr p (by simp), hr q (by simp)⟩

/-- The omegaTwo chain condition, stated without a forcing-model API. -/
theorem antichain_card_le (hCH : CH) (A : Set Condition)
    (hA : ∀ p ∈ A, ∀ q ∈ A, p ≠ q → ¬∃ r : Condition, r ≤ p ∧ r ≤ q) :
    #A ≤ ℵ_ 1 := by
  have hinj : Injective (fun p : A => centerCode hCH p.val) := by
    intro p q heq
    by_contra hne
    exact hA p.val p.property q.val q.property
      (fun h => hne (Subtype.ext h)) (common_lower_of_same_code hCH p.val q.val heq)
  simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using
    Cardinal.mk_le_of_injective hinj

theorem condition_ext {p q : Condition} (hstem : p.stem = q.stem) (hside : p.side = q.side) :
    p = q := by
  cases p
  cases q
  cases hstem
  cases hside
  rfl

/-- The concrete one-step order has size at most omegaTwo under GCH.
This is a cardinality statement about conditions, not a forcing extension. -/
theorem mk_Condition_le (hGCH : GCH) : #Condition ≤ ℵ_ 2 := by
  let Side := {s : Set (W1 → W1) // #s ≤ ℵ₀}
  have hfunc : #(W1 → W1) ≤ ℵ_ 2 := by
    rw [Cardinal.mk_arrow]
    simp only [Cardinal.lift_id, W1, Cardinal.mk_toType, Ordinal.card_omega]
    exact (Cardinal.power_le_power_right
      (Cardinal.aleph_le_aleph.mpr (by norm_num : (1 : Ordinal.{0}) ≤ 2))).trans_eq
        hGCH.aleph_two_power_aleph_one
  have hside : #Side ≤ ℵ_ 2 := by
    apply (Cardinal.mk_bounded_set_le (W1 → W1) ℵ₀).trans
    exact (Cardinal.power_le_power_right (max_le hfunc (Cardinal.aleph0_le_aleph 2))).trans_eq
      hGCH.aleph_two_power_aleph_zero
  let code (p : Condition) : Stem × Side :=
    (⟨p.stem, p.stem_countable⟩,
      ⟨p.side, Cardinal.le_aleph0_iff_set_countable.mpr p.side_countable⟩)
  have hinj : Injective code := by
    intro p q h
    apply condition_ext
    · exact congrArg (fun c : Stem × Side => c.1.val) h
    · exact congrArg (fun c : Stem × Side => c.2.val) h
  apply (Cardinal.mk_le_of_injective hinj).trans
  rw [Cardinal.mk_prod]
  simp only [Cardinal.lift_id]
  exact (mul_le_mul' ((mk_Stem_le hGCH.toCH).trans
    (Cardinal.aleph_le_aleph.mpr (by norm_num : (1 : Ordinal.{0}) ≤ 2))) hside).trans_eq
      (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 2))

end Erdos1172Part3HechlerCentering
