/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaShortThreadUnion

@[expose] public section

/-! # Meeting stagewise requirements with descending threads on growing domains -/

set_option autoImplicit false
noncomputable section
universe u
namespace Erdos1172Shioya.InverseSystem

/-- At each stage, fuse the earlier threads on the open initial segment,
then use the supplied extension to meet the new requirement. Only proper
initial segments of the index order need to be short. -/
theorem exists_thread_decision_run {θ : Cardinal.{u}} {J : Type u}
    [LinearOrder J] [WellFoundedLT J] (P : J → Type u) [∀ i, PartialOrder (P i)]
    (ρ : ∀ {i j : J}, i < j → PartialProjection θ (P j) (P i))
    (hJ : ∀ j : J, Cardinal.mk (Set.Iio j) < θ) (hP : ∀ i, ShortInfima θ (P i))
    (m : ∀ j, P j) (K : ∀ j, Set (P j))
    (extend : ∀ (j : J) (r : Thread P ρ (Set.Iio j)), (∀ i, r.val i ≤ m i.val) →
      ∃ t : Thread P ρ (Set.Iic j), (∀ i, t.val i ≤ m i.val) ∧
        t.val ⟨j,le_rfl⟩ ∈ K j ∧ ∀ i : Set.Iio j, t.val ⟨i.val,i.property.le⟩ ≤ r.val i) :
    ∃ t : ∀ j, Thread P ρ (Set.Iic j), (∀ j i, (t j).val i ≤ m i.val) ∧
      (∀ j, (t j).val ⟨j,le_rfl⟩ ∈ K j) ∧ ∀ (i j : J) (hij : i < j) (k : Set.Iic i),
        (t j).val ⟨k.val,k.property.trans hij.le⟩ ≤ (t i).val k := by
  classical
  let T (j : J) := Thread P ρ (Set.Iic j)
  let good (j : J) (past : ∀ i, i < j → Option (T i)) (t : T j) : Prop :=
    (∀ i, t.val i ≤ m i.val) ∧ t.val ⟨j,le_rfl⟩ ∈ K j ∧
      ∀ (i : J) (hij : i < j) (r : T i), past i hij = some r → ∀ k : Set.Iic i,
        t.val ⟨k.val,k.property.trans hij.le⟩ ≤ r.val k
  let step (j : J) (past : ∀ i, i < j → Option (T i)) : Option (T j) :=
    if h : ∃ t, good j past t then some h.choose else none
  let q : ∀ j, Option (T j) := wellFounded_lt.fix step
  have eqn (j : J) : q j = step j (fun i _ => q i) := WellFounded.fix_eq _ _ _
  have valid (j : J) : ∃ t, q j = some t ∧ good j (fun i _ => q i) t := by
    induction j using (wellFounded_lt : WellFounded ((· < ·) : J → J → Prop)).induction with
    | h j ih =>
      choose t ht hg using fun i : Set.Iio j => ih i.val i.property
      let s (i : Set.Iio j) : Set J := Set.Iic i.val
      have mono : Monotone s := fun _ _ h _ hk => hk.trans h
      have inside (i : Set.Iio j) : s i ⊆ Set.Iio j := fun _ hk => hk.trans_lt i.property
      have cover (i : Set.Iio j) : ∃ n, i.val ∈ s n := ⟨i,le_rfl⟩
      have dec (i l : Set.Iio j) (h : i ≤ l) (k : s i) :
          (t l).val ⟨k.val,mono h k.property⟩ ≤ (t i).val k := by
        rcases h.lt_or_eq with hlt | rfl
        · exact (hg l).2.2 i.val hlt (t i) (ht i) k
        · exact le_rfl
      obtain ⟨r,hr⟩ := exists_thread_on_short_union P ρ (hJ j) hP (Set.Iio j)
        s mono inside cover t dec
      have below (i : Set.Iio j) : r.val i ≤ m i.val :=
        (hr i ⟨i.val,le_rfl⟩).trans ((hg i).1 _)
      obtain ⟨z,hm,hK,hz⟩ := extend j r below
      have fits : ∃ v, good j (fun i _ => q i) v := by
        refine ⟨z,hm,hK,?_⟩
        intro i hij v hv k
        let n : Set.Iio j := ⟨i,hij⟩
        have he : t n = v := Option.some.inj ((ht n).symm.trans hv)
        subst v
        exact (hz ⟨k.val,k.property.trans_lt hij⟩).trans (hr n k)
      exact ⟨fits.choose,(eqn j).trans (dif_pos fits),fits.choose_spec⟩
  choose t ht hg using valid
  exact ⟨t,fun j => (hg j).1,fun j => (hg j).2.1,
    fun i j hij => (hg j).2.2 i hij (t i) (ht i)⟩

end Erdos1172Shioya.InverseSystem
