/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3FailureFiber

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3FiniteIdealEndpoint

open Erdos1172Part3Failure

/-- Only finite closure is required at the two-successor endpoint. -/
structure FiniteSmallness (V : Type) where
  small : Set V → Prop
  empty_small : small ∅
  mono : ∀ {s t}, s ⊆ t → small t → small s
  union_small : ∀ {s t}, small s → small t → small (s ∪ t)

namespace FiniteSmallness

theorem positive_sdiff {V : Type} (J : FiniteSmallness V) {s t : Set V}
    (hs : ¬J.small s) (ht : J.small t) : ¬J.small (s \ t) := by
  intro h
  exact hs (J.mono (by intro x hx; by_cases hxt : x ∈ t <;> simp_all)
    (J.union_small h ht))

/-- The dual filter, restricted to one positive row set. -/
def dual {V : Type} (J : FiniteSmallness V) (rows : Set V) : Filter V where
  sets := {s | J.small (rows \ s)}
  univ_sets := by simpa using J.empty_small
  sets_of_superset := by
    intro s t hs hst
    change J.small (rows \ s) at hs
    change J.small (rows \ t)
    exact J.mono (show rows \ t ⊆ rows \ s from
      fun x hx => ⟨hx.1, fun hxs => hx.2 (hst hxs)⟩) hs
  inter_sets := by
    intro s t hs ht
    change J.small (rows \ s) at hs
    change J.small (rows \ t) at ht
    change J.small (rows \ (s ∩ t))
    simpa only [Set.sdiff_inter] using J.union_small hs ht

theorem exists_positive_ultrafilter {V : Type} (J : FiniteSmallness V)
    (rows : Set V) (hrows : ¬J.small rows) :
    ∃ U : Ultrafilter V, rows ∈ U ∧ ∀ s ∈ U, ¬J.small s := by
  let f := J.dual rows
  have hf : Filter.NeBot f := by
    refine ⟨fun h => ?_⟩
    have he : (∅ : Set V) ∈ f := by rw [h]; exact Filter.mem_bot
    change J.small (rows \ ∅) at he
    exact hrows (by simpa using he)
  let _ := hf
  obtain ⟨U, hU⟩ := Ultrafilter.exists_le f
  refine ⟨U, hU (by change J.small (rows \ rows); simpa using J.empty_small), ?_⟩
  intro s hs hsmall
  have hc : sᶜ ∈ U := hU (show J.small (rows \ sᶜ) from
    J.mono (by intro x hx; simpa only [Set.mem_compl_iff, not_not] using hx.2) hsmall)
  exact (Ultrafilter.compl_notMem_iff.mpr hs) hc

end FiniteSmallness

theorem clique_add_two {K : SimpleGraph W2} {s : Set W2} {δ : Ordinal}
    (hs : K.IsClique s) (hstype : typeLT s = δ) {p q : W2}
    (hp : ∀ x ∈ s, x < p) (hpq : p < q) (hedge : K.Adj p q)
    (hsp : ∀ x ∈ s, K.Adj x p) (hsq : ∀ x ∈ s, K.Adj x q) :
    OrdinalRamsey.HasCliqueOfType K (δ + 2) := by
  have hi : K.IsClique (insert p s) := hs.insert (fun x hx _ => (hsp x hx).symm)
  have hit : typeLT (insert p s : Set W2) = δ + 1 := by
    change typeLT (Set.insert p s : Set W2) = δ + 1
    rw [Ordinal.typeLT_insert_of_forall_lt hp, hstype]
  obtain ⟨t, ht, htt⟩ := K.exists_clique_type_add_one_of_common_later hi hit
    (x := q) (by
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact hpq
      · exact (hp x hx).trans hpq) (by
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact hedge
      · exact hsq x hx)
  exact ⟨t, ht, by simpa only [add_assoc, one_add_one_eq_two] using htt⟩

/-- A large future with one ultrafilter color either has a pair of that
color, or is an entire clique of the opposite color. -/
theorem endpoint_of_uniform_future
    (K L : SimpleGraph W2) (hcompl : IsCompl K L)
    (δ ε : Ordinal) (hε : ε ≤ ω_ 2)
    (U : Ultrafilter W2) (rows : Set W2) (a : W2)
    (hrows : rows ∈ U) (hbefore : rows ⊆ Set.Iio a)
    (hcore : ∀ s ∈ U, s ⊆ rows → ∃ c ⊆ s, K.IsClique c ∧ typeLT c = δ)
    (future : Set W2) (hcard : #future = ℵ_ 2)
    (hlater : future ⊆ Set.Ioi a)
    (huniform : ∀ y ∈ future, {x | K.Adj x y} ∈ U) :
    OrdinalRamsey.HasCliqueOfType K (δ + 2) ∨
      OrdinalRamsey.HasCliqueOfType L ε := by
  classical
  by_cases hpair : ∃ p ∈ future, ∃ q ∈ future, p < q ∧ K.Adj p q
  · obtain ⟨p, hp, q, hq, hpq, hpqK⟩ := hpair
    let common : Set W2 := rows ∩ {x | K.Adj x p} ∩ {x | K.Adj x q}
    have hm : common ∈ U := Filter.inter_mem (Filter.inter_mem hrows
      (huniform p hp)) (huniform q hq)
    obtain ⟨c, hcs, hc, hct⟩ := hcore common hm (fun x hx => hx.1.1)
    exact Or.inl (clique_add_two hc hct
      (fun x hx => (hbefore (hcs hx).1.1).trans (hlater hp)) hpq hpqK
      (fun x hx => (hcs hx).1.2) (fun x hx => (hcs hx).2))
  · have hL : L.IsClique future := by
      intro x hx y hy hxy
      rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
      refine ⟨hxy, ?_⟩
      intro hK
      rcases lt_or_gt_of_ne hxy with hlt | hgt
      · exact hpair ⟨x, hx, y, hy, hlt, hK⟩
      · exact hpair ⟨y, hy, x, hx, hgt, hK.symm⟩
    obtain ⟨c, hcs, hct⟩ := Ordinal.exists_subset_typeLT_eq future
      (show ε ≤ typeLT future by rwa [typeLT_eq_omegaTwo_of_mk_eq hcard])
    exact Or.inr ⟨c, hL.subset hcs, hct⟩

/-- A positive finite ideal in which every positive row set has both
homogeneous cores closes both two-successor targets. No countable
completeness, stationary intersection, or common whole-row neighborhood
is assumed. -/
theorem targets_of_mixed_positive_ideal
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (δ β : Ordinal) (hδ : δ + 2 ≤ ω_ 2) (hβ : β + 2 ≤ ω_ 2)
    (J : FiniteSmallness W2) (rows : Set W2) (a : W2)
    (hrows : ¬J.small rows) (hbefore : rows ⊆ Set.Iio a)
    (hred : ∀ s ⊆ rows, ¬J.small s → ∃ c ⊆ s, red.IsClique c ∧ typeLT c = δ)
    (hblue : ∀ s ⊆ rows, ¬J.small s → ∃ c ⊆ s, blue.IsClique c ∧ typeLT c = β) :
    OrdinalRamsey.HasCliqueOfType red (δ + 2) ∨
      OrdinalRamsey.HasCliqueOfType blue (β + 2) := by
  classical
  obtain ⟨U, hUrows, hUpositive⟩ := J.exists_positive_ultrafilter rows hrows
  let color : Set.Ioi a → Bool := fun y => decide ({x | red.Adj x y} ∈ U)
  have htail := mk_Ioi_omegaTwo_eq a
  obtain ⟨b, hb⟩ := Cardinal.infinite_pigeonhole color
    (by rw [htail]; exact Cardinal.aleph0_le_aleph 2) (by
      rw [htail]
      have hreg : (ℵ_ 2 : Cardinal.{0}).IsRegular := by
        convert Cardinal.isRegular_aleph_add_one 1 using 1 <;> norm_num
      rw [hreg.cof_ord]
      simpa only [Cardinal.mk_fintype, Fintype.card_bool, Nat.cast_ofNat] using
        (Cardinal.natCast_lt_aleph0 : (2 : Cardinal) < ℵ₀).trans_le
          (Cardinal.aleph0_le_aleph 2))
  let future : Set W2 := Subtype.val '' (color ⁻¹' {b})
  have hfuture : #future = ℵ_ 2 := (Cardinal.mk_image_eq Subtype.val_injective).trans
    (hb.trans htail)
  have hlater : future ⊆ Set.Ioi a := by
    rintro _ ⟨y, _, rfl⟩
    exact y.property
  have hcolor : ∀ y (hy : y ∈ future), color ⟨y, hlater hy⟩ = b := by
    rintro _ ⟨y, hy, rfl⟩
    exact hy
  cases b with
  | true =>
      apply endpoint_of_uniform_future red blue hcompl δ (β + 2) hβ U rows a
        hUrows hbefore (fun s hs hsub => hred s hsub (hUpositive s hs))
        future hfuture hlater
      intro y hy
      have h := hcolor y hy
      simpa only [color, decide_eq_true_eq] using h
  | false =>
      apply Or.symm
      apply endpoint_of_uniform_future blue red hcompl.symm β (δ + 2) hδ U rows a
        hUrows hbefore (fun s hs hsub => hblue s hsub (hUpositive s hs))
        future hfuture hlater
      intro y hy
      have hn : {x | red.Adj x y} ∉ U := by
        simpa only [color, decide_eq_false_iff_not] using hcolor y hy
      have hc := U.compl_mem_iff_notMem.mpr hn
      apply Filter.mem_of_superset (Filter.inter_mem hUrows hc)
      intro x hx
      change blue.Adj x y
      rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
      exact ⟨((hbefore hx.1).trans (hlater hy)).ne, hx.2⟩

end Erdos1172Part3FiniteIdealEndpoint
