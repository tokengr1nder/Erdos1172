/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.SetTheory.Cardinal.Cofinality.Club
public import Erdos1172.ForMathlib.SetTheory.Ordinal.DushnikMiller

@[expose] public section

open Cardinal Ordinal Set

/-!
# Club diagonal intersections, pressing down, and regular cofinality suprema

This file develops diagonal intersections of clubs, Fodor's pressing-down lemma on regular
uncountable initial ordinals, and stationarity / boundedness helpers for `I`-indexed suprema.
-/

universe u

namespace Set

/-- A stationary subset of a linear order is cofinal. -/
theorem IsStationary.isCofinal {V : Type u} [LinearOrder V] {s : Set V}
    (hs : IsStationary s) : IsCofinal s := by
  by_contra hcof
  obtain ⟨cutoff, hcutoff⟩ := not_isCofinal_iff.1 hcof
  have hclub : IsClub (Ici cutoff) :=
    ⟨fun _ hd ⟨x, hx⟩ _ _ htop ↦ (hd hx).trans (htop.1 hx),
     fun x ↦ ⟨max cutoff x, le_max_left _ _, le_max_right _ _⟩⟩
  obtain ⟨x, hx, hxc⟩ := hs hclub
  exact (not_lt_of_ge hxc) (hcutoff x hx)

/-- Fodor's pressing-down principle on a linear order. -/
def StationaryPressingDown (V : Type u) [LinearOrder V] : Prop :=
  ∀ (s : Set V) (f : V → V), IsStationary s →
    (∀ x ∈ s, f x < x) → ∃ value, IsStationary {x | x ∈ s ∧ f x = value}

/-- The diagonal intersection `{x | ∀ y < x, x ∈ C y}`. -/
def diagonalInter {V : Type u} [LT V] (C : V → Set V) : Set V :=
  {x | ∀ y, y < x → x ∈ C y}

/-- Diagonal intersections of clubs in an uncountable regular initial ordinal are club. -/
theorem isClub_diagonalInter_ord
    (k : Cardinal.{u}) (hk : k.IsRegular) (huncountable : ℵ₀ < k)
    (C : k.ord.ToType → Set k.ord.ToType) (hC : ∀ x, IsClub (C x)) :
    IsClub (diagonalInter C) := by
  classical
  let V := k.ord.ToType
  let _ : Nonempty V := Cardinal.nonempty_ord_toType hk.ne_zero
  let _ : OrderBot V := WellFoundedLT.toOrderBot V
  let _ : ConditionallyCompleteLinearOrderBot V :=
    WellFoundedLT.conditionallyCompleteLinearOrderBot V
  have hcof : Order.cof V ≠ ℵ₀ := by
    simpa [V, Ordinal.cof_toType, hk.cof_ord] using huncountable.ne'
  have hclubs (x : V) : IsClub (⋂ a : Set.Iic x, C a.1) := by
    refine IsClub.iInter hcof ?_ (fun a ↦ hC a.1)
    simpa [V, Ordinal.cof_toType, hk.cof_ord] using
      Cardinal.mk_Iic_lt x (by simp [V]) (by simpa [V] using hk.aleph0_le)
  let next (x : V) : V := Classical.choose ((hclubs x).isCofinal x)
  have next_spec (x : V) := Classical.choose_spec ((hclubs x).isCofinal x)
  refine ⟨?_, fun start ↦ ?_⟩
  · intro d hd _ _ top htop a ha
    have hex : ∃ x ∈ d, a < x := by
      by_contra! h
      exact (not_lt_of_ge (htop.2 h)) ha
    obtain ⟨x, hxd, hax⟩ := hex
    let tail : Set V := d ∩ Set.Ioi a
    have htail_sub : tail ⊆ C a := fun y hy ↦ hd hy.1 a hy.2
    have htail_lub : IsLUB tail top :=
      ⟨fun y hy ↦ htop.1 hy.1, fun b hb ↦ htop.2 fun y hy ↦
        if hay : a < y then hb ⟨hy, hay⟩
        else (le_of_not_gt hay).trans (hax.le.trans (hb ⟨hxd, hax⟩))⟩
    exact (hC a).isLUB_mem htail_sub ⟨x, hxd, hax⟩ htail_lub
  · let seq : ℕ → V := fun n ↦ next^[n] start
    have seq_succ (n : ℕ) : seq (n + 1) = next (seq n) := by
      simp [seq, Function.iterate_succ_apply']
    have seq_mono : Monotone seq :=
      monotone_nat_of_le_succ fun n ↦ by rw [seq_succ]; exact (next_spec _).2
    have seq_bdd : BddAbove (Set.range seq) := .of_not_isCofinal fun hseq ↦ by
      have hle : k ≤ #(Set.range seq) := by
        simpa [V, Ordinal.cof_toType, hk.cof_ord] using Order.cof_le hseq
      exact huncountable.not_ge (hle.trans (by simpa using Cardinal.mk_range_le_lift (f := seq)))
    let limit : V := sSup (Set.range seq)
    have limit_lub : IsLUB (Set.range seq) limit :=
      isLUB_csSup (Set.range_nonempty seq) seq_bdd
    refine ⟨limit, fun a ha ↦ ?_, limit_lub.1 ⟨0, rfl⟩⟩
    have hex : ∃ n, a < seq n := by
      by_contra! h
      exact ha.not_ge (limit_lub.2 (by rintro _ ⟨n, rfl⟩; exact h n))
    obtain ⟨n, han⟩ := hex
    let tail : Set V := Set.range fun m ↦ seq (n + 1 + m)
    have htail_sub : tail ⊆ C a := by
      rintro _ ⟨m, rfl⟩
      change seq (n + 1 + m) ∈ C a
      rw [show n + 1 + m = (n + m) + 1 by omega, seq_succ]
      exact Set.mem_iInter.mp (next_spec (seq (n + m))).1
        ⟨a, han.le.trans (seq_mono (Nat.le_add_right n m))⟩
    have htail_lub : IsLUB tail limit := by
      refine ⟨fun x hx ↦ ?_, fun b hb ↦ limit_lub.2 ?_⟩
      · obtain ⟨m, rfl⟩ := hx
        exact limit_lub.1 ⟨_, rfl⟩
      · rintro _ ⟨j, rfl⟩
        exact (seq_mono (show j ≤ n + 1 + j by omega)).trans (hb ⟨j, rfl⟩)
    exact (hC a).isLUB_mem htail_sub (Set.range_nonempty _) htail_lub

/-- Fodor's pressing-down lemma for every uncountable regular initial ordinal. -/
theorem stationaryPressingDown_ord
    (k : Cardinal.{u}) (hk : k.IsRegular) (huncountable : ℵ₀ < k) :
    StationaryPressingDown k.ord.ToType := by
  intro s f hs hreg
  by_contra! hnonstationary
  choose C hC hdisjoint using fun value ↦ not_isStationary_iff.mp (hnonstationary value)
  obtain ⟨x, hxs, hxdiag⟩ := hs (isClub_diagonalInter_ord k hk huncountable C hC)
  exact Set.disjoint_left.mp (hdisjoint (f x)) ⟨hxs, rfl⟩ (hxdiag (f x) (hreg x hxs))

/-- If `#I < cof V`, points which are suprema of strictly increasing `I`-sequences are stationary. -/
theorem isStationary_exists_strictMono_isLUB {I V : Type}
    [LinearOrder I] [WellFoundedLT I] [Nonempty I]
    [LinearOrder V] [WellFoundedLT V] [Nonempty V]
    (hI : #I < Order.cof V) :
    IsStationary {top : V | ∃ seq : I → V, StrictMono seq ∧ IsLUB (Set.range seq) top} := by
  classical
  let _ : OrderBot V := WellFoundedLT.toOrderBot V
  let _ : ConditionallyCompleteLinearOrderBot V :=
    WellFoundedLT.conditionallyCompleteLinearOrderBot V
  intro C hC
  have hex (i : I) (prev : ∀ j, j < i → V) : ∃ x ∈ C, ∀ j (hj : j < i), prev j hj < x := by
    let prior : Set V := Set.range fun j : Set.Iio i ↦ prev j.1 j.2
    have hlt : #prior < Order.cof V :=
      (Cardinal.mk_range_le.trans (Cardinal.mk_subtype_le _)).trans_lt hI
    obtain ⟨b, hb⟩ := not_isCofinal_iff.mp fun hc ↦ hlt.not_ge (Order.cof_le hc)
    obtain ⟨x, hxC, hbx⟩ := hC.isCofinal b
    exact ⟨x, hxC, fun j hj ↦ (hb _ ⟨⟨j, hj⟩, rfl⟩).trans_le hbx⟩
  let step (i : I) (prev : ∀ j, j < i → V) : V := Classical.choose (hex i prev)
  let seq : I → V := WellFoundedLT.fix step
  have hstep (i : I) : seq i ∈ C ∧ ∀ j (hj : j < i), seq j < seq i := by
    have heq : seq i = step i (fun j _ ↦ seq j) := WellFoundedLT.fix_eq step i
    rw [heq]
    exact Classical.choose_spec (hex i (fun j _ ↦ seq j))
  have hseq : StrictMono seq := fun i j hij ↦ (hstep j).2 i hij
  have hbdd : BddAbove (Set.range seq) := .of_not_isCofinal fun hc ↦
    (Cardinal.mk_range_le.trans_lt hI).not_ge (Order.cof_le hc)
  have hlub : IsLUB (Set.range seq) (sSup (Set.range seq)) :=
    isLUB_csSup (Set.range_nonempty seq) hbdd
  exact ⟨_, ⟨seq, hseq, hlub⟩,
    hC.isLUB_mem (by rintro _ ⟨i, rfl⟩; exact (hstep i).1) (Set.range_nonempty seq) hlub⟩

/-- Any `< cof I`-sized set strictly below an `I`-supremum has a strict bound below it. -/
theorem exists_strict_bound_of_strictMono_isLUB {I V : Type}
    [LinearOrder I] [NoMaxOrder I] [LinearOrder V]
    {top : V} {seq : I → V} (hseq : StrictMono seq) (htop : IsLUB (Set.range seq) top)
    {seed : Set V} (hseed : #seed < Order.cof I) (hbelow : ∀ y ∈ seed, y < top) :
    ∃ cutoff : V, cutoff < top ∧ ∀ y ∈ seed, y < cutoff := by
  classical
  have habove (y : seed) : ∃ i : I, y.1 < seq i := by
    by_contra! hnone
    exact (hbelow y.1 y.2).not_ge (htop.2 (by rintro _ ⟨i, rfl⟩; exact hnone i))
  let idx : seed → I := fun y ↦ Classical.choose (habove y)
  have hnot : ¬ IsCofinal (Set.range idx) := fun hc ↦
    (Cardinal.mk_range_le.trans_lt hseed).not_ge (Order.cof_le hc)
  obtain ⟨i, hi⟩ := not_isCofinal_iff.mp hnot
  obtain ⟨j, hij⟩ := exists_gt i
  refine ⟨seq i, (hseq hij).trans_le (htop.1 ⟨j, rfl⟩), fun y hy ↦ ?_⟩
  exact (Classical.choose_spec (habove ⟨y, hy⟩)).trans (hseq (hi _ ⟨⟨y, hy⟩, rfl⟩))

end Set
