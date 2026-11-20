/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.SetTheory.Cardinal.Cofinality.Club
public import Erdos1172.ForMathlib.SetTheory.Ordinal.DushnikMiller

@[expose] public section

open Cardinal Ordinal Set

/-!
# The countable-successor step in the Erdős--Dushnik--Miller argument

For a graph `blue` on a well-order and a finite blue seed `b`, `barrierCore blue b β`
is the set of possible top vertices `γ > β` for the seed which are *minimal above `β`*:
no intermediate vertex extends the same seed together with `γ` to a blue clique.

The key finite-seed observation is completely elementary: a barrier core is a clique in
the complementary (red) graph.  Conversely, repeatedly failing to find a barrier at one
fixed top constructs a blue copy of `ω+1`.  Fodor's pressing-down lemma then uniformizes
the pointwise finite seeds on a stationary final segment, proving the classical Erdős--Rado
sharpening `κ → (κ, ω+1)²` for every regular uncountable cardinal.
-/

universe u

namespace Set

/-- A stationary subset of a linear order is cofinal.  The club witnessing this is the
closed final segment above a strict upper bound. -/
theorem IsStationary.isCofinal {V : Type u} [LinearOrder V] {s : Set V}
    (hs : IsStationary s) : IsCofinal s := by
  by_contra hcof
  obtain ⟨cutoff, hcutoff⟩ := not_isCofinal_iff.1 hcof
  have hclosed : DirSupClosed (Ici cutoff) := by
    intro d hd hne _ top htop
    obtain ⟨x, hx⟩ := hne
    exact (hd hx).trans (htop.1 hx)
  have hclub : IsClub (Ici cutoff) :=
    ⟨hclosed, fun x ↦ ⟨max cutoff x, le_max_left _ _, le_max_right _ _⟩⟩
  obtain ⟨x, hx, hxc⟩ := hs hclub
  exact (not_lt_of_ge hxc) (hcutoff x hx)

/-- The pressing-down principle, stated independently so that the finite-seed part of the
Erdős--Rado argument can be developed without depending on a particular implementation of
clubs and diagonal intersections. -/
def StationaryPressingDown (V : Type u) [LinearOrder V] : Prop :=
  ∀ (s : Set V) (f : V → V), IsStationary s →
    (∀ x ∈ s, f x < x) → ∃ value, IsStationary {x | x ∈ s ∧ f x = value}

/-- Pressing down one point at a time also uniformizes a regressive finite set of fixed size. -/
theorem StationaryPressingDown.finset_of_card
    {V : Type u} [LinearOrder V] [OrderBot V] [WellFoundedLT V]
    (hpress : StationaryPressingDown V) (n : ℕ) (s : Set V) (f : V → Finset V)
    (hs : IsStationary s)
    (hreg : ∀ x ∈ s, ∀ y ∈ f x, y < x)
    (hcard : ∀ x ∈ s, (f x).card = n) :
    ∃ b : Finset V, IsStationary {x | x ∈ s ∧ f x = b} := by
  induction n generalizing s f with
  | zero =>
      refine ⟨∅, hs.mono fun x hx ↦ ⟨hx, Finset.card_eq_zero.mp (hcard x hx)⟩⟩
  | succ n ih =>
      classical
      let top (x : V) : V :=
        if h : (f x).Nonempty then (f x).max' h else ⊥
      have htop_reg : ∀ x ∈ s, top x < x := by
        intro x hx
        have hne : (f x).Nonempty := Finset.card_pos.mp (by simp [hcard x hx])
        rw [show top x = (f x).max' hne by simp only [top, dif_pos hne]]
        rw [Finset.max'_lt_iff]
        exact hreg x hx
      obtain ⟨value, hvalue⟩ := hpress s top hs htop_reg
      let t : Set V := {x | x ∈ s ∧ top x = value}
      let g (x : V) : Finset V := (f x).erase value
      have hvalue_mem : ∀ x ∈ t, value ∈ f x := by
        intro x hx
        have hne : (f x).Nonempty := Finset.card_pos.mp (by simp [hcard x hx.1])
        have htop : top x = (f x).max' hne := by simp only [top, dif_pos hne]
        rw [← hx.2, htop]
        exact Finset.max'_mem _ _
      have hg_reg : ∀ x ∈ t, ∀ y ∈ g x, y < x := by
        intro x hx y hy
        exact hreg x hx.1 y (Finset.mem_of_mem_erase hy)
      have hg_card : ∀ x ∈ t, (g x).card = n := by
        intro x hx
        simp only [g, Finset.card_erase_of_mem (hvalue_mem x hx), hcard x hx.1,
          Nat.add_sub_cancel]
      obtain ⟨b, hb⟩ := ih t g hvalue hg_reg hg_card
      refine ⟨insert value b, hb.mono fun x hx ↦ ⟨hx.1.1, ?_⟩⟩
      calc
        f x = insert value ((f x).erase value) := (Finset.insert_erase (hvalue_mem x hx.1)).symm
        _ = insert value (g x) := rfl
        _ = insert value b := congrArg (insert value) hx.2

/-- The fixed-cardinality restriction can be removed when countable unions of nonstationary
sets are nonstationary. -/
theorem StationaryPressingDown.finset
    {V : Type u} [LinearOrder V] [OrderBot V] [WellFoundedLT V]
    (hpress : StationaryPressingDown V) (hcof : Order.cof V ≠ ℵ₀)
    (s : Set V) (f : V → Finset V) (hs : IsStationary s)
    (hreg : ∀ x ∈ s, ∀ y ∈ f x, y < x) :
    ∃ b : Finset V, IsStationary {x | x ∈ s ∧ f x = b} := by
  let pieces : ℕ → Set V := fun n ↦ {x | x ∈ s ∧ (f x).card = n}
  have hunion : (⋃ n, pieces n) = s := by
    ext x
    simp only [pieces, Set.mem_iUnion]
    exact ⟨fun ⟨_, hx, _⟩ ↦ hx, fun hx ↦ ⟨(f x).card, hx, rfl⟩⟩
  have hstationary : IsStationary (⋃ n, pieces n) := by simpa [hunion] using hs
  obtain ⟨n, hn⟩ := (isStationary_iUnion_iff_of_countable hcof).mp hstationary
  obtain ⟨b, hb⟩ := hpress.finset_of_card n (pieces n) f hn
    (fun x hx ↦ hreg x hx.1) (fun x hx ↦ hx.2)
  exact ⟨b, hb.mono fun x hx ↦ ⟨hx.1.1, hx.2⟩⟩

/-- The diagonal intersection of a family of sets: `x` belongs when it belongs to every
set indexed strictly below `x`. -/
def diagonalInter {V : Type u} [LT V] (C : V → Set V) : Set V :=
  {x | ∀ y, y < x → x ∈ C y}

/-- Diagonal intersections of clubs in an uncountable regular initial ordinal are club.
This is the missing closure fact behind the pressing-down lemma. -/
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
    dsimp [V]
    rw [Ordinal.cof_toType, hk.cof_ord]
    exact huncountable.ne'
  have hsmall (x : V) : #(Set.Iic x) < k := by
    simpa [V] using Cardinal.mk_Iic_lt x (by simp [V]) (by simpa [V] using hk.aleph0_le)
  have hclubs (x : V) : IsClub (⋂ a : Set.Iic x, C a.1) := by
    apply IsClub.iInter hcof
    · simpa [V, Ordinal.cof_toType, hk.cof_ord] using hsmall x
    · exact fun a ↦ hC a.1
  let next (x : V) : V := Classical.choose ((hclubs x).isCofinal x)
  have next_mem (x : V) : next x ∈ ⋂ a : Set.Iic x, C a.1 :=
    (Classical.choose_spec ((hclubs x).isCofinal x)).1
  have le_next (x : V) : x ≤ next x :=
    (Classical.choose_spec ((hclubs x).isCofinal x)).2
  refine ⟨?_, fun start ↦ ?_⟩
  · intro d hd hdn _ top htop a ha
    have hex : ∃ x ∈ d, a < x := by
      by_contra h
      push Not at h
      exact (not_lt_of_ge (htop.2 fun x hx ↦ h x hx)) ha
    obtain ⟨x, hxd, hax⟩ := hex
    let tail : Set V := d ∩ Set.Ioi a
    have htail_nonempty : tail.Nonempty := ⟨x, hxd, hax⟩
    have htail_subset : tail ⊆ C a := by
      intro y hy
      exact hd hy.1 a hy.2
    have htail_lub : IsLUB tail top := by
      refine ⟨fun y hy ↦ htop.1 hy.1, fun b hb ↦ htop.2 fun y hy ↦ ?_⟩
      by_cases hay : a < y
      · exact hb ⟨hy, hay⟩
      · exact (le_of_not_gt hay).trans (hax.le.trans (hb ⟨hxd, hax⟩))
    exact (hC a).isLUB_mem htail_subset htail_nonempty htail_lub
  · let seq : ℕ → V := fun n ↦ next^[n] start
    have seq_zero : seq 0 = start := by simp [seq]
    have seq_succ (n : ℕ) : seq (n + 1) = next (seq n) := by
      simp [seq, Function.iterate_succ_apply']
    have seq_mono : Monotone seq := by
      apply monotone_nat_of_le_succ
      intro n
      rw [seq_succ]
      exact le_next _
    have seq_not_cofinal : ¬ IsCofinal (Set.range seq) := by
      intro hseq
      have hle : k ≤ #(Set.range seq) := by
        simpa [V, Ordinal.cof_toType, hk.cof_ord] using Order.cof_le hseq
      have hrange : #(Set.range seq) ≤ ℵ₀ := by
        simpa using Cardinal.mk_range_le_lift (f := seq)
      exact (not_le_of_gt huncountable) (hle.trans hrange)
    have seq_bdd : BddAbove (Set.range seq) := .of_not_isCofinal seq_not_cofinal
    let limit : V := sSup (Set.range seq)
    have limit_lub : IsLUB (Set.range seq) limit :=
      isLUB_csSup (Set.range_nonempty seq) seq_bdd
    refine ⟨limit, ?_, ?_⟩
    · intro a ha
      have hex : ∃ n, a < seq n := by
        by_contra h
        push Not at h
        exact (not_lt_of_ge
          (limit_lub.2 fun x hx ↦ by obtain ⟨n, rfl⟩ := hx; exact h n)) ha
      obtain ⟨n, han⟩ := hex
      let tail : Set V := Set.range fun m ↦ seq (n + 1 + m)
      have tail_subset : tail ⊆ C a := by
        intro x hx
        obtain ⟨m, rfl⟩ := hx
        change seq (n + 1 + m) ∈ C a
        rw [show n + 1 + m = (n + m) + 1 by omega, seq_succ]
        exact Set.mem_iInter.mp (next_mem (seq (n + m)))
          ⟨a, han.le.trans (seq_mono (Nat.le_add_right n m))⟩
      have tail_lub : IsLUB tail limit := by
        refine ⟨fun x hx ↦ limit_lub.1 (by obtain ⟨m, rfl⟩ := hx; exact ⟨_, rfl⟩),
          fun b hb ↦ limit_lub.2 fun x hx ↦ ?_⟩
        obtain ⟨j, rfl⟩ := hx
        exact (seq_mono (show j ≤ n + 1 + j by omega)).trans (hb ⟨j, rfl⟩)
      exact (hC a).isLUB_mem tail_subset (Set.range_nonempty _) tail_lub
    · rw [← seq_zero]
      exact limit_lub.1 ⟨0, rfl⟩

/-- Fodor's pressing-down lemma for every uncountable regular initial ordinal. -/
theorem stationaryPressingDown_ord
    (k : Cardinal.{u}) (hk : k.IsRegular) (huncountable : ℵ₀ < k) :
    StationaryPressingDown k.ord.ToType := by
  intro s f hs hreg
  by_contra hconstant
  push Not at hconstant
  have hnonstationary (value : k.ord.ToType) :
      ¬ IsStationary {x | x ∈ s ∧ f x = value} := hconstant value
  choose C hC hdisjoint using fun value ↦
    not_isStationary_iff.mp (hnonstationary value)
  have hdiag : IsClub (diagonalInter C) :=
    isClub_diagonalInter_ord k hk huncountable C hC
  obtain ⟨x, hxs, hxdiag⟩ := hs hdiag
  have hfx : f x < x := hreg x hxs
  have hxC : x ∈ C (f x) := hxdiag (f x) hfx
  have hxfiber : x ∈ {y | y ∈ s ∧ f y = f x} := ⟨hxs, rfl⟩
  exact Set.disjoint_left.mp (hdisjoint (f x)) hxfiber hxC

/-- A point is an `ω`-supremum when it is the least upper bound of a strictly increasing
sequence.  This formulation records exactly the local data used by the finite-barrier
construction, without making an arbitrary choice of a cofinality witness globally. -/
def IsOmegaSup {V : Type u} [LinearOrder V] (top : V) : Prop :=
  ∃ seq : ℕ → V, StrictMono seq ∧ IsLUB (Set.range seq) top

/-- The `ω`-suprema form a stationary subset of every uncountable regular initial ordinal. -/
theorem isStationary_isOmegaSup_ord
    (k : Cardinal.{u}) (hk : k.IsRegular) (huncountable : ℵ₀ < k) :
    IsStationary {top : k.ord.ToType | IsOmegaSup top} := by
  classical
  let V := k.ord.ToType
  let _ : Nonempty V := Cardinal.nonempty_ord_toType hk.ne_zero
  let _ : OrderBot V := WellFoundedLT.toOrderBot V
  let _ : ConditionallyCompleteLinearOrderBot V :=
    WellFoundedLT.conditionallyCompleteLinearOrderBot V
  let _ : NoMaxOrder V := Cardinal.noMaxOrder hk.aleph0_le
  intro C hC
  let above (x : V) : V := Classical.choose (exists_gt x)
  have lt_above (x : V) : x < above x := Classical.choose_spec (exists_gt x)
  let next (x : V) : V := Classical.choose (hC.isCofinal (above x))
  have next_mem (x : V) : next x ∈ C :=
    (Classical.choose_spec (hC.isCofinal (above x))).1
  have lt_next (x : V) : x < next x :=
    (lt_above x).trans_le (Classical.choose_spec (hC.isCofinal (above x))).2
  let seq : ℕ → V := fun n ↦ next^[n + 1] ⊥
  have seq_succ (n : ℕ) : seq (n + 1) = next (seq n) := by
    simp only [seq, Function.iterate_succ_apply']
  have seq_mem (n : ℕ) : seq n ∈ C := by
    cases n with
    | zero => exact next_mem ⊥
    | succ n => rw [seq_succ]; exact next_mem _
  have seq_strict : StrictMono seq :=
    strictMono_nat_of_lt_succ fun n ↦ by rw [seq_succ]; exact lt_next _
  have seq_not_cofinal : ¬ IsCofinal (Set.range seq) := by
    intro hseq
    have hle : k ≤ #(Set.range seq) := by
      simpa [V, Ordinal.cof_toType, hk.cof_ord] using Order.cof_le hseq
    have hrange : #(Set.range seq) ≤ ℵ₀ := by
      simpa using Cardinal.mk_range_le_lift (f := seq)
    exact (not_le_of_gt huncountable) (hle.trans hrange)
  have seq_bdd : BddAbove (Set.range seq) := .of_not_isCofinal seq_not_cofinal
  let limit : V := sSup (Set.range seq)
  have limit_lub : IsLUB (Set.range seq) limit :=
    isLUB_csSup (Set.range_nonempty seq) seq_bdd
  have limit_mem : limit ∈ C :=
    hC.isLUB_mem (fun x hx ↦ by obtain ⟨n, rfl⟩ := hx; exact seq_mem n)
      (Set.range_nonempty seq) limit_lub
  exact ⟨limit, ⟨seq, seq_strict, limit_lub⟩, limit_mem⟩

end Set

namespace SimpleGraph

variable {V : Type u} [LinearOrder V]

/-- A strictly increasing blue sequence lying below one further blue vertex contains a blue
copy of `ω+1`. -/
theorem exists_clique_type_omega_add_one_of_strictMono
    [WellFoundedLT V] (blue : SimpleGraph V) (seq : ℕ → V) (top : V)
    (hseq : StrictMono seq) (hbelow : ∀ n, seq n < top)
    (hclique : blue.IsClique (Set.range seq ∪ {top})) :
    ∃ B : Set V, blue.IsClique B ∧ typeLT B = ω + 1 := by
  classical
  let A : Set V := Set.range seq ∪ {top}
  let sourceRel : Sum (ULift.{u} ℕ) (ULift.{u} Unit) →
      Sum (ULift.{u} ℕ) (ULift.{u} Unit) → Prop :=
    Sum.Lex (· < ·) (· < ·)
  let embed : Sum (ULift.{u} ℕ) (ULift.{u} Unit) → A
    | Sum.inl n => ⟨seq n.down, Or.inl ⟨n.down, rfl⟩⟩
    | Sum.inr _ => ⟨top, Or.inr rfl⟩
  have embed_mono : ∀ a b, sourceRel a b → embed a < embed b := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · simp [sourceRel] at hab
      exact hseq hab
    · exact hbelow _
    · simp [sourceRel] at hab
    · simp only [sourceRel, Sum.lex_inr_inr] at hab
      have hab_eq : a = b := Subsingleton.elim _ _
      subst b
      exact (lt_irrefl _ hab).elim
  let emb : sourceRel ↪r ((· < ·) : A → A → Prop) :=
    RelEmbedding.ofMonotone embed embed_mono
  have hsource : Ordinal.type sourceRel = ω + 1 := by
    change Ordinal.type
      (Sum.Lex ((· < ·) : ULift.{u} ℕ → ULift.{u} ℕ → Prop)
        ((· < ·) : ULift.{u} Unit → ULift.{u} Unit → Prop)) = ω + 1
    rw [Ordinal.type_sum_lex, Ordinal.type_lt_ulift, Ordinal.type_nat_lt,
      Ordinal.lift_omega0]
    have hunit : typeLT (ULift.{u} Unit) = 1 :=
      Ordinal.type_eq_one_iff_unique.2 ⟨inferInstance⟩
    rw [hunit]
  have hle : ω + 1 ≤ typeLT A := by
    rw [← hsource]
    exact emb.ordinal_type_le
  obtain ⟨B, hBA, hBtype⟩ := Ordinal.exists_subset_typeLT_eq A hle
  exact ⟨B, hclique.subset hBA, hBtype⟩

/-- Vertices which minimally extend a finite blue seed above a cutoff. -/
def barrierCore (blue : SimpleGraph V) (b : Finset V) (cutoff : V) : Set V :=
  {top | cutoff < top ∧ blue.IsClique ((b : Set V) ∪ {top}) ∧
    ∀ middle, cutoff < middle → middle < top →
      ¬ blue.IsClique ((b : Set V) ∪ {middle, top})}

theorem mem_barrierCore_iff {blue : SimpleGraph V} {b : Finset V} {cutoff top : V} :
    top ∈ barrierCore blue b cutoff ↔
      cutoff < top ∧ blue.IsClique ((b : Set V) ∪ {top}) ∧
        ∀ middle, cutoff < middle → middle < top →
          ¬ blue.IsClique ((b : Set V) ∪ {middle, top}) :=
  Iff.rfl

/-- Failure of the barrier condition, when its two positive clauses hold, supplies a new
intermediate vertex extending the finite blue seed. -/
theorem exists_between_clique_of_not_mem_barrierCore
    {blue : SimpleGraph V} {b : Finset V} {cutoff top : V}
    (hcutoff : cutoff < top) (hclique : blue.IsClique ((b : Set V) ∪ {top}))
    (hnot : top ∉ barrierCore blue b cutoff) :
    ∃ middle, cutoff < middle ∧ middle < top ∧
      blue.IsClique (((insert middle b : Finset V) : Set V) ∪ {top}) := by
  rw [mem_barrierCore_iff, not_and_or, not_and_or] at hnot
  rcases hnot with h | h | h
  · exact (h hcutoff).elim
  · exact (h hclique).elim
  · push Not at h
    obtain ⟨middle, hcutoff_middle, hmiddle_top, hmiddle⟩ := h
    refine ⟨middle, hcutoff_middle, hmiddle_top, ?_⟩
    simpa only [Finset.coe_insert, Set.union_insert, Set.insert_union] using hmiddle

private structure BarrierBuildState (blue : SimpleGraph V) (top : V) where
  seed : Finset V
  last : V
  last_mem : last ∈ seed
  seed_lt : ∀ y ∈ seed, y < top
  isClique : blue.IsClique ((seed : Set V) ∪ {top})

/-- If a non-minimal vertex is not the top of a blue `ω+1`, then some finite seed and
cutoff put it in a barrier core.  The contrapositive recursively extends finite seeds and
thereby constructs a strictly increasing blue `ω`-sequence below the fixed top. -/
theorem exists_barrierCore_at_of_no_clique_type_omega_add_one
    [OrderBot V] [WellFoundedLT V] (blue : SimpleGraph V) (top : V) (hbot : ⊥ < top)
    (hno : ¬ ∃ B : Set V, blue.IsClique B ∧ typeLT B = ω + 1) :
    ∃ (b : Finset V) (cutoff : V),
      (∀ y ∈ b, y < top) ∧ top ∈ barrierCore blue b cutoff := by
  classical
  by_contra hresult
  have no_barrier (b : Finset V) (cutoff : V) (hseed : ∀ y ∈ b, y < top) :
      top ∉ barrierCore blue b cutoff := by
    intro hmem
    exact hresult ⟨b, cutoff, hseed, hmem⟩
  have empty_clique : blue.IsClique ((((∅ : Finset V) : Set V)) ∪ {top}) := by simp
  obtain ⟨first, hbot_first, hfirst_top, hfirst_clique⟩ :=
    exists_between_clique_of_not_mem_barrierCore hbot empty_clique
      (no_barrier ∅ ⊥ (by simp))
  let initial : BarrierBuildState blue top :=
    { seed := {first}
      last := first
      last_mem := by simp
      seed_lt := by simpa using hfirst_top
      isClique := by simpa using hfirst_clique }
  have extend (s : BarrierBuildState blue top) :
      ∃ middle, s.last < middle ∧ middle < top ∧
        blue.IsClique ((((insert middle s.seed : Finset V) : Set V)) ∪ {top}) :=
    exists_between_clique_of_not_mem_barrierCore
      (s.seed_lt s.last s.last_mem) s.isClique (no_barrier s.seed s.last s.seed_lt)
  let nextVertex (s : BarrierBuildState blue top) : V := Classical.choose (extend s)
  have nextVertex_spec (s : BarrierBuildState blue top) :
      s.last < nextVertex s ∧ nextVertex s < top ∧
        blue.IsClique ((((insert (nextVertex s) s.seed : Finset V) : Set V)) ∪ {top}) :=
    Classical.choose_spec (extend s)
  let step (s : BarrierBuildState blue top) : BarrierBuildState blue top :=
    { seed := insert (nextVertex s) s.seed
      last := nextVertex s
      last_mem := Finset.mem_insert_self _ _
      seed_lt := by
        intro y hy
        rw [Finset.mem_insert] at hy
        exact hy.elim (fun h ↦ h ▸ (nextVertex_spec s).2.1) (s.seed_lt y)
      isClique := (nextVertex_spec s).2.2 }
  have step_last (s : BarrierBuildState blue top) : (step s).last = nextVertex s := rfl
  have step_seed (s : BarrierBuildState blue top) :
      (step s).seed = insert (nextVertex s) s.seed := rfl
  let states : ℕ → BarrierBuildState blue top := fun n ↦ step^[n] initial
  have states_succ (n : ℕ) : states (n + 1) = step (states n) := by
    simp only [states, Function.iterate_succ_apply']
  let vertex : ℕ → V := fun n ↦ (states n).last
  let seeds : ℕ → Finset V := fun n ↦ (states n).seed
  have vertex_lt_succ (n : ℕ) : vertex n < vertex (n + 1) := by
    change (states n).last < (states (n + 1)).last
    rw [states_succ]
    exact (nextVertex_spec (states n)).1
  have vertex_strict : StrictMono vertex := strictMono_nat_of_lt_succ vertex_lt_succ
  have vertex_below (n : ℕ) : vertex n < top :=
    (states n).seed_lt _ (states n).last_mem
  have seeds_le_succ (n : ℕ) : seeds n ⊆ seeds (n + 1) := by
    change (states n).seed ⊆ (states (n + 1)).seed
    rw [states_succ, step_seed]
    exact Finset.subset_insert _ _
  have seeds_mono : Monotone seeds := monotone_nat_of_le_succ seeds_le_succ
  have vertex_mem_seed (n : ℕ) : vertex n ∈ seeds n := (states n).last_mem
  have vertex_mem_seed_of_le {i j : ℕ} (hij : i ≤ j) : vertex i ∈ seeds j :=
    seeds_mono hij (vertex_mem_seed i)
  have range_top_clique : blue.IsClique (Set.range vertex ∪ {top}) := by
    intro x hx y hy hxy
    simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff] at hx hy
    rcases hx with ⟨i, rfl⟩ | rfl <;> rcases hy with ⟨j, rfl⟩ | rfl
    · have hij : i ≠ j := fun h ↦ hxy (congrArg vertex h)
      rcases lt_or_gt_of_ne hij with hij | hji
      · exact (states j).isClique (Or.inl (vertex_mem_seed_of_le hij.le))
          (Or.inl (vertex_mem_seed j)) hxy
      · exact ((states i).isClique (Or.inl (vertex_mem_seed_of_le hji.le))
          (Or.inl (vertex_mem_seed i)) hxy.symm).symm
    · exact (states i).isClique (Or.inl (vertex_mem_seed i)) (Or.inr rfl) hxy
    · exact (states j).isClique (Or.inr rfl) (Or.inl (vertex_mem_seed j)) hxy
    · exact (hxy rfl).elim
  exact hno (exists_clique_type_omega_add_one_of_strictMono
    blue vertex top vertex_strict vertex_below range_top_clique)

/-- Two distinct elements of a barrier core cannot be joined by a blue edge. -/
theorem not_adj_of_mem_barrierCore {blue : SimpleGraph V} {b : Finset V} {cutoff x y : V}
    (hx : x ∈ barrierCore blue b cutoff) (hy : y ∈ barrierCore blue b cutoff)
    (hxy : x ≠ y) : ¬ blue.Adj x y := by
  wlog hlt : x < y generalizing x y
  · exact fun hblue ↦ this hy hx hxy.symm (lt_of_le_of_ne (le_of_not_gt hlt) hxy.symm) hblue.symm
  intro hblue
  apply hy.2.2 x hx.1 hlt
  rw [show (b : Set V) ∪ {x, y} = insert x ((b : Set V) ∪ {y}) by ext; simp]
  apply hy.2.1.insert
  intro q hq hxq
  rcases hq with hqb | rfl
  · exact hx.2.1 (Or.inr rfl) (Or.inl hqb) hxq
  · exact hblue

/-- Every finite-seed barrier core is homogeneous in the complementary color. -/
theorem compl_isClique_barrierCore (blue : SimpleGraph V) (b : Finset V) (cutoff : V) :
    blueᶜ.IsClique (barrierCore blue b cutoff) := by
  intro x hx y hy hxy
  rw [SimpleGraph.compl_adj]
  exact ⟨hxy, not_adj_of_mem_barrierCore hx hy hxy⟩

/-- Regressive choices of a cutoff and a finite seed can be made constant on a stationary
set; that stationary set is then contained in one barrier core. -/
theorem exists_stationary_barrierCore_of_regressive_data
    [OrderBot V] [WellFoundedLT V]
    (hpress : StationaryPressingDown V) (hcof : Order.cof V ≠ ℵ₀)
    (blue : SimpleGraph V) (s : Set V) (seed : V → Finset V) (cutoff : V → V)
    (hs : IsStationary s)
    (hcutoff : ∀ x ∈ s, cutoff x < x)
    (hseed : ∀ x ∈ s, ∀ y ∈ seed x, y < x)
    (hbarrier : ∀ x ∈ s, x ∈ barrierCore blue (seed x) (cutoff x)) :
    ∃ (b : Finset V) (value : V), IsStationary (barrierCore blue b value) := by
  obtain ⟨value, hvalue⟩ := hpress s cutoff hs hcutoff
  let t : Set V := {x | x ∈ s ∧ cutoff x = value}
  obtain ⟨b, hb⟩ := hpress.finset hcof t seed hvalue
    (fun x hx ↦ hseed x hx.1)
  refine ⟨b, value, hb.mono fun x hx ↦ ?_⟩
  have h := hbarrier x hx.1.1
  simpa only [hx.1.2, hx.2] using h

end SimpleGraph

namespace Ordinal

/-- Local finite-barrier data on a stationary set.  Direct finite-seed extension constructs
this data at every non-minimal point when there is no blue `ω+1`. -/
def LocalFiniteBarrierData (k : Cardinal.{u}) (blue : SimpleGraph k.ord.ToType) : Prop :=
  ∃ (s : Set k.ord.ToType) (seed : k.ord.ToType → Finset k.ord.ToType)
      (cutoff : k.ord.ToType → k.ord.ToType),
    IsStationary s ∧
      (∀ x ∈ s, cutoff x < x) ∧
      (∀ x ∈ s, ∀ y ∈ seed x, y < x) ∧
      ∀ x ∈ s, x ∈ SimpleGraph.barrierCore blue (seed x) (cutoff x)

/-- Absence of a blue `ω+1` gives local finite-barrier data on the stationary final segment
above the least element. -/
theorem localFiniteBarrierData_of_no_clique_type_omega_add_one
    (k : Cardinal.{u}) (hinfinite : ℵ₀ ≤ k) (blue : SimpleGraph k.ord.ToType)
    (hno : ¬ ∃ B : Set k.ord.ToType, blue.IsClique B ∧ typeLT B = ω + 1) :
    LocalFiniteBarrierData k blue := by
  classical
  let V := k.ord.ToType
  let _ : Nonempty V :=
    Cardinal.nonempty_ord_toType (Cardinal.aleph0_pos.trans_le hinfinite).ne'
  let _ : OrderBot V := WellFoundedLT.toOrderBot V
  let _ : NoMaxOrder V := Cardinal.noMaxOrder hinfinite
  let s : Set V := Set.Ioi ⊥
  have hs : IsStationary s := by
    intro C hC
    obtain ⟨above, hbot_above⟩ := exists_gt (⊥ : V)
    obtain ⟨x, hxC, habove_x⟩ := hC.isCofinal above
    exact ⟨x, hbot_above.trans_le habove_x, hxC⟩
  choose seed cutoff hseed hbarrier using fun x : s ↦
    SimpleGraph.exists_barrierCore_at_of_no_clique_type_omega_add_one
      blue x.1 x.2 hno
  let seedAll (x : V) : Finset V := if hx : x ∈ s then seed ⟨x, hx⟩ else ∅
  let cutoffAll (x : V) : V := if hx : x ∈ s then cutoff ⟨x, hx⟩ else ⊥
  refine ⟨s, seedAll, cutoffAll, hs, ?_, ?_, ?_⟩
  · intro x hx
    simpa only [cutoffAll, dif_pos hx] using (hbarrier ⟨x, hx⟩).1
  · intro x hx y hy
    have hy' : y ∈ seed ⟨x, hx⟩ := by simpa only [seedAll, dif_pos hx] using hy
    exact hseed ⟨x, hx⟩ y hy'
  · intro x hx
    simpa only [seedAll, cutoffAll, dif_pos hx] using hbarrier ⟨x, hx⟩

/-- The exact reflection principle needed by the finite-seed proof of
`κ → (κ, ω+1)²`: if a coloring has no blue copy of `ω+1`, one of its finite
barrier cores has full cardinality. -/
def FiniteBarrierReflection (k : Cardinal.{u}) : Prop :=
  ∀ blue : SimpleGraph k.ord.ToType,
    (¬ ∃ B : Set k.ord.ToType, blue.IsClique B ∧ typeLT B = ω + 1) →
      ∃ (b : Finset k.ord.ToType) (cutoff : k.ord.ToType),
        #(SimpleGraph.barrierCore blue b cutoff) = k

/-- On an initial ordinal, stationarity already implies full cardinality. -/
theorem mk_eq_of_isStationary_on_ord (k : Cardinal.{u}) (hk : k.IsRegular)
    {s : Set k.ord.ToType} (hs : IsStationary s) : #s = k := by
  let _ : IsRegularCardinalOrder k.ord.ToType := ⟨by
    rw [type_toType, Ordinal.cof_toType, hk.cof_ord]⟩
  have htype : typeLT s = k.ord := by
    simpa using Order.type_eq_of_isCofinal hs.isCofinal
  rw [← Ordinal.card_type ((· < ·) : s → s → Prop), htype, Cardinal.card_ord]

/-- A stationary finite barrier core supplies the cardinal reflection hypothesis. -/
theorem finiteBarrierReflection_of_stationary
    (k : Cardinal.{u}) (hk : k.IsRegular)
    (hstationary : ∀ blue : SimpleGraph k.ord.ToType,
      (¬ ∃ B : Set k.ord.ToType, blue.IsClique B ∧ typeLT B = ω + 1) →
        ∃ (b : Finset k.ord.ToType) (cutoff : k.ord.ToType),
          IsStationary (SimpleGraph.barrierCore blue b cutoff)) :
    FiniteBarrierReflection k := by
  intro blue hblue
  obtain ⟨b, cutoff, hstat⟩ := hstationary blue hblue
  exact ⟨b, cutoff, mk_eq_of_isStationary_on_ord k hk hstat⟩

/-- Pressing down turns local barrier data into the finite-barrier reflection principle. -/
theorem finiteBarrierReflection_of_pressingDown_of_localData
    (k : Cardinal.{u}) (hk : k.IsRegular) (huncountable : ℵ₀ < k)
    (hpress : StationaryPressingDown k.ord.ToType)
    (hlocal : ∀ blue : SimpleGraph k.ord.ToType,
      (¬ ∃ B : Set k.ord.ToType, blue.IsClique B ∧ typeLT B = ω + 1) →
        LocalFiniteBarrierData k blue) :
    FiniteBarrierReflection k := by
  apply finiteBarrierReflection_of_stationary k hk
  intro blue hblue
  obtain ⟨s, seed, cutoff, hs, hcutoff, hseed, hbarrier⟩ := hlocal blue hblue
  have hcof : Order.cof k.ord.ToType ≠ ℵ₀ := by
    rw [Ordinal.cof_toType, hk.cof_ord]
    exact huncountable.ne'
  let _ : Nonempty k.ord.ToType := Cardinal.nonempty_ord_toType hk.ne_zero
  let _ : OrderBot k.ord.ToType := WellFoundedLT.toOrderBot k.ord.ToType
  exact SimpleGraph.exists_stationary_barrierCore_of_regressive_data
    hpress hcof blue s seed cutoff hs hcutoff hseed hbarrier

/-- Every uncountable regular cardinal satisfies the finite-barrier reflection principle. -/
theorem finiteBarrierReflection_of_isRegular
    (k : Cardinal.{u}) (hk : k.IsRegular) (huncountable : ℵ₀ < k) :
    FiniteBarrierReflection k :=
  finiteBarrierReflection_of_pressingDown_of_localData k hk huncountable
    (Set.stationaryPressingDown_ord k hk huncountable)
    (fun blue hno ↦
      localFiniteBarrierData_of_no_clique_type_omega_add_one k hk.aleph0_le blue hno)

/-- A full-sized barrier core has exactly the initial order type. -/
theorem exists_compl_clique_type_ord_of_barrierCore_mk_eq
    (k : Cardinal.{u}) (blue : SimpleGraph k.ord.ToType)
    (b : Finset k.ord.ToType) (cutoff : k.ord.ToType)
    (hcard : #(SimpleGraph.barrierCore blue b cutoff) = k) :
    ∃ A : Set k.ord.ToType, blueᶜ.IsClique A ∧ typeLT A = k.ord := by
  let A := SimpleGraph.barrierCore blue b cutoff
  refine ⟨A, SimpleGraph.compl_isClique_barrierCore blue b cutoff, le_antisymm ?_ ?_⟩
  · simpa using Ordinal.type_set_le A
  · simpa only [A, hcard] using
      (Cardinal.ord_le_type ((· < ·) : A → A → Prop))

/-- The finite-barrier reflection principle implies the regular-cardinal
Erdős--Rado target `k.ord → (k.ord, ω+1)²`. -/
theorem ordinalRamsey_ord_ord_omega_add_one_of_finiteBarrierReflection
    (k : Cardinal.{u}) (hreflect : FiniteBarrierReflection k) :
    OrdinalRamsey k.ord k.ord (ω + 1) := by
  classical
  intro red blue hcompl
  by_cases hblue : ∃ B : Set k.ord.ToType, blue.IsClique B ∧ typeLT B = ω + 1
  · exact Or.inr hblue
  · obtain ⟨b, cutoff, hcard⟩ := hreflect blue hblue
    obtain ⟨A, hA, hAtype⟩ :=
      exists_compl_clique_type_ord_of_barrierCore_mk_eq k blue b cutoff hcard
    rw [hcompl.symm.compl_eq] at hA
    exact Or.inl ⟨A, hA, hAtype⟩

/-- A fully packaged reduction of the regular-cardinal `ω+1` theorem to pressing down and
the local finite-barrier construction. -/
theorem ordinalRamsey_ord_ord_omega_add_one_of_pressingDown_of_localData
    (k : Cardinal.{u}) (hk : k.IsRegular) (huncountable : ℵ₀ < k)
    (hpress : StationaryPressingDown k.ord.ToType)
    (hlocal : ∀ blue : SimpleGraph k.ord.ToType,
      (¬ ∃ B : Set k.ord.ToType, blue.IsClique B ∧ typeLT B = ω + 1) →
        LocalFiniteBarrierData k blue) :
    OrdinalRamsey k.ord k.ord (ω + 1) :=
  ordinalRamsey_ord_ord_omega_add_one_of_finiteBarrierReflection k
    (finiteBarrierReflection_of_pressingDown_of_localData
      k hk huncountable hpress hlocal)

/-- **Erdős--Rado's sharpening of Dushnik--Miller.**

Every uncountable regular initial ordinal satisfies `k.ord → (k.ord, ω+1)²`. -/
theorem ordinalRamsey_ord_ord_omega_add_one_of_isRegular
    (k : Cardinal.{u}) (hk : k.IsRegular) (huncountable : ℵ₀ < k) :
    OrdinalRamsey k.ord k.ord (ω + 1) :=
  ordinalRamsey_ord_ord_omega_add_one_of_finiteBarrierReflection k
    (finiteBarrierReflection_of_isRegular k hk huncountable)

/-- The `ω₂` instance used as a countable-target weakening of Erdős Problem 1172. -/
theorem ordinalRamsey_omega_two_omega_two_omega_add_one :
    OrdinalRamsey (ω_ 2) (ω_ 2) (ω + 1) := by
  have htwo : (1 : Ordinal) + 1 = 2 := by
    simpa using (Nat.cast_succ 1).symm
  rw [← htwo]
  simpa only [Cardinal.ord_aleph] using
    ordinalRamsey_ord_ord_omega_add_one_of_isRegular
    (ℵ_ ((1 : Ordinal) + 1)) (Cardinal.isRegular_aleph_add_one 1)
    (Cardinal.aleph0_lt_aleph.2 (by simp))

/-- The `ω₃` instance used as a countable-target weakening of Erdős Problem 1172. -/
theorem ordinalRamsey_omega_three_omega_three_omega_add_one :
    OrdinalRamsey (ω_ 3) (ω_ 3) (ω + 1) := by
  have hthree : (2 : Ordinal) + 1 = 3 := by
    simpa using (Nat.cast_succ 2).symm
  rw [← hthree]
  simpa only [Cardinal.ord_aleph] using
    ordinalRamsey_ord_ord_omega_add_one_of_isRegular
    (ℵ_ ((2 : Ordinal) + 1)) (Cardinal.isRegular_aleph_add_one 2)
    (Cardinal.aleph0_lt_aleph.2 (by simp))

end Ordinal
