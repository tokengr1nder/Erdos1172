/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3HechlerStationaryProfile

@[expose] public section

/-!
# A square block joined to stationary future decisions

Row bounds for the blue losses in an ordered red square give an actual
clique-decision system with a stationary future. The common block is
represented by decisions in the concrete countably closed Hechler order;
it is not asserted to be one ground block with a ground stationary future.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3StationarySquareDecisions

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3HechlerOrder
open Erdos1172Part3HechlerStationaryProfile
open Erdos1172Part3StationaryDecisions
open Erdos1172Part3ClosedDecisionSystem (CliqueDecisions)

theorem exists_strict_tail (bound : W1) :
    ∃ f : W1 → W1, StrictMono f ∧ ∀ i, bound < f i := by
  let _ : IsRegularCardinalOrder W1 := ⟨by
    rw [cof_W1, Cardinal.ord_aleph]
    simp only [W1, Ordinal.type_toType, le_refl]⟩
  have hcof : ℵ₀ < Order.cof W1 := by
    rw [cof_W1]
    exact Cardinal.aleph0_lt_aleph.mpr (by norm_num)
  let e := Order.enum (Set.Ioi bound)
    (Set.isClub_Ioi_of_aleph0_lt_cof hcof bound).isCofinal
  exact ⟨fun i => (e i).val, (Subtype.strictMono_coe _).comp e.strictMono,
    fun i => (e i).property⟩

noncomputable def tail (bound : W1) : W1 → W1 := (exists_strict_tail bound).choose

theorem tail_strict (bound : W1) : StrictMono (tail bound) :=
  (exists_strict_tail bound).choose_spec.1

theorem lt_tail (bound i : W1) : bound < tail bound i :=
  (exists_strict_tail bound).choose_spec.2 i

abbrev Square : Type := W1 ×ₗ W1

/-- The whole square and its future use compatible decisions. The
stationarity field is quantified over every stronger condition. -/
structure StationarySquareDecisions (G : SimpleGraph W2) (S : Set W2) where
  start : Condition
  clique : CliqueDecisions Condition Square W2 G
  future : Condition → W2 → Prop
  persistent : Persistent future
  subset_source : ∀ p a, future p a → a ∈ S
  stationary : StationaryAt future start
  cross : ∀ p a, future p a → ∀ i x, clique.decides p i x → x < a ∧ G.Adj x a

/-- Past one fixed row cutoff, each blue column has a bounded set of
positions in every row. These bounds, not a domination principle, are
the remaining geometric premises of this constructor. -/
theorem exists_stationary_square_decisions_of_row_bounds (hCH : CH) (p0 : Condition)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (core : Square → W2) (hcore : StrictMono core) (hred : G.IsClique (Set.range core))
    (S : Set W2) (hS : IsStationary S) (hafter : ∀ a ∈ S, ∀ z : Square, core z < a)
    (cutoff : W1) (F : W2 → W1 → W1)
    (hloss : ∀ a ∈ S, ∀ i : W1, cutoff < i → ∀ j : W1,
      H.Adj (core (toLex (i, j))) a → j < F a i) :
    ∃ sys : StationarySquareDecisions G S, sys.start ≤ p0 ∧
      ∀ q i x, sys.clique.decides q i x → x ∈ Set.range core := by
  classical
  obtain ⟨bound, p, hpp0, hp⟩ := exists_stationary_uniform_tail hCH p0 S hS F
  let row : W1 → W1 := tail (max cutoff bound)
  let decides (q : Condition) (i : Square) (x : W2) : Prop :=
    ∃ v : W1, q.stem (row (ofLex i).1) = some v ∧
      x = core (toLex (row (ofLex i).1, tail v (ofLex i).2))
  have hordered {q : Condition} {i j : Square} {x y : W2}
      (hij : i < j) (hx : decides q i x) (hy : decides q j y) : x < y := by
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    apply hcore
    rw [Prod.Lex.lt_iff] at hij ⊢
    rcases hij with hfirst | ⟨hfirst, hsecond⟩
    · exact Or.inl (tail_strict _ hfirst)
    · have heq : v = w := Option.some.inj (by rw [hfirst] at hv; exact hv.symm.trans hw)
      subst w
      exact Or.inr ⟨congrArg row hfirst, tail_strict v hsecond⟩
  let clique : CliqueDecisions Condition Square W2 G := {
    decides := decides
    dense := by
      intro q i
      obtain ⟨r, ⟨v, hv⟩, hrq⟩ := coordinate_dense (row (ofLex i).1) q
      exact ⟨r, hrq, _, v, hv, rfl⟩
    persistent := by
      intro q r i x hrq hx
      obtain ⟨v, hv, heq⟩ := hx
      exact ⟨v, hrq.1 _ _ hv, heq⟩
    unique := by
      intro q i x y hx hy
      obtain ⟨v, hv, rfl⟩ := hx
      obtain ⟨w, hw, rfl⟩ := hy
      have heq : v = w := Option.some.inj (hv.symm.trans hw)
      rw [heq]
    ordered := hordered
    adjacent := by
      intro q i j x y hij hx hy
      have hxy : x ≠ y := by
        rcases lt_or_gt_of_ne hij with hlt | hgt
        · exact (hordered hlt hx hy).ne
        · exact (hordered hgt hy hx).ne.symm
      exact hred ⟨_, hx.choose_spec.2.symm⟩ ⟨_, hy.choose_spec.2.symm⟩ hxy }
  refine ⟨{
    start := p
    clique := clique
    future := TailMembers S F bound
    persistent := tailMembers_persistent S F bound
    subset_source := fun _ _ h => h.1
    stationary := hp
    cross := ?_ }, hpp0, ?_⟩
  · intro q a ha i x hx
    obtain ⟨v, hv, rfl⟩ := hx
    have hrowCut : cutoff < row (ofLex i).1 :=
      (le_max_left cutoff bound).trans_lt (lt_tail _ _)
    have hrowBound : bound < row (ofLex i).1 :=
      (le_max_right cutoff bound).trans_lt (lt_tail _ _)
    have hfa : F a (row (ofLex i).1) < v := ha.2 q le_rfl _ hrowBound v hv
    have hbefore := hafter a ha.1 (toLex (row (ofLex i).1, tail v (ofLex i).2))
    refine ⟨hbefore, ?_⟩
    rw [← hcompl.symm.compl_eq, SimpleGraph.compl_adj]
    refine ⟨hbefore.ne, ?_⟩
    intro hblue
    have hbad := hloss a ha.1 _ hrowCut _ hblue
    exact (hfa.trans (lt_tail v (ofLex i).2)).asymm hbad
  · intro q i x hx
    exact ⟨_, hx.choose_spec.2.symm⟩

end Erdos1172Part3StationarySquareDecisions
