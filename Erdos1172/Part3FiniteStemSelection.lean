/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3FiniteTraceCutoffs
public import Erdos1172.Part3StationaryCubeThinning

@[expose] public section

/-!
# Finite-depth coherent stem selection

One stem chooses a tail at each proper prefix on a finite path.
Coincident earlier coordinates use the same stem entry. This proves
uniqueness and strict lexicographic order at every finite depth.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3FiniteStemSelection

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3FiniteTraceSchemes (Index Prefix root)
open Erdos1172Part3FiniteTraceCutoffs (Clears subBounds)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3IteratedHechlerOrder (Condition liftBase liftBase_le base_le)
open Erdos1172Part3StationarySquareDecisions (tail tail_strict lt_tail)

variable {P : Type} [Preorder P]

def Selected : (n : ℕ) → (Prefix n → W1) → Condition P → Index n → Index n → Prop
  | 0, code, p, z, old => ∃ v : W1, p.stem (code ()) = some v ∧ old = tail v z
  | n + 1, code, p, z, old => ∃ v : W1, p.stem (code (Sum.inl ())) = some v ∧
      (ofLex old).1 = tail v (ofLex z).1 ∧
        Selected n (fun e => code (Sum.inr ((ofLex old).1, e))) p (ofLex z).2 (ofLex old).2

theorem selected_persistent (n : ℕ) (code : Prefix n → W1) {p q : Condition P}
    {z old : Index n} (hqp : q ≤ p) (h : Selected n code p z old) : Selected n code q z old := by
  induction n with
  | zero =>
    obtain ⟨v, hv, heq⟩ := h
    exact ⟨v, hqp.2.1 _ _ hv, heq⟩
  | succ n ih =>
    obtain ⟨v, hv, heq, hinner⟩ := h
    exact ⟨v, hqp.2.1 _ _ hv, heq, ih _ hinner⟩

theorem selected_unique (n : ℕ) (code : Prefix n → W1) (p : Condition P)
    {z old other : Index n} (h : Selected n code p z old) (h' : Selected n code p z other) :
    old = other := by
  induction n with
  | zero =>
    obtain ⟨v, hv, ho⟩ := h
    obtain ⟨w, hw, ho'⟩ := h'
    have heq : v = w := Option.some.inj (hv.symm.trans hw)
    exact ho.trans (by rw [heq, ho'])
  | succ n ih =>
    obtain ⟨v, hv, ho, hi⟩ := h
    obtain ⟨w, hw, ho', hi'⟩ := h'
    have heq : v = w := Option.some.inj (hv.symm.trans hw)
    subst w
    have hfirst : (ofLex old).1 = (ofLex other).1 := ho.trans ho'.symm
    have hsecond : (ofLex old).2 = (ofLex other).2 := by
      apply ih (fun e => code (Sum.inr ((ofLex old).1, e))) hi
      rwa [hfirst]
    exact congrArg toLex (Prod.ext hfirst hsecond)

theorem selected_ordered (n : ℕ) (code : Prefix n → W1) (p : Condition P)
    {z z' old other : Index n} (hzz' : z < z')
    (h : Selected n code p z old) (h' : Selected n code p z' other) : old < other := by
  induction n with
  | zero =>
    obtain ⟨v, hv, ho⟩ := h
    obtain ⟨w, hw, ho'⟩ := h'
    have heq : v = w := Option.some.inj (hv.symm.trans hw)
    subst w
    rw [ho, ho']
    exact tail_strict v hzz'
  | succ n ih =>
    obtain ⟨v, hv, ho, hi⟩ := h
    obtain ⟨w, hw, ho', hi'⟩ := h'
    have heq : v = w := Option.some.inj (hv.symm.trans hw)
    subst w
    change (toLex (ofLex z) : W1 ×ₗ Index n) < toLex (ofLex z') at hzz'
    change (toLex (ofLex old) : W1 ×ₗ Index n) < toLex (ofLex other)
    rw [Prod.Lex.lt_iff] at hzz' ⊢
    change (ofLex z).1 < (ofLex z').1 ∨
      (ofLex z).1 = (ofLex z').1 ∧ (ofLex z).2 < (ofLex z').2 at hzz'
    change (ofLex old).1 < (ofLex other).1 ∨
      (ofLex old).1 = (ofLex other).1 ∧ (ofLex old).2 < (ofLex other).2
    rcases hzz' with hfirst | ⟨hfirst, hsecond⟩
    · exact Or.inl (by rw [ho, ho']; exact tail_strict v hfirst)
    · have hsame : (ofLex old).1 = (ofLex other).1 := by rw [ho, ho', hfirst]
      refine Or.inr ⟨hsame, ?_⟩
      apply ih (fun e => code (Sum.inr ((ofLex old).1, e))) hsecond hi
      rwa [hsame]

theorem selected_dense (hclosed : CountablyClosed P) (n : ℕ) (code : Prefix n → W1)
    (p : Condition P) (z : Index n) : ∃ q : Condition P, q ≤ p ∧ ∃ old, Selected n code q z old := by
  induction n generalizing p with
  | zero =>
    obtain ⟨q, ⟨v, hv⟩, hqp⟩ := Erdos1172Part3IteratedHechlerClosure.coordinate_dense hclosed (code ()) p
    exact ⟨q, hqp, tail v z, v, hv, rfl⟩
  | succ n ih =>
    obtain ⟨q, ⟨v, hv⟩, hqp⟩ :=
      Erdos1172Part3IteratedHechlerClosure.coordinate_dense hclosed (code (Sum.inl ())) p
    let first : W1 := tail v (ofLex z).1
    obtain ⟨s, hsq, inner, hinner⟩ := ih (fun e => code (Sum.inr (first, e))) q (ofLex z).2
    exact ⟨s, hsq.trans hqp, toLex (first, inner), v, hsq.2.1 _ _ hv, rfl, hinner⟩

theorem exists_clears_of_selected (n : ℕ) (F : FunctionDecisions P (Prefix n) W1)
    (code : Prefix n → W1) (p : Condition P) (z old : Index n) (h : Selected n code p z old)
    (hbound : ∀ e v, p.stem (code e) = some v → ∀ q : P, q ≤ p.base →
      ∀ w : W1, F.decides q e w → w < v)
    (base : P) (hbase : base ≤ p.base) : ∃ q : P, q ≤ base ∧ Clears n F q old := by
  induction n generalizing p base with
  | zero =>
    obtain ⟨v, hv, ho⟩ := h
    obtain ⟨q, hqb, w, hw⟩ := F.dense base ()
    refine ⟨q, hqb, w, hw, ?_⟩
    rw [ho]
    exact (hbound () v hv q (hqb.trans hbase) w hw).trans (lt_tail v z)
  | succ n ih =>
    obtain ⟨v, hv, ho, hi⟩ := h
    obtain ⟨q, hqb, w, hw⟩ := F.dense base (Sum.inl ())
    obtain ⟨s, hsq, hs⟩ := ih (subBounds F (ofLex old).1)
      (fun e => code (Sum.inr ((ofLex old).1, e))) p (ofLex z).2 (ofLex old).2 hi
      (fun e v hv q hq w hw => hbound (Sum.inr ((ofLex old).1, e)) v hv q hq w hw)
      q (hqb.trans hbase)
    refine ⟨s, hsq.trans hqb, w, F.persistent hsq hw, ?_, hs⟩
    rw [ho]
    exact (hbound (Sum.inl ()) v hv q (hqb.trans hbase) w hw).trans (lt_tail v (ofLex z).1)

def thinningClique (hclosed : CountablyClosed P) (n : ℕ) {G : SimpleGraph W2}
    (core : CliqueDecisions P (Index (n + 1)) W2 G) (row : W1 → W1) (hrow : StrictMono row)
    (code : W1 × Prefix n → W1) : CliqueDecisions (Condition P) (Index (n + 1)) W2 G where
  decides p z x := ∃ old : Index n,
    Selected n (fun e => code (row (ofLex z).1, e)) p (ofLex z).2 old ∧
      core.decides p.base (toLex (row (ofLex z).1, old)) x
  dense := by
    intro p z
    obtain ⟨q, hqp, old, hsel⟩ := selected_dense hclosed n (fun e => code (row (ofLex z).1, e)) p (ofLex z).2
    obtain ⟨base, hbase, x, hx⟩ := core.dense q.base (toLex (row (ofLex z).1, old))
    exact ⟨liftBase q base, (liftBase_le q hbase).trans hqp, x, old,
      selected_persistent n _ (liftBase_le q hbase) hsel, hx⟩
  persistent := by
    rintro p q z x hqp ⟨old, hsel, hx⟩
    exact ⟨old, selected_persistent n _ hqp hsel, core.persistent (base_le hqp) hx⟩
  unique := by
    rintro p z x y ⟨old, hsel, hx⟩ ⟨other, hsel', hy⟩
    have heq := selected_unique n _ p hsel hsel'
    subst other
    exact core.unique hx hy
  ordered := by
    rintro p z z' x y hzz' ⟨old, hsel, hx⟩ ⟨other, hsel', hy⟩
    apply core.ordered (j := toLex (row (ofLex z').1, other)) _ hx hy
    change (toLex (ofLex z) : W1 ×ₗ Index n) < toLex (ofLex z') at hzz'
    change (toLex (row (ofLex z).1, old) : W1 ×ₗ Index n) < toLex (row (ofLex z').1, other)
    rw [Prod.Lex.lt_iff] at hzz' ⊢
    change (ofLex z).1 < (ofLex z').1 ∨
      (ofLex z).1 = (ofLex z').1 ∧ (ofLex z).2 < (ofLex z').2 at hzz'
    rcases hzz' with hfirst | ⟨hfirst, hsecond⟩
    · exact Or.inl (hrow hfirst)
    · refine Or.inr ⟨congrArg row hfirst, ?_⟩
      apply selected_ordered n _ p hsecond hsel
      rwa [hfirst]
  adjacent := by
    rintro p z z' x y hzz' ⟨old, hsel, hx⟩ ⟨other, hsel', hy⟩
    apply core.adjacent (j := toLex (row (ofLex z').1, other)) _ hx hy
    intro heq
    have hfirst : (ofLex z).1 = (ofLex z').1 := hrow.injective
      (congrArg (fun t : W1 ×ₗ Index n => (ofLex t).1) heq)
    have hsecond : old = other := congrArg (fun t : W1 ×ₗ Index n => (ofLex t).2) heq
    subst other
    have hinner : (ofLex z).2 = (ofLex z').2 := by
      by_contra hne
      have hselSame : Selected n (fun e => code (row (ofLex z).1, e)) p (ofLex z').2 old := by
        rwa [hfirst]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact (selected_ordered n _ p hlt hsel hselSame).false
      · exact (selected_ordered n _ p hgt hselSame hsel).false
    exact hzz' (congrArg toLex (Prod.ext hfirst hinner))

theorem thinningClique_origin (hclosed : CountablyClosed P) (n : ℕ) {G : SimpleGraph W2}
    (core : CliqueDecisions P (Index (n + 1)) W2 G) (row : W1 → W1) (hrow : StrictMono row)
    (code : W1 × Prefix n → W1) :
    ∀ p z x, (thinningClique hclosed n core row hrow code).decides p z x →
      ∃ old : Index (n + 1), core.decides p.base old x := by
  rintro p z x ⟨old, _, hx⟩
  exact ⟨toLex (row (ofLex z).1, old), hx⟩

end Erdos1172Part3FiniteStemSelection
