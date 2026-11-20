/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedSquareTraceIdeal

@[expose] public section

/-!
# Square subsequences with two-coordinate provenance

Outer fusion chooses increasing old rows. Within each chosen row, trace
positivity supplies a subsequence with increasing old inner indices.
Neither the row choices nor their bounds are decided simultaneously at
the end of the omegaOne recursion.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedSquareSubsequence

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularConeRestriction (onCone)
open Erdos1172Part3NamedTraceIdeal
open Erdos1172Part3NamedTraceSubsequence (exists_cone_subsequence)
open Erdos1172Part3NamedSquareTraceIdeal
open Erdos1172Part3NamedBlockFlattening (joinedCores onConeCore flatten)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RelationalDecisionFusion (RelationalExtension exists_relational_decisions)
open Erdos1172Part3StationarySquareDecisions (Square)
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)

variable {P : Type} [Preorder P] {G : SimpleGraph W2}

abbrev RowLabel (P : Type) [Preorder P] (G : SimpleGraph W2) :=
  W1 × CliqueDecisions P W1 W2 G

def RowOrigin (core : CliqueDecisions P Square W2 G) (U : RegularName P W2)
    (p : P) (N : RowLabel P G) : Prop :=
  ∀ q : P, q ≤ p → ∀ j x, N.2.decides q j x → U.holds q x ∧
    ∃ k : W1, j < k ∧ core.decides q (toLex (N.1, k)) x

theorem rowOrigin_persistent {core : CliqueDecisions P Square W2 G} {U : RegularName P W2}
    {p q : P} {N : RowLabel P G} (hqp : q ≤ p) (h : RowOrigin core U p N) :
    RowOrigin core U q N := fun s hsq => h s (hsq.trans hqp)

structure SquareSubsequenceData (core : CliqueDecisions P Square W2 G)
    (U : RegularName P W2) (p0 : P) where
  choices : FunctionDecisions (Set.Iic p0) W1 (RowLabel P G)
  origins : ∀ p i N, choices.decides p i N → RowOrigin core U p.val N
  indices : ∀ p i N, choices.decides p i N → i < N.1
  ordered_rows : ∀ p i j N M, i < j → choices.decides p i N →
    choices.decides p j M → N.1 < M.1

theorem exists_square_subsequence_data (hclosed : CountablyClosed P)
    (core : CliqueDecisions P Square W2 G) (p0 : P) (U : RegularName P W2)
    (hU : ¬(squareTraceName core).holds p0 U) :
    ∃ q : P, q ≤ p0 ∧ Nonempty (SquareSubsequenceData core U q) := by
  classical
  obtain ⟨q, hqp0, hq⟩ := (not_holds_iff_exists_neg (squareTraceName core) p0 U).mp hU
  let R (p : Set.Iic q) (N : RowLabel P G) := RowOrigin core U p.val N
  let K (i : W1) (_ : Set.Iic q) (N : RowLabel P G) := i < N.1
  let J (_ : Set.Iic q) (N M : RowLabel P G) := N.1 < M.1
  have hextend : RelationalExtension R K J := by
    intro i p selected hcount hselected
    have hrowsCount : (Prod.fst '' selected).Countable := hcount.image Prod.fst
    obtain ⟨bound, hbound⟩ := exists_bound_of_countable
      (insert i (Prod.fst '' selected)) (hrowsCount.insert i)
    obtain ⟨s, hsp, oldRow, hrow, hs⟩ := exists_positive_row core q U hq p.val p.property bound
    obtain ⟨t, hts, row, hrowOrigin⟩ := exists_cone_subsequence hclosed
      (rowCore core oldRow) s U (hs s le_rfl)
    obtain ⟨global, hglobal, _⟩ :=
      Erdos1172Part3CliqueConeExtension.exists_global_clique_from_cone hclosed t row (by
        simp only [W1, Cardinal.mk_toType, Ordinal.card_omega, le_refl])
    let N : RowLabel P G := (oldRow, global)
    refine ⟨⟨t, (hts.trans hsp).trans p.property⟩, hts.trans hsp, N, ?_,
      (hbound i (Set.mem_insert _ _)).trans hrow, ?_⟩
    · intro v hvt j x hx
      exact hrowOrigin ⟨v, hvt⟩ j x ((hglobal v hvt j x).mp hx)
    · intro M hM
      exact (hbound M.1 (Set.mem_insert_of_mem _ ⟨M, hM, rfl⟩)).trans hrow
  obtain ⟨F, hF, hcross⟩ := exists_relational_decisions
    (Erdos1172Part3ClosedDenseRequirements.countablyClosed_Iic hclosed q) R K J
    (fun hsp h => rowOrigin_persistent hsp h) (fun _ h => h) (fun _ h => h) hextend
  exact ⟨q, hqp0, ⟨⟨F, fun p i N hN => (hF p i N hN).1,
    fun p i N hN => (hF p i N hN).2, hcross⟩⟩⟩

variable {core : CliqueDecisions P Square W2 G} {U : RegularName P W2} {p0 : P}

theorem SquareSubsequenceData.joined (data : SquareSubsequenceData core U p0)
    (p : Set.Iic p0) (i j : W1) (N M : RowLabel P G) (hij : i < j)
    (hN : data.choices.decides p i N) (hM : data.choices.decides p j M) :
    (joinedCores (onConeCore p0 N.2) (onConeCore p0 M.2)).holds p () := by
  intro t htp k y hy s hst l x hx
  obtain ⟨_, oldl, hl, hxl⟩ := data.origins p i N hN s.val (hst.trans htp) l x hx
  obtain ⟨_, oldk, hk, hyk⟩ := data.origins p j M hM s.val (hst.trans htp) k y
    (M.2.persistent hst hy)
  have hlt : toLex (N.1, oldl) < toLex (M.1, oldk) := by
    rw [Prod.Lex.lt_iff]
    exact Or.inl (data.ordered_rows p i j N M hij hN hM)
  exact ⟨core.ordered hlt hxl hyk, core.adjacent hlt.ne hxl hyk⟩

noncomputable def SquareSubsequenceData.toSquare (data : SquareSubsequenceData core U p0) :
    CliqueDecisions (Set.Iic p0) Square W2 G :=
  flatten (fun N : RowLabel P G => onConeCore p0 N.2) data.choices data.joined

theorem SquareSubsequenceData.membership (data : SquareSubsequenceData core U p0)
    (p : Set.Iic p0) (z : Square) (x : W2) (hx : data.toSquare.decides p z x) :
    U.holds p.val x ∧ ∃ oldRow oldInner : W1,
      (ofLex z).1 < oldRow ∧ (ofLex z).2 < oldInner ∧
        core.decides p.val (toLex (oldRow, oldInner)) x := by
  obtain ⟨N, hN, hx⟩ := hx
  obtain ⟨hUx, k, hk, hcore⟩ := data.origins p (ofLex z).1 N hN p.val le_rfl (ofLex z).2 x hx
  exact ⟨hUx, N.1, k, data.indices p (ofLex z).1 N hN, hk, hcore⟩

/-- Deciding a single new row fixes its old row. Its inner bound can then
be obtained densely, independently of the other new rows. -/
theorem SquareSubsequenceData.row_trace_transfer (data : SquareSubsequenceData core U p0)
    (p : Set.Iic p0) (V : RegularName P W2) (bound i : W1) (hi : bound < i)
    (hsmall : ∀ oldRow : W1, bound < oldRow → (traceName (rowCore core oldRow)).holds p.val V) :
    (traceName (rowCore data.toSquare i)).holds p (onCone p0 V) := by
  intro q hqp
  obtain ⟨s, hsq, N, hN⟩ := data.choices.dense q i
  have hbi : bound < N.1 := hi.trans (data.indices s i N hN)
  obtain ⟨t, hts, innerBound, ht⟩ := hsmall N.1 hbi s.val (hsq.trans hqp)
  refine ⟨⟨t, hts.trans s.property⟩, hts.trans hsq, innerBound, ?_⟩
  intro v hvt j hj x hx hVx
  obtain ⟨M, hM, hx⟩ := hx
  have heq : N = M := data.choices.unique
    (data.choices.persistent (hvt.trans hts) hN) hM
  subst M
  obtain ⟨_, k, hjk, hk⟩ := data.origins s i N hN v.val (hvt.trans hts) j x hx
  exact ht v.val hvt k (hj.trans hjk) x hk hVx

theorem SquareSubsequenceData.square_trace_transfer (data : SquareSubsequenceData core U p0)
    (p : Set.Iic p0) (V : RegularName P W2) (hsmall : (squareTraceName core).holds p.val V) :
    (squareTraceName data.toSquare).holds p (onCone p0 V) := by
  intro q hqp
  obtain ⟨s, hsq, bound, hs⟩ := hsmall q.val hqp
  exact ⟨⟨s, hsq.trans q.property⟩, hsq, bound,
    fun i hi => data.row_trace_transfer ⟨s, hsq.trans q.property⟩ V bound i hi hs⟩

end Erdos1172Part3NamedSquareSubsequence
