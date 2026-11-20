/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3ProductTraceIdeal

@[expose] public section

/-!
# Extracting a whole cube while preserving its small traces

Outer fusion chooses increasing old square rows. Each positive old row
supplies a square subsequence together with its trace-transfer theorem.
The chosen old row is fixed by a single outer decision. This retained
row-local law is stronger than coordinatewise vertex provenance alone.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3CubeTraceSubsequence

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularConeRestriction (onCone)
open Erdos1172Part3NamedTraceIdeal (traceName)
open Erdos1172Part3NamedSquareTraceIdeal (squareTraceName)
open Erdos1172Part3ProductTraceIdeal (rowCore cubeTrace squareTrace squareTrace_eq)
open Erdos1172Part3NamedSquareSubsequence (exists_square_subsequence_data)
open Erdos1172Part3NamedBlockFlattening (joinedCores onConeCore flatten)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RelationalDecisionFusion (RelationalExtension exists_relational_decisions)
open Erdos1172Part3StationarySquareDecisions (Square)
open Erdos1172Part3FullSourceCubes (Cube)
open Erdos1172Part3CliqueNameCoding (mk_square_le)
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)

variable {P : Type} [Preorder P] {G : SimpleGraph W2}

theorem line_trace_to_cone (p0 : P) (core : CliqueDecisions P W1 W2 G)
    (sub : CliqueDecisions (Set.Iic p0) W1 W2 G) (p : Set.Iic p0) (U : RegularName P W2)
    (hdec : ∀ q : Set.Iic p0, q ≤ p → ∀ i x, sub.decides q i x → core.decides q.val i x)
    (hsmall : (traceName core).holds p.val U) : (traceName sub).holds p (onCone p0 U) := by
  intro q hqp
  obtain ⟨s, hsq, bound, hs⟩ := hsmall q.val hqp
  refine ⟨⟨s, hsq.trans q.property⟩, hsq, bound, ?_⟩
  intro t hts i hi x hx hUx
  exact hs t.val hts i hi x (hdec t ((hts.trans hsq).trans hqp) i x hx) hUx

theorem square_trace_to_cone (p0 : P) (core : CliqueDecisions P Square W2 G)
    (sub : CliqueDecisions (Set.Iic p0) Square W2 G) (p : Set.Iic p0) (U : RegularName P W2)
    (hdec : ∀ q : Set.Iic p0, q ≤ p → ∀ z x, sub.decides q z x → core.decides q.val z x)
    (hsmall : (squareTraceName core).holds p.val U) :
    (squareTraceName sub).holds p (onCone p0 U) := by
  intro q hqp
  obtain ⟨s, hsq, bound, hs⟩ := hsmall q.val hqp
  refine ⟨⟨s, hsq.trans q.property⟩, hsq, bound, ?_⟩
  intro i hi
  exact line_trace_to_cone p0
    (Erdos1172Part3NamedSquareTraceIdeal.rowCore core i)
    (Erdos1172Part3NamedSquareTraceIdeal.rowCore sub i)
    ⟨s, hsq.trans q.property⟩ U
    (fun t hts j x hx => hdec t ((hts.trans hsq).trans hqp) (toLex (i, j)) x hx) (hs i hi)

abbrev RowLabel (P : Type) [Preorder P] (G : SimpleGraph W2) := W1 × CliqueDecisions P Square W2 G

def RowOrigin (core : CliqueDecisions P Cube W2 G) (U : RegularName P W2)
    (p : P) (N : RowLabel P G) : Prop :=
  ∀ q : P, q ≤ p → ∀ z x, N.2.decides q z x → U.holds q x ∧
    ∃ old : Square, core.decides q (toLex (N.1, old)) x

def RowTransfer (core : CliqueDecisions P Cube W2 G) (p : P) (N : RowLabel P G) : Prop :=
  ∀ q : P, q ≤ p → ∀ V : RegularName P W2,
    (squareTraceName (rowCore core N.1)).holds q V → (squareTraceName N.2).holds q V

theorem rowOrigin_persistent {core : CliqueDecisions P Cube W2 G} {U : RegularName P W2}
    {p q : P} {N : RowLabel P G} (hqp : q ≤ p) (h : RowOrigin core U p N) :
    RowOrigin core U q N := fun s hsq => h s (hsq.trans hqp)

theorem rowTransfer_persistent {core : CliqueDecisions P Cube W2 G}
    {p q : P} {N : RowLabel P G} (hqp : q ≤ p) (h : RowTransfer core p N) :
    RowTransfer core q N := fun s hsq => h s (hsq.trans hqp)

structure CubeSubsequenceData (core : CliqueDecisions P Cube W2 G)
    (U : RegularName P W2) (p0 : P) where
  choices : FunctionDecisions (Set.Iic p0) W1 (RowLabel P G)
  origins : ∀ p i N, choices.decides p i N → RowOrigin core U p.val N
  transfers : ∀ p i N, choices.decides p i N → RowTransfer core p.val N
  indices : ∀ p i N, choices.decides p i N → i < N.1
  ordered_rows : ∀ p i j N M, i < j → choices.decides p i N → choices.decides p j M → N.1 < M.1

theorem exists_cube_subsequence_data (hclosed : CountablyClosed P)
    (core : CliqueDecisions P Cube W2 G) (p0 : P) (U : RegularName P W2)
    (hU : ¬(cubeTrace.trace core).holds p0 U) :
    ∃ q : P, q ≤ p0 ∧ Nonempty (CubeSubsequenceData core U q) := by
  classical
  obtain ⟨q, hqp0, hq⟩ := (not_holds_iff_exists_neg (cubeTrace.trace core) p0 U).mp hU
  let R (p : Set.Iic q) (N : RowLabel P G) := RowOrigin core U p.val N ∧ RowTransfer core p.val N
  let K (i : W1) (_ : Set.Iic q) (N : RowLabel P G) := i < N.1
  let J (_ : Set.Iic q) (N M : RowLabel P G) := N.1 < M.1
  have hextend : RelationalExtension R K J := by
    intro i p selected hcount hselected
    have hrowsCount : (Prod.fst '' selected).Countable := hcount.image Prod.fst
    obtain ⟨bound, hbound⟩ := exists_bound_of_countable
      (insert i (Prod.fst '' selected)) (hrowsCount.insert i)
    obtain ⟨s, hsp, oldRow, hrow, hs⟩ := Erdos1172Part3ProductTraceIdeal.exists_positive_row
      squareTrace core q U hq p.val p.property bound
    have hnot : ¬(squareTraceName (rowCore core oldRow)).holds s U := by
      rw [← squareTrace_eq (rowCore core oldRow)]
      exact hs s le_rfl
    obtain ⟨t, hts, ⟨innerData⟩⟩ := exists_square_subsequence_data hclosed (rowCore core oldRow) s U hnot
    obtain ⟨global, hglobal, _⟩ :=
      Erdos1172Part3CliqueConeExtension.exists_global_clique_from_cone hclosed t
        innerData.toSquare mk_square_le
    let N : RowLabel P G := (oldRow, global)
    refine ⟨⟨t, (hts.trans hsp).trans p.property⟩, hts.trans hsp, N, ⟨?_, ?_⟩,
      (hbound i (Set.mem_insert _ _)).trans hrow, ?_⟩
    · intro v hvt z x hx
      obtain ⟨hUx, oldMiddle, oldInner, _, _, hdec⟩ := innerData.membership ⟨v, hvt⟩ z x
        ((hglobal v hvt z x).mp hx)
      exact ⟨hUx, toLex (oldMiddle, oldInner), hdec⟩
    · intro v hvt V hV
      have hsmall := innerData.square_trace_transfer ⟨v, hvt⟩ V hV
      exact Erdos1172Part3GlobalNamedSquareLoss.square_trace_from_cone t innerData.toSquare global
        (fun w z x hx => (hglobal w.val w.property z x).mp hx) ⟨v, hvt⟩ V hsmall
    · intro M hM
      exact (hbound M.1 (Set.mem_insert_of_mem _ ⟨M, hM, rfl⟩)).trans hrow
  obtain ⟨F, hF, hcross⟩ := exists_relational_decisions
    (Erdos1172Part3ClosedDenseRequirements.countablyClosed_Iic hclosed q) R K J
    (fun hsp h => ⟨rowOrigin_persistent hsp h.1, rowTransfer_persistent hsp h.2⟩)
    (fun _ h => h) (fun _ h => h) hextend
  exact ⟨q, hqp0, ⟨⟨F, fun p i N hN => (hF p i N hN).1.1,
    fun p i N hN => (hF p i N hN).1.2, fun p i N hN => (hF p i N hN).2, hcross⟩⟩⟩

variable {core : CliqueDecisions P Cube W2 G} {U : RegularName P W2} {p0 : P}

theorem CubeSubsequenceData.joined (data : CubeSubsequenceData core U p0)
    (p : Set.Iic p0) (i j : W1) (N M : RowLabel P G) (hij : i < j)
    (hN : data.choices.decides p i N) (hM : data.choices.decides p j M) :
    (joinedCores (onConeCore p0 N.2) (onConeCore p0 M.2)).holds p () := by
  intro t htp k y hy s hst l x hx
  obtain ⟨_, oldl, hxl⟩ := data.origins p i N hN s.val (hst.trans htp) l x hx
  obtain ⟨_, oldk, hyk⟩ := data.origins p j M hM s.val (hst.trans htp) k y (M.2.persistent hst hy)
  have hlt : toLex (N.1, oldl) < toLex (M.1, oldk) := by
    rw [Prod.Lex.lt_iff]
    exact Or.inl (data.ordered_rows p i j N M hij hN hM)
  exact ⟨core.ordered hlt hxl hyk, core.adjacent hlt.ne hxl hyk⟩

noncomputable def CubeSubsequenceData.toCube (data : CubeSubsequenceData core U p0) :
    CliqueDecisions (Set.Iic p0) Cube W2 G :=
  flatten (fun N : RowLabel P G => onConeCore p0 N.2) data.choices data.joined

theorem CubeSubsequenceData.membership (data : CubeSubsequenceData core U p0)
    (p : Set.Iic p0) (z : Cube) (x : W2) (hx : data.toCube.decides p z x) :
    U.holds p.val x ∧ ∃ oldRow : W1, ∃ oldInner : Square,
      (ofLex z).1 < oldRow ∧ core.decides p.val (toLex (oldRow, oldInner)) x := by
  obtain ⟨N, hN, hx⟩ := hx
  obtain ⟨hUx, old, hcore⟩ := data.origins p (ofLex z).1 N hN p.val le_rfl (ofLex z).2 x hx
  exact ⟨hUx, N.1, old, data.indices p (ofLex z).1 N hN, hcore⟩

theorem CubeSubsequenceData.row_trace_transfer (data : CubeSubsequenceData core U p0)
    (p : Set.Iic p0) (V : RegularName P W2) (bound i : W1) (hi : bound < i)
    (hsmall : ∀ oldRow : W1, bound < oldRow → (squareTraceName (rowCore core oldRow)).holds p.val V) :
    (squareTraceName (rowCore data.toCube i)).holds p (onCone p0 V) := by
  apply (squareTraceName (rowCore data.toCube i)).of_dense p (onCone p0 V)
  intro q hqp
  obtain ⟨s, hsq, N, hN⟩ := data.choices.dense q i
  have hbi : bound < N.1 := hi.trans (data.indices s i N hN)
  have hNs : (squareTraceName N.2).holds s.val V := data.transfers s i N hN s.val le_rfl V
    ((squareTraceName (rowCore core N.1)).persistent (hsq.trans hqp) (hsmall N.1 hbi))
  refine ⟨s, hsq, square_trace_to_cone p0 N.2 (rowCore data.toCube i) s V ?_ hNs⟩
  intro t hts z x hx
  obtain ⟨M, hM, hx⟩ := hx
  have heq : N = M := data.choices.unique (data.choices.persistent hts hN) hM
  subst M
  exact hx

theorem CubeSubsequenceData.cube_trace_transfer (data : CubeSubsequenceData core U p0)
    (p : Set.Iic p0) (V : RegularName P W2) (hsmall : (cubeTrace.trace core).holds p.val V) :
    (cubeTrace.trace data.toCube).holds p (onCone p0 V) := by
  intro q hqp
  obtain ⟨s, hsq, bound, hs⟩ := hsmall q.val hqp
  refine ⟨⟨s, hsq.trans q.property⟩, hsq, bound, ?_⟩
  intro i hi
  rw [squareTrace_eq]
  apply data.row_trace_transfer ⟨s, hsq.trans q.property⟩ V bound i hi
  intro oldRow hrow
  rw [← squareTrace_eq]
  exact hs oldRow hrow

end Erdos1172Part3CubeTraceSubsequence
