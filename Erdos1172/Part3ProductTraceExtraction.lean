/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3TraceScheme

@[expose] public section

/-!
# Product induction for trace-preserving extraction

Every positive whole-row trace supplies increasing positive inner rows.
Inner extraction is globalized with its small-trace transfer law retained
in each outer choice. Countable fusion then assembles a full product.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3ProductTraceExtraction

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularConeRestriction (onCone)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3ProductTraceIdeal (rowCore exists_positive_row)
open Erdos1172Part3TraceScheme (TraceScheme Extracts)
open Erdos1172Part3NamedBlockFlattening (joinedCores onConeCore flatten)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RelationalDecisionFusion (RelationalExtension exists_relational_decisions)
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)

variable {P I : Type} [Preorder P] [LinearOrder I] {G : SimpleGraph W2}

abbrev RowLabel (P I : Type) [Preorder P] [LinearOrder I] (G : SimpleGraph W2) :=
  W1 × CliqueDecisions P I W2 G

def RowOrigin (core : CliqueDecisions P (W1 ×ₗ I) W2 G) (U : RegularName P W2)
    (p : P) (N : RowLabel P I G) : Prop :=
  ∀ q : P, q ≤ p → ∀ z x, N.2.decides q z x → U.holds q x ∧
    ∃ old : I, core.decides q (toLex (N.1, old)) x

def RowTransfer (T : TraceScheme I G) (core : CliqueDecisions P (W1 ×ₗ I) W2 G)
    (p : P) (N : RowLabel P I G) : Prop :=
  ∀ q : P, q ≤ p → ∀ V : RegularName P W2,
    ((T.forOrder P).trace (rowCore core N.1)).holds q V → ((T.forOrder P).trace N.2).holds q V

structure ProductSubsequenceData (T : TraceScheme I G) (core : CliqueDecisions P (W1 ×ₗ I) W2 G)
    (U : RegularName P W2) (p0 : P) where
  choices : FunctionDecisions (Set.Iic p0) W1 (RowLabel P I G)
  origins : ∀ p i N, choices.decides p i N → RowOrigin core U p.val N
  transfers : ∀ p i N, choices.decides p i N → RowTransfer T core p.val N
  indices : ∀ p i N, choices.decides p i N → i < N.1
  ordered_rows : ∀ p i j N M, i < j → choices.decides p i N → choices.decides p j M → N.1 < M.1

theorem exists_product_subsequence_data (T : TraceScheme I G) (hT : Extracts T)
    (hI : #I ≤ ℵ_ 1) (hclosed : CountablyClosed P)
    (core : CliqueDecisions P (W1 ×ₗ I) W2 G) (p0 : P) (U : RegularName P W2)
    (hU : ¬((T.product.forOrder P).trace core).holds p0 U) :
    ∃ q : P, q ≤ p0 ∧ Nonempty (ProductSubsequenceData T core U q) := by
  classical
  obtain ⟨q, hqp0, hq⟩ := (not_holds_iff_exists_neg ((T.product.forOrder P).trace core) p0 U).mp hU
  let R (p : Set.Iic q) (N : RowLabel P I G) := RowOrigin core U p.val N ∧ RowTransfer T core p.val N
  let K (i : W1) (_ : Set.Iic q) (N : RowLabel P I G) := i < N.1
  let J (_ : Set.Iic q) (N M : RowLabel P I G) := N.1 < M.1
  have hextend : RelationalExtension R K J := by
    intro i p selected hcount hselected
    obtain ⟨bound, hbound⟩ := exists_bound_of_countable
      (insert i (Prod.fst '' selected)) ((hcount.image Prod.fst).insert i)
    obtain ⟨s, hsp, oldRow, hrow, hs⟩ := exists_positive_row
      (T.forOrder P) core q U hq p.val p.property bound
    obtain ⟨t, hts, inner, hmember, htransfer⟩ :=
      hT hclosed (rowCore core oldRow) s U (hs s le_rfl)
    obtain ⟨global, hglobal, _⟩ :=
      Erdos1172Part3CliqueConeExtension.exists_global_clique_from_cone hclosed t inner hI
    let N : RowLabel P I G := (oldRow, global)
    refine ⟨⟨t, (hts.trans hsp).trans p.property⟩, hts.trans hsp, N, ⟨?_, ?_⟩,
      (hbound i (Set.mem_insert _ _)).trans hrow, ?_⟩
    · intro v hvt z x hx
      exact hmember ⟨v, hvt⟩ z x ((hglobal v hvt z x).mp hx)
    · intro v hvt V hV
      exact T.fromCone t inner global (fun w z x hx => (hglobal w.val w.property z x).mp hx)
        ⟨v, hvt⟩ V (htransfer ⟨v, hvt⟩ V hV)
    · intro M hM
      exact (hbound M.1 (Set.mem_insert_of_mem _ ⟨M, hM, rfl⟩)).trans hrow
  obtain ⟨F, hF, hcross⟩ := exists_relational_decisions
    (Erdos1172Part3ClosedDenseRequirements.countablyClosed_Iic hclosed q) R K J
    (fun hsp h => ⟨fun t hts => h.1 t (hts.trans hsp), fun t hts => h.2 t (hts.trans hsp)⟩)
    (fun _ h => h) (fun _ h => h) hextend
  exact ⟨q, hqp0, ⟨⟨F, fun p i N hN => (hF p i N hN).1.1,
    fun p i N hN => (hF p i N hN).1.2, fun p i N hN => (hF p i N hN).2, hcross⟩⟩⟩

variable {T : TraceScheme I G} {core : CliqueDecisions P (W1 ×ₗ I) W2 G}
  {U : RegularName P W2} {p0 : P}

theorem ProductSubsequenceData.joined (data : ProductSubsequenceData T core U p0)
    (p : Set.Iic p0) (i j : W1) (N M : RowLabel P I G) (hij : i < j)
    (hN : data.choices.decides p i N) (hM : data.choices.decides p j M) :
    (joinedCores (onConeCore p0 N.2) (onConeCore p0 M.2)).holds p () := by
  intro t htp k y hy s hst l x hx
  obtain ⟨_, oldl, hxl⟩ := data.origins p i N hN s.val (hst.trans htp) l x hx
  obtain ⟨_, oldk, hyk⟩ := data.origins p j M hM s.val (hst.trans htp) k y (M.2.persistent hst hy)
  have hlt : toLex (N.1, oldl) < toLex (M.1, oldk) := by
    rw [Prod.Lex.lt_iff]
    exact Or.inl (data.ordered_rows p i j N M hij hN hM)
  exact ⟨core.ordered hlt hxl hyk, core.adjacent hlt.ne hxl hyk⟩

noncomputable def ProductSubsequenceData.toProduct (data : ProductSubsequenceData T core U p0) :
    CliqueDecisions (Set.Iic p0) (W1 ×ₗ I) W2 G :=
  flatten (fun N : RowLabel P I G => onConeCore p0 N.2) data.choices data.joined

theorem ProductSubsequenceData.membership (data : ProductSubsequenceData T core U p0)
    (p : Set.Iic p0) (z : W1 ×ₗ I) (x : W2) (hx : data.toProduct.decides p z x) :
    U.holds p.val x ∧ ∃ oldRow : W1, ∃ oldInner : I,
      (ofLex z).1 < oldRow ∧ core.decides p.val (toLex (oldRow, oldInner)) x := by
  obtain ⟨N, hN, hx⟩ := hx
  obtain ⟨hUx, old, hcore⟩ := data.origins p (ofLex z).1 N hN p.val le_rfl (ofLex z).2 x hx
  exact ⟨hUx, N.1, old, data.indices p (ofLex z).1 N hN, hcore⟩

theorem ProductSubsequenceData.row_trace_transfer (data : ProductSubsequenceData T core U p0)
    (p : Set.Iic p0) (V : RegularName P W2) (bound i : W1) (hi : bound < i)
    (hsmall : ∀ oldRow : W1, bound < oldRow →
      ((T.forOrder P).trace (rowCore core oldRow)).holds p.val V) :
    ((T.forOrder (Set.Iic p0)).trace (rowCore data.toProduct i)).holds p (onCone p0 V) := by
  apply ((T.forOrder (Set.Iic p0)).trace (rowCore data.toProduct i)).of_dense p (onCone p0 V)
  intro q hqp
  obtain ⟨s, hsq, N, hN⟩ := data.choices.dense q i
  have hbi : bound < N.1 := hi.trans (data.indices s i N hN)
  have hNs : ((T.forOrder P).trace N.2).holds s.val V := data.transfers s i N hN s.val le_rfl V
    (((T.forOrder P).trace (rowCore core N.1)).persistent (hsq.trans hqp) (hsmall N.1 hbi))
  refine ⟨s, hsq, T.toCone p0 N.2 (rowCore data.toProduct i) s V ?_ hNs⟩
  intro t hts z x hx
  obtain ⟨M, hM, hx⟩ := hx
  have heq : N = M := data.choices.unique (data.choices.persistent hts hN) hM
  subst M
  exact hx

theorem ProductSubsequenceData.trace_transfer (data : ProductSubsequenceData T core U p0)
    (p : Set.Iic p0) (V : RegularName P W2)
    (hsmall : ((T.product.forOrder P).trace core).holds p.val V) :
    ((T.product.forOrder (Set.Iic p0)).trace data.toProduct).holds p (onCone p0 V) := by
  intro q hqp
  obtain ⟨s, hsq, bound, hs⟩ := hsmall q.val hqp
  exact ⟨⟨s, hsq.trans q.property⟩, hsq, bound,
    fun i hi => data.row_trace_transfer ⟨s, hsq.trans q.property⟩ V bound i hi hs⟩

theorem extracts_product (T : TraceScheme I G) (hT : Extracts T) (hI : #I ≤ ℵ_ 1) :
    Extracts T.product := by
  intro P inst hclosed core p0 U hU
  obtain ⟨q, hqp0, ⟨data⟩⟩ := exists_product_subsequence_data T hT hI hclosed core p0 U hU
  refine ⟨q, hqp0, data.toProduct, ?_, data.trace_transfer⟩
  intro p z x hx
  obtain ⟨hUx, oldRow, oldInner, _, hdec⟩ := data.membership p z x hx
  exact ⟨hUx, toLex (oldRow, oldInner), hdec⟩

end Erdos1172Part3ProductTraceExtraction
