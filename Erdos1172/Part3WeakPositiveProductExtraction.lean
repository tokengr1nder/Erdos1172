/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3OmegaPositiveExtraction

@[expose] public section

/-!
# Product extraction without a small-trace transfer assertion

Countable relational fusion selects increasing positive rows and their
extracted inner cores. This construction uses only positive extraction,
not countable completeness or a trace-preserving reindexing law. It
therefore applies to the proved weak omega trace.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3WeakPositiveProductExtraction

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3ProductTraceIdeal (rowCore)
open Erdos1172Part3WeakProductTrace (WeakCoreTrace exists_positive_row)
open Erdos1172Part3ProductTraceExtraction (RowLabel RowOrigin)
open Erdos1172Part3NamedBlockFlattening (joinedCores onConeCore flatten)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RelationalDecisionFusion (RelationalExtension exists_relational_decisions)
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)

variable {P I : Type} [Preorder P] [LinearOrder I] {G : SimpleGraph W2}

def ExtractsFull (T : WeakCoreTrace P I G) : Prop :=
  ∀ core : CliqueDecisions P I W2 G, ∀ p0 : P, ∀ U : RegularName P W2,
    (neg (T.trace core)).holds p0 U →
    ∃ q : P, q ≤ p0 ∧ ∃ sub : CliqueDecisions (Set.Iic q) I W2 G,
      ∀ p i x, sub.decides p i x → U.holds p.val x ∧ ∃ j : I, core.decides p.val j x

structure PositiveProductData (core : CliqueDecisions P (W1 ×ₗ I) W2 G)
    (U : RegularName P W2) (p0 : P) where
  choices : FunctionDecisions (Set.Iic p0) W1 (RowLabel P I G)
  origins : ∀ p i N, choices.decides p i N → RowOrigin core U p.val N
  indices : ∀ p i N, choices.decides p i N → i < N.1
  ordered_rows : ∀ p i j N M, i < j → choices.decides p i N → choices.decides p j M → N.1 < M.1

theorem exists_positive_product_data (T : WeakCoreTrace P I G) (hT : ExtractsFull T)
    (hI : #I ≤ ℵ_ 1) (hclosed : CountablyClosed P)
    (core : CliqueDecisions P (W1 ×ₗ I) W2 G) (p0 : P) (U : RegularName P W2)
    (hU : (neg (T.product.trace core)).holds p0 U) : Nonempty (PositiveProductData core U p0) := by
  classical
  let R (p : Set.Iic p0) (N : RowLabel P I G) := RowOrigin core U p.val N
  let K (i : W1) (_ : Set.Iic p0) (N : RowLabel P I G) := i < N.1
  let J (_ : Set.Iic p0) (N M : RowLabel P I G) := N.1 < M.1
  have hextend : RelationalExtension R K J := by
    intro i p selected hcount hselected
    obtain ⟨bound, hbound⟩ := exists_bound_of_countable
      (insert i (Prod.fst '' selected)) ((hcount.image Prod.fst).insert i)
    obtain ⟨s, hsp, oldRow, hrow, hs⟩ := exists_positive_row T core p0 U hU p.val p.property bound
    obtain ⟨t, hts, inner, hmember⟩ := hT (rowCore core oldRow) s U hs
    obtain ⟨global, hglobal, _⟩ :=
      Erdos1172Part3CliqueConeExtension.exists_global_clique_from_cone hclosed t inner hI
    let N : RowLabel P I G := (oldRow, global)
    refine ⟨⟨t, (hts.trans hsp).trans p.property⟩, hts.trans hsp, N, ?_,
      (hbound i (Set.mem_insert _ _)).trans hrow, ?_⟩
    · intro v hvt z x hx
      exact hmember ⟨v, hvt⟩ z x ((hglobal v hvt z x).mp hx)
    · intro M hM
      exact (hbound M.1 (Set.mem_insert_of_mem _ ⟨M, hM, rfl⟩)).trans hrow
  obtain ⟨F, hF, hcross⟩ := exists_relational_decisions
    (Erdos1172Part3ClosedDenseRequirements.countablyClosed_Iic hclosed p0) R K J
    (fun hsp h t hts => h t (hts.trans hsp)) (fun _ h => h) (fun _ h => h) hextend
  exact ⟨⟨F, fun p i N hN => (hF p i N hN).1, fun p i N hN => (hF p i N hN).2, hcross⟩⟩

variable {core : CliqueDecisions P (W1 ×ₗ I) W2 G} {U : RegularName P W2} {p0 : P}

theorem PositiveProductData.joined (data : PositiveProductData core U p0)
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

noncomputable def PositiveProductData.toProduct (data : PositiveProductData core U p0) :
    CliqueDecisions (Set.Iic p0) (W1 ×ₗ I) W2 G :=
  flatten (fun N : RowLabel P I G => onConeCore p0 N.2) data.choices data.joined

theorem PositiveProductData.membership (data : PositiveProductData core U p0)
    (p : Set.Iic p0) (z : W1 ×ₗ I) (x : W2) (hx : data.toProduct.decides p z x) :
    U.holds p.val x ∧ ∃ oldRow : W1, ∃ oldInner : I,
      (ofLex z).1 < oldRow ∧ core.decides p.val (toLex (oldRow, oldInner)) x := by
  obtain ⟨N, hN, hx⟩ := hx
  obtain ⟨hUx, old, hcore⟩ := data.origins p (ofLex z).1 N hN p.val le_rfl (ofLex z).2 x hx
  exact ⟨hUx, N.1, old, data.indices p (ofLex z).1 N hN, hcore⟩

theorem extracts_full_product (T : WeakCoreTrace P I G) (hT : ExtractsFull T)
    (hI : #I ≤ ℵ_ 1) (hclosed : CountablyClosed P) : ExtractsFull T.product := by
  intro core p0 U hU
  obtain ⟨data⟩ := exists_positive_product_data T hT hI hclosed core p0 U hU
  refine ⟨p0, le_rfl, data.toProduct, ?_⟩
  intro p z x hx
  obtain ⟨hUx, oldRow, oldInner, _, hdec⟩ := data.membership p z x hx
  exact ⟨hUx, toLex (oldRow, oldInner), hdec⟩

open Erdos1172Part3OmegaPowerIndex (OmegaIndex mk_omegaIndex_le)
open Erdos1172Part3OmegaLevelTrace (omegaWeakTrace omegaProductTrace)

theorem omega_extracts_full (hclosed : CountablyClosed P) :
    ExtractsFull (omegaWeakTrace (P := P) (G := G)) :=
  Erdos1172Part3OmegaPositiveExtraction.exists_omega_subcore hclosed

theorem omega_product_extracts_full (hclosed : CountablyClosed P) :
    ExtractsFull (omegaProductTrace (P := P) (G := G)) :=
  extracts_full_product omegaWeakTrace (omega_extracts_full hclosed) mk_omegaIndex_le hclosed

end Erdos1172Part3WeakPositiveProductExtraction
