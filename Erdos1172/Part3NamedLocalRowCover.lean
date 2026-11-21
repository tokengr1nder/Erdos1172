/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedLowerCovers
public import Erdos1172.Part3NamedDomainPieces
public import Erdos1172.Part3NamedCoverBounds

@[expose] public section

/-!
# Countable endpoint supports and actual lower covers for one row

Decompose the fixed short enumeration domain into countably many pure
pieces. Singleton pieces retain their actual singleton value; the other
pieces retain a strict upper endpoint with dense cofinality below it.
These countably many endpoints can be fixed simultaneously.

Each pure piece is then covered by the named lower-cover interface, and
one common upper function name combines the countably many resulting
names. The final cover assertion uses actual dense membership throughout.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedLocalRowCover

open ErdosRadoCHAsym (W1)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName)
open Erdos1172Part3RegularConeRestriction (onCone)
open Erdos1172Part3NamedCofinality (OrderedDecisions)
open Erdos1172Part3NamedFinalTail (DenseCoverage)
open Erdos1172Part3NamedDomainPieces
open Erdos1172Part3NamedCofinalEndpoint
open Erdos1172Part3FinitePowerDecomposition (PowerPiece)
open Erdos1172Part3CofinalLineCover (LineCoverData)
open Erdos1172Part3CofinalPowerCoverAssembly (LowerCovers)
open Erdos1172Part3NamedLowerCovers (NamedLowerCovers)
open Erdos1172Part3SupportedCoverRealization

variable {P I V : Type} [Preorder P] [LinearOrder V] [WellFoundedLT V] {n : ℕ}

/-- The endpoint set and lower-cover function chosen on one actual cone.
The original source may contain other rows, ignored by `covered`. -/
structure LocalRowCover (data : LineCoverData V) (L : LowerCovers n V)
    (U : RegularName P V) (i : W1) (q : P) where
  endpoints : Set V
  countable : endpoints.Countable
  endpoint_le : ∀ y ∈ endpoints, y ≤ data.cut i
  row_witness : ∀ y ∈ endpoints, ∃ x : V, data.row x = i ∧ x ≤ y
  functionName : FunctionDecisions (Set.Iic q) W1 W1
  covered : ∀ p : Set.Iic q, ∀ x : V, U.holds p.val x → data.row x = i →
    ∃ r : Set.Iic q, r ≤ p ∧ (x ∈ endpoints ∨
      ∃ y ∈ endpoints, ∃ k : Fin n, (coverName functionName (L.into y k)).holds r x)

/-- Restrict just the condition type of a function decision system. -/
def onConeDecisions (E : FunctionDecisions P I V) (q : P) :
    FunctionDecisions (Set.Iic q) I V where
  decides p j x := E.decides p.val j x
  dense p j := by
    obtain ⟨r, hrp, x, hx⟩ := E.dense p.val j
    exact ⟨⟨r, hrp.trans p.property⟩, hrp, x, hx⟩
  persistent := fun hqp hx => E.persistent hqp hx
  unique := fun hx hy => E.unique hx hy

variable [LinearOrder I] [WellFoundedLT I]

/-- Mixed endpoint certificates retain singleton values exactly, while
pure lower-power pieces retain their strict upper/cofinal endpoint. -/
def RowPieceEndpoint (data : LineCoverData V) (n : ℕ)
    (E : FunctionDecisions P I V) (B : Set I) (i : W1) (p : P) (y : V) : Prop :=
  y ≤ data.cut i ∧ (∃ x : V, data.row x = i ∧ x ≤ y) ∧
    ((typeLT B = 1 ∧ ∀ r : P, r ≤ p → ∀ x : V, (pieceU E B).holds r x → x = y) ∨
      ∃ k : Fin n, typeLT B = (ω_ 1 : Ordinal.{0}) ^ ((k.val + 1 : ℕ) : Ordinal) ∧
        Upper (pieceU E B) p y ∧ CofinalBelow (pieceU E B) p y)

theorem rowPieceEndpoint_persistent {data : LineCoverData V}
    {E : FunctionDecisions P I V} {B : Set I} {i : W1} {p q : P} {y : V}
    (hqp : q ≤ p) (h : RowPieceEndpoint data n E B i p y) :
    RowPieceEndpoint data n E B i q y := by
  refine ⟨h.1, h.2.1, ?_⟩
  rcases h.2.2 with ⟨htype, hsingle⟩ | ⟨k, htype, hupper, hcofinal⟩
  · exact Or.inl ⟨htype, fun r hrq x hx => hsingle r (hrq.trans hqp) x hx⟩
  · exact Or.inr ⟨k, htype, upper_persistent hqp hupper, cofinalBelow_persistent hqp hcofinal⟩

/-- Every nonempty domain piece admits a row-witnessed endpoint densely.
Singleton endpoints are the actual value, not its successor. -/
theorem exists_rowPieceEndpoint (data : LineCoverData V)
    (E : FunctionDecisions P I V) (U : RegularName P V) (B : Set I) (i : W1)
    (hpiece : PowerPiece n B) (hne : B.Nonempty)
    (hmem : ∀ p j x, E.decides p j x → U.holds p x)
    (hrow : ∀ p x, U.holds p x → data.row x = i) (p0 : P) :
    ∃ q : P, q ≤ p0 ∧ ∃ y : V, RowPieceEndpoint data n E B i q y := by
  rcases hpiece with hsingle | ⟨k, hk, htype⟩
  · obtain ⟨q, hqp0, j, x, hx, hfrozen, -⟩ := exists_frozen_singleton_piece E B hsingle p0
    have hxrow : data.row x = i := hrow q x (hmem q j.val x hx)
    have hxcut : x < data.cut i := hxrow ▸ data.lt_cut_row x
    exact ⟨q, hqp0, x, hxcut.le, ⟨x, hxrow, le_rfl⟩,
      Or.inl ⟨hsingle, fun r hrq z hz => (hfrozen r hrq z).mp hz⟩⟩
  · have hbound : Upper (pieceU E B) p0 (data.cut i) := by
      intro p _ x hx
      have hxrow := hrow p x (pieceU_sub E U hmem B p x hx)
      exact hxrow ▸ data.lt_cut_row x
    obtain ⟨q, hqp0, y, hycut, hupper, hcofinal⟩ :=
      exists_cofinal_endpoint (pieceU E B) p0 (data.cut i) hbound
    obtain ⟨j, hj⟩ := hne
    obtain ⟨r, hrq, x, hx⟩ := (pieceE E B).dense q ⟨j, hj⟩
    have hxactual := pieceU_holds_of_decision E B hx
    have hxrow := hrow r x (pieceU_sub E U hmem B r x hxactual)
    have hxy : x < y := hupper r hrq x hxactual
    exact ⟨r, hrq.trans hqp0, y, hycut, ⟨x, hxrow, hxy.le⟩,
      Or.inr ⟨⟨k, hk⟩, htype, upper_persistent hrq hupper, cofinalBelow_persistent hrq hcofinal⟩⟩

/-- Once a piece endpoint is fixed, its actual range is either that
singleton or is covered by one of the named lower-power families. -/
theorem exists_piece_cover_at_endpoint (data : LineCoverData V)
    (L : NamedLowerCovers n V) (E : FunctionDecisions P I V) (B : Set I)
    (i : W1) (q : P) (y : V) (hclosed : CountablyClosed P)
    (hordered : OrderedDecisions E) (hendpoint : RowPieceEndpoint data n E B i q y) :
    ∃ F : FunctionDecisions (Set.Iic q) W1 W1,
      ∀ p : Set.Iic q, ∀ x : V, (pieceU E B).holds p.val x →
        x = y ∨ ∃ k : Fin n, (coverName F (L.into y k)).holds p x := by
  rcases hendpoint.2.2 with ⟨_, hsingle⟩ | ⟨k, htype, hupper, hcofinal⟩
  · refine ⟨FunctionDecisions.ofFunction (fun _ => Ordinal.ToType.mk ⟨0, Ordinal.omega_pos 1⟩), ?_⟩
    exact fun p x hx => Or.inl (hsingle p.val p.property x hx)
  · let source : RegularName (Set.Iic q) V := onCone q (pieceU E B)
    let decisions : FunctionDecisions (Set.Iic q) B V := onConeDecisions (pieceE E B) q
    have hdense : DenseCoverage decisions source := fun p x hx =>
      let ⟨r, hrp, j, hj⟩ := pieceU_denseCoverage E B p.val x hx
      ⟨⟨r, hrp.trans p.property⟩, hrp, j, hj⟩
    have hcof (p : Set.Iic q) : CofinalBelow source p y := fun r _ z hzy =>
      let ⟨s, hsr, x, hx, hzx, hxy⟩ := hcofinal r.val r.property z hzy
      ⟨⟨s, hsr.trans r.property⟩, hsr, x, hx, hzx, hxy⟩
    obtain ⟨F, hF⟩ := L.named_covers y k (Set.Iic q) B
      (Erdos1172Part3ClosedDenseRequirements.countablyClosed_Iic hclosed q)
      source decisions htype (fun hjk hx hz => pieceE_ordered E hordered B hjk hx hz)
      hdense (fun _ _ _ hx => pieceU_holds_of_decision E B hx)
      (fun p x hx => hupper p.val p.property x hx) hcof
    exact ⟨F, fun p x hx => Or.inr ⟨k, hF p x hx⟩⟩

/-- A short exact row enumeration yields, after strengthening, a
countable ground endpoint support and one lower-cover function name.
All covering functions remain genuine decision names. -/
theorem exists_localRowCover (data : LineCoverData V) (L : NamedLowerCovers n V)
    (U : RegularName P V) (E : FunctionDecisions P I V) (i : W1)
    (hclosed : CountablyClosed P) (p0 : P)
    (htype : typeLT I < (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal))
    (hordered : OrderedDecisions E) (hcoverage : DenseCoverage E U)
    (hmem : ∀ p j x, E.decides p j x → U.holds p x)
    (hrow : ∀ p x, U.holds p x → data.row x = i) :
    ∃ q : P, q ≤ p0 ∧ Nonempty (LocalRowCover data L.toLowerCovers U i q) := by
  classical
  obtain ⟨D, hDcount, hDcover, hpieces, -, -⟩ :=
    exists_named_domain_pieces n E U hordered hcoverage hmem htype
  have hDcard : #D ≤ ℵ₀ := Cardinal.le_aleph0_iff_set_countable.mpr hDcount
  obtain ⟨Dname, hDname⟩ :=
    Erdos1172Part3DecisionSelection.exists_function_decisions_of_dense
      (fun p (B : D) y => RowPieceEndpoint data n E B.val i p y)
      (fun hqp h => rowPieceEndpoint_persistent hqp h)
      (fun p B => exists_rowPieceEndpoint data E U B.val i
        (hpieces B.val B.property).2.1 (hpieces B.val B.property).1 hmem hrow p)
  obtain ⟨q, hqp0, hvalues⟩ := Dname.exists_simultaneous hclosed p0 hDcard
  let endpoint (B : D) : V := (hvalues B).choose
  have hendpoint (B : D) : RowPieceEndpoint data n E B.val i q (endpoint B) :=
    hDname q B (endpoint B) (hvalues B).choose_spec
  choose F hF using fun B : D =>
    exists_piece_cover_at_endpoint data L E B.val i q (endpoint B) hclosed hordered (hendpoint B)
  obtain ⟨R, hR⟩ := Erdos1172Part3NamedCoverBounds.exists_pointwise_upper
    (Erdos1172Part3ClosedDenseRequirements.countablyClosed_Iic hclosed q) F hDcard
  refine ⟨q, hqp0, ⟨{
    endpoints := Set.range endpoint
    countable := Cardinal.le_aleph0_iff_set_countable.mp (Cardinal.mk_range_le.trans hDcard)
    endpoint_le := by rintro _ ⟨B, rfl⟩; exact (hendpoint B).1
    row_witness := by rintro _ ⟨B, rfl⟩; exact (hendpoint B).2.1
    functionName := R
    covered := fun p x hx _ => ?_ }⟩⟩
  obtain ⟨r, hrp, B, hBD, j, hj⟩ := exists_decision_in_piece E U hcoverage D hDcover p.val x hx
  let s : Set.Iic q := ⟨r, hrp.trans p.property⟩
  rcases hF ⟨B, hBD⟩ s x (pieceU_holds_of_decision E B hj) with hsingle | ⟨k, hcover⟩
  · exact ⟨s, hrp, Or.inl ⟨⟨B, hBD⟩, hsingle.symm⟩⟩
  · exact ⟨s, hrp, Or.inr ⟨endpoint ⟨B, hBD⟩, Set.mem_range_self (⟨B, hBD⟩ : D), k,
      coverName_mono_of_pointwiseBelow (hR ⟨B, hBD⟩ s) hcover⟩⟩

end Erdos1172Part3NamedLocalRowCover
