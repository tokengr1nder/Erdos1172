/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedLocalRowCover
public import Erdos1172.Part3NamedRowInterval
public import Erdos1172.Part3ClosedDenseRequirements

@[expose] public section

/-!
# Dense local row covers for a cofinal pure-power name

Exact row intervals reduce each actual row of the original cofinal name
to a strictly shorter fixed ground enumeration domain. The local lower-rank
construction applies on that cone. Flattening the resulting nested cone
preserves function decisions and actual supported-cover membership.

Consequently every condition and row have a strengthening with a local
row cover for the same original source. Permanently empty rows use an
empty endpoint family. No named row decomposition is assumed as a premise.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedCofinalRowCovers

open ErdosRadoCHAsym (W1)
open Erdos1172Part3FiniteTraceSchemes (Index typeLT_index)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName)
open Erdos1172Part3RegularConeRestriction (onCone)
open Erdos1172Part3NamedCofinality (OrderedDecisions CofinalDecisions)
open Erdos1172Part3NamedFinalTail (DenseCoverage)
open Erdos1172Part3NamedRowInterval (rowName intervalE exists_exact_row_interval)
open Erdos1172Part3CofinalLineCover (LineCoverData)
open Erdos1172Part3CofinalPowerCoverAssembly (LowerCovers)
open Erdos1172Part3NamedLowerCovers (NamedLowerCovers)
open Erdos1172Part3NamedLocalRowCover (LocalRowCover exists_localRowCover)
open Erdos1172Part3SupportedCoverRealization (Certificate coverName)

variable {P I X : Type} [Preorder P]

/-- Regard a condition below r.val as a condition in the nested cone at r. -/
def nestCone {q : P} (r : Set.Iic q) (p : Set.Iic r.val) : Set.Iic r :=
  ⟨⟨p.val, p.property.trans r.property⟩, p.property⟩

/-- Forget only the redundant intermediate-cone proof. -/
def flattenCone {q : P} (r : Set.Iic q) (p : Set.Iic r) : Set.Iic r.val :=
  ⟨p.val.val, p.property⟩

/-- Pull back a function name along the exact nested-cone identification. -/
def flattenDecisions {q : P} (r : Set.Iic q)
    (F : FunctionDecisions (Set.Iic r) I X) : FunctionDecisions (Set.Iic r.val) I X where
  decides p i x := F.decides (nestCone r p) i x
  dense p i := by
    obtain ⟨s, hsp, x, hx⟩ := F.dense (nestCone r p) i
    exact ⟨flattenCone r s, hsp, x, hx⟩
  persistent hsp h := F.persistent hsp h
  unique hx hy := F.unique hx hy

/-- A finite certificate is unchanged by removing the redundant cone. -/
theorem certificate_flatten_iff {q : P} (r : Set.Iic q)
    (F : FunctionDecisions (Set.Iic r) W1 W1) (C : (W1 → W1) → Set X)
    (p : Set.Iic r.val) (x : X) :
    Certificate (flattenDecisions r F) C p x ↔ Certificate F C (nestCone r p) x := Iff.rfl

/-- The exact cone identification compares every refinement in both
directions, hence preserves actual regularized cover membership. -/
theorem coverName_flatten_iff {q : P} (r : Set.Iic q)
    (F : FunctionDecisions (Set.Iic r) W1 W1) (C : (W1 → W1) → Set X)
    (p : Set.Iic r.val) (x : X) :
    (coverName (flattenDecisions r F) C).holds p x ↔
      (coverName F C).holds (nestCone r p) x := by
  constructor
  · intro hx s hsp
    obtain ⟨t, hts, ht⟩ := hx (flattenCone r s) hsp
    exact ⟨nestCone r t, hts, ht⟩
  · intro hx s hsp
    obtain ⟨t, hts, ht⟩ := hx (nestCone r s) hsp
    exact ⟨flattenCone r t, hts, ht⟩

variable {V : Type} [LinearOrder V] [WellFoundedLT V] {n : ℕ}

/-- Lift a local row cover of the restricted row source back to a local
row cover of the original U. The row premise supplies the exact restriction. -/
def flattenRowCover (data : LineCoverData V) (L : LowerCovers n V)
    (U : RegularName P V) (i : W1) {q : P} (r : Set.Iic q)
    (R : LocalRowCover data L (onCone q (rowName data U i)) i r) :
    LocalRowCover data L U i r.val where
  endpoints := R.endpoints
  countable := R.countable
  endpoint_le := R.endpoint_le
  row_witness := R.row_witness
  functionName := flattenDecisions r R.functionName
  covered := by
    intro p x hx hrow
    obtain ⟨s, hsp, hs⟩ := R.covered (nestCone r p) x ⟨hx, hrow⟩ hrow
    refine ⟨flattenCone r s, hsp, ?_⟩
    rcases hs with hs | ⟨y, hy, k, hk⟩
    · exact Or.inl hs
    · exact Or.inr ⟨y, hy, k,
        (coverName_flatten_iff r R.functionName (L.into y k) (flattenCone r s) x).mpr hk⟩

/-- A permanently empty row has a vacuous local cover with no endpoints. -/
noncomputable def emptyRowCover (data : LineCoverData V) (L : LowerCovers n V)
    (U : RegularName P V) (i : W1) (q : P)
    (hempty : ∀ r : P, r ≤ q → ∀ x : V, ¬(rowName data U i).holds r x) :
    LocalRowCover data L U i q where
  endpoints := ∅
  countable := Set.countable_empty
  endpoint_le := by intro y hy; exact hy.elim
  row_witness := by intro y hy; exact hy.elim
  functionName := FunctionDecisions.ofFunction
    (fun _ => Ordinal.ToType.mk ⟨0, Ordinal.omega_pos 1⟩)
  covered := by
    intro p x hx hrow
    exact (hempty p.val p.property x ⟨hx, hrow⟩).elim

/-- Every row of the same original cofinal pure-power name admits local
row-cover data densely. Lower-rank named covers are the induction input;
the actual shorter row enumeration is constructed here. -/
theorem exists_cofinal_localRowCover (data : LineCoverData V)
    (L : NamedLowerCovers n V) (U : RegularName P V)
    (E : FunctionDecisions P (Index n) V) (hclosed : CountablyClosed P)
    (hordered : OrderedDecisions E) (hcofinal : CofinalDecisions E)
    (hcoverage : DenseCoverage E U) (hmem : ∀ p j x, E.decides p j x → U.holds p x)
    (p0 : P) (i : W1) :
    ∃ q : P, q ≤ p0 ∧ Nonempty (LocalRowCover data L.toLowerCovers U i q) := by
  obtain ⟨q, hqp0, hrow⟩ := exists_exact_row_interval data U E hordered hcofinal hmem hcoverage p0 i
  rcases hrow with hempty | ⟨a, b, _hab, hshort, hrowOrdered, hrowMem, hrowCoverage⟩
  · exact ⟨q, hqp0, ⟨emptyRowCover data L.toLowerCovers U i q hempty⟩⟩
  · obtain ⟨r, _hrtop, hR⟩ := exists_localRowCover data L (onCone q (rowName data U i))
      (intervalE E q a b) i
      (Erdos1172Part3ClosedDenseRequirements.countablyClosed_Iic hclosed q)
      ⟨q, le_rfl⟩ (hshort.trans_eq (typeLT_index n)) hrowOrdered hrowCoverage hrowMem
      (fun _ _ hx => hx.2)
    obtain ⟨R⟩ := hR
    exact ⟨r.val, r.property.trans hqp0, ⟨flattenRowCover data L.toLowerCovers U i r R⟩⟩

end Erdos1172Part3NamedCofinalRowCovers
