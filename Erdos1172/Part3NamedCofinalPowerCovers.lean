/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedCofinalRowCovers
public import Erdos1172.Part3NamedRowMixing
public import Erdos1172.Part3NamedEndpointSupport
public import Erdos1172.Part3NamedCoverAssembly

@[expose] public section

/-!
# Constructed named cofinal covers at every finite power

Strong induction constructs lower cover families that retain their ground
and named guarantees together. The actual shorter row enumerations give
dense local row covers; coherent antichain mixing gives row functions and
countable endpoint-set decisions. The endpoint name has a line cover, and
finite certificate assembly combines the head and row names.

The final theorem assumes only the small ambient well-order and a ground
cofinal seed of the stated exact type. Named coverage holds on every
countably closed condition order for every ordered, cofinal, exact regular
enumeration. No higher-rank named-cover principle remains as a premise.

This is a covering theorem, not yet the original Part 3 partition relation.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedCofinalPowerCovers

open ErdosRadoCHAsym (W1)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3FiniteTraceSchemes (Index)
open Erdos1172Part3NamedCofinality (OrderedDecisions CofinalDecisions)
open Erdos1172Part3NamedFinalTail (DenseCoverage)
open Erdos1172Part3CofinalLineCover (LineCoverData)
open Erdos1172Part3NamedCofinalCovers (NamedCofinalCovers)
open Erdos1172Part3NamedLowerCovers (NamedLowerCovers exists_namedLowerCovers)
open Erdos1172Part3SupportedCoverRealization (coverName)
open Erdos1172Part3NamedEndpointSupport
open Erdos1172Part3NamedCoverAssembly (family exists_assembled_name)

variable {P V : Type} [Preorder P] [LinearOrder V] [WellFoundedLT V] {n : ℕ}

/-- The assembled family covers every actual member of the cofinal name.
Lower named covers are used only at strictly smaller ranks. -/
theorem exists_named_cover_of_lower (data : LineCoverData V)
    (L : NamedLowerCovers n V) (seed : Set V) (U : RegularName P V)
    (E : FunctionDecisions P (Index n) V) (hclosed : CountablyClosed P)
    (hordered : OrderedDecisions E) (hcofinal : CofinalDecisions E)
    (hcoverage : DenseCoverage E U) (hmem : ∀ p j x, E.decides p j x → U.holds p x) :
    ∃ H : FunctionDecisions P W1 W1,
      ∀ p x, U.holds p x → (coverName H (family data L.toLowerCovers seed)).holds p x := by
  obtain ⟨B, R, hB, hcover⟩ := Erdos1172Part3NamedRowMixing.exists_mixed_row_covers
    data L.toLowerCovers U
    (Erdos1172Part3NamedCofinalRowCovers.exists_cofinal_localRowCover
      data L U E hclosed hordered hcofinal hcoverage hmem)
  obtain ⟨F, hF⟩ := exists_named_set_endpoint_head data B
    (fun p i S hS => ⟨(hB p i S hS).1, (hB p i S hS).2.2⟩) hclosed
  apply exists_assembled_name data L.toLowerCovers seed U F R
  intro p x hx
  obtain ⟨q, hqp, S, hS, hpiece⟩ := hcover p x hx
  refine ⟨q, hqp, Or.inr ?_⟩
  rcases hpiece with hxS | ⟨y, hyS, k, hk⟩
  · exact Or.inl (hF q x (setEndpoint_holds_of_decision B hS hxS))
  · exact Or.inr ⟨data.row x, y, k, rfl, (hB q (data.row x) S hS).2.1 y hyS,
      hF q y (setEndpoint_holds_of_decision B hS hyS), hk⟩

/-- At every finite rank the same constructed family has both ground
cofinal completeness and actual named cofinal completeness. -/
theorem exists_namedCofinalCovers (n : ℕ) :
    ∀ (V : Type) [LinearOrder V] [WellFoundedLT V], #V ≤ ℵ_ 1 →
      (∃ A : Set V, IsCofinal A ∧
        typeLT A = (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal)) →
          Nonempty (NamedCofinalCovers n V) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V instOrder instWF hV hseed
    obtain ⟨seed, hseed, hseedType⟩ := hseed
    obtain ⟨data⟩ := Erdos1172Part3CofinalFiniteCuts.exists_finite_power_lineCutData
      hV n seed hseed hseedType
    obtain ⟨L⟩ := exists_namedLowerCovers n hV (fun y k hlocal =>
      ih k.val k.isLt (Set.Iio y) ((Cardinal.mk_set_le (Set.Iio y)).trans hV) hlocal)
    refine ⟨{
      family := family data L.toLowerCovers seed
      mono := (Erdos1172Part3CofinalPowerCoverAssembly.cover_mono data L.toLowerCovers seed).comp
        Erdos1172Part3CoverProfileTools.decode_mono
      supported := Erdos1172Part3CofinalCoverSupport.precompose_supported
        Erdos1172Part3CoverProfileTools.profileRank
        (Erdos1172Part3CofinalPowerCoverAssembly.cover data L.toLowerCovers seed)
        (Erdos1172Part3CofinalPowerCoverAssembly.cover_supported data L.toLowerCovers seed)
      cofinal := fun f => Erdos1172Part3CofinalPowerCoverAssembly.cover_cofinal
        data L.toLowerCovers seed hseed _
      orderType := fun f => Erdos1172Part3CofinalPowerCoverAssembly.cover_type
        data L.toLowerCovers seed hseed hseedType _
      covers := ?_
      named_covers := ?_ }⟩
    · intro A hA htype
      obtain ⟨p, hp⟩ := Erdos1172Part3CofinalPowerCoverCoverage.exists_covering_profile
        data L.toLowerCovers seed A hA htype
      obtain ⟨f, hf⟩ := Erdos1172Part3CoverProfileTools.decode_surjective p
      exact ⟨f, by simpa only [family, hf] using hp⟩
    · intro P instP hclosed U E hordered hcofinal hcoverage hmem
      exact exists_named_cover_of_lower data L seed U E hclosed
        hordered hcofinal hcoverage hmem

end Erdos1172Part3NamedCofinalPowerCovers
