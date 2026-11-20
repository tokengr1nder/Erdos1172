/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3StationarySquareDecisions

@[expose] public section

/-!
# Deriving square-row bounds from ordinal-small losses

A subset of omegaOne squared of smaller order type cannot have cofinally
many rows which are themselves cofinal. Past a bounded set of rows its
columns therefore have scalar bounds. Stationary pigeonhole freezes the
row cutoff, discharging the row-bound premise of the decision constructor.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3SquareLossBounds

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3HechlerOrder
open Erdos1172Part3StationarySquareDecisions
open Erdos1172Part3CenteredStationaryLoss (exists_stationary_fiber_of_small)

local instance : IsRegularCardinalOrder W1 := ⟨by
  rw [cof_W1, Cardinal.ord_aleph]
  simp only [W1, Ordinal.type_toType, le_refl]⟩

theorem typeLT_square : typeLT Square = (ω_ 1) ^ (2 : Ordinal.{0}) := by
  change Ordinal.type (Prod.Lex ((· < ·) : W1 → W1 → Prop)
    ((· < ·) : W1 → W1 → Prop)) = _
  rw [Ordinal.type_prod_lex]
  simp only [W1, Ordinal.type_toType]
  rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, Ordinal.opow_add_one, Ordinal.opow_one]

/-- Ordinal smallness permits uncountably many points, but only boundedly
many cofinal rows. No countability claim about the whole loss is used. -/
theorem exists_row_bounds_of_typeLT_lt_square (A : Set Square)
    (hA : typeLT A < (ω_ 1) ^ (2 : Ordinal.{0})) :
    ∃ cutoff : W1, ∃ f : W1 → W1, ∀ i : W1, cutoff < i →
      ∀ j : W1, toLex (i, j) ∈ A → j < f i := by
  classical
  let rows : Set W1 := {i | IsCofinal {j : W1 | toLex (i, j) ∈ A}}
  have hnot : ¬IsCofinal rows := by
    intro hrows
    let outer : W1 ≃o rows := Order.enum rows hrows
    let inner (i : W1) : W1 ≃o {j : W1 | toLex ((outer i).val, j) ∈ A} :=
      Order.enum _ (outer i).property
    let points (z : Square) : Square :=
      toLex ((outer (ofLex z).1).val, (inner (ofLex z).1 (ofLex z).2).val)
    have hstrict : StrictMono points := by
      intro x y hxy
      rw [Prod.Lex.lt_iff] at hxy ⊢
      rcases hxy with hout | ⟨heq, hin⟩
      · exact Or.inl (outer.strictMono hout)
      · refine Or.inr ⟨congrArg (fun i => (outer i).val) heq, ?_⟩
        dsimp only [points]
        rw [heq]
        exact (inner (ofLex y).1).strictMono hin
    have hsub : Set.range points ⊆ A := by
      rintro z ⟨x, rfl⟩
      exact (inner (ofLex x).1 (ofLex x).2).property
    have htype : typeLT (Set.range points) = (ω_ 1) ^ (2 : Ordinal.{0}) := by
      rw [Ordinal.typeLT_range_of_strictMono points hstrict, typeLT_square]
    exact ((Ordinal.type_mono hsub).trans_lt hA).ne htype
  obtain ⟨cutoff, hcutoff⟩ := not_isCofinal_iff.mp hnot
  have hbound (i : W1) (hi : cutoff < i) :
      ∃ b : W1, ∀ j : W1, toLex (i, j) ∈ A → j < b := by
    apply not_isCofinal_iff.mp
    exact fun hrow => (hcutoff i hrow).asymm hi
  let f (i : W1) : W1 := if hi : cutoff < i then (hbound i hi).choose else i
  refine ⟨cutoff, f, ?_⟩
  intro i hi j hj
  simpa only [f, dif_pos hi] using (hbound i hi).choose_spec j hj

theorem exists_blue_row_bounds (H : SimpleGraph W2) (core : Square → W2)
    (hcore : StrictMono core) (a : W2)
    (hloss : typeLT (Set.range core ∩ {x | H.Adj x a} : Set W2) <
      (ω_ 1) ^ (2 : Ordinal.{0})) :
    ∃ cutoff : W1, ∃ f : W1 → W1, ∀ i : W1, cutoff < i →
      ∀ j : W1, H.Adj (core (toLex (i, j))) a → j < f i := by
  let A : Set Square := {z | H.Adj (core z) a}
  have hA : typeLT A < (ω_ 1) ^ (2 : Ordinal.{0}) := by
    let f (z : A) : (Set.range core ∩ {x | H.Adj x a} : Set W2) :=
      ⟨core z.val, ⟨z.val, rfl⟩, z.property⟩
    have hf : StrictMono f := by
      intro x y hxy
      exact hcore hxy
    have hemb := (RelEmbedding.ofMonotone f hf).ordinal_type_le
    exact hemb.trans_lt hloss
  exact exists_row_bounds_of_typeLT_lt_square A hA

/-- The genuine ordinal-small loss premise suffices. The output keeps
the original red square as its point source and retains a stationary
future through persistent decisions. No whole-loss cardinal bound or
extra domination principle is assumed. -/
theorem exists_stationary_square_decisions_of_small_losses (hCH : CH) (p0 : Condition)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (core : Square → W2) (hcore : StrictMono core) (hred : G.IsClique (Set.range core))
    (S : Set W2) (hS : IsStationary S) (hafter : ∀ a ∈ S, ∀ z : Square, core z < a)
    (hloss : ∀ a ∈ S, typeLT (Set.range core ∩ {x | H.Adj x a} : Set W2) <
      (ω_ 1) ^ (2 : Ordinal.{0})) :
    ∃ sys : StationarySquareDecisions G S, sys.start ≤ p0 ∧
      ∀ q i x, sys.clique.decides q i x → x ∈ Set.range core := by
  classical
  have witness (a : S) := exists_blue_row_bounds H core hcore a.val (hloss a.val a.property)
  let chosen (a : S) : W1 := (witness a).choose
  have hsmall : #W1 < ℵ_ 2 := by
    simp only [W1, Cardinal.mk_toType, Ordinal.card_omega]
    exact Cardinal.aleph_lt_aleph.mpr (by norm_num)
  obtain ⟨cutoff, hfiber⟩ := exists_stationary_fiber_of_small hsmall hS chosen
  let T : Set W2 := {a | ∃ ha : a ∈ S, chosen ⟨a, ha⟩ = cutoff}
  have hTS : T ⊆ S := fun _ h => h.choose
  let F (a : W2) : W1 → W1 :=
    if ha : a ∈ S then (witness ⟨a, ha⟩).choose_spec.choose else id
  have hbounds : ∀ a ∈ T, ∀ i : W1, cutoff < i → ∀ j : W1,
      H.Adj (core (toLex (i, j))) a → j < F a i := by
    rintro a ⟨ha, heq⟩ i hi j hj
    have h := (witness ⟨a, ha⟩).choose_spec.choose_spec
    change (witness ⟨a, ha⟩).choose = cutoff at heq
    simpa only [F, dif_pos ha] using h i (heq.trans_lt hi) j hj
  obtain ⟨sys, hsys, hinside⟩ := exists_stationary_square_decisions_of_row_bounds hCH p0
    G H hcompl core hcore hred T hfiber (fun a ha => hafter a (hTS ha)) cutoff F hbounds
  exact ⟨⟨sys.start, sys.clique, sys.future, sys.persistent,
    fun q a ha => hTS (sys.subset_source q a ha), sys.stationary, sys.cross⟩, hsys, hinside⟩

end Erdos1172Part3SquareLossBounds
