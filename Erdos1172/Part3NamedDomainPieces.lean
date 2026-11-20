/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3FinitePowerDecomposition
public import Erdos1172.Part3NamedFinalTail
public import Erdos1172.Part3RegularConeRestriction

@[expose] public section

/-!
# Countable lower-power pieces of an exact named enumeration

Decompose the fixed ground domain, not a set of possible values. Each
domain piece retains its exact restricted decision system and regularized
range. These actual piece names are contained in the source, and their
dense union is exactly the source. Every piece is nonempty and has either
singleton type or a strictly lower finite pure-power type.

A singleton-domain piece can be decided and frozen to a ground singleton
throughout its resulting cone. No closure, endpoint selection, or named
covering principle is assumed in this module.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedDomainPieces

open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName join ground)
open Erdos1172Part3RegularConeRestriction (onCone)
open Erdos1172Part3NamedCofinality (OrderedDecisions)
open Erdos1172Part3NamedFinalTail
open Erdos1172Part3FinitePowerDecomposition (PowerPiece exists_countable_power_decomposition)

variable {P I V : Type} [Preorder P] [LinearOrder I]

/-- The exact restriction of E to a ground subset of its original domain. -/
def pieceE (E : FunctionDecisions P I V) (B : Set I) : FunctionDecisions P B V :=
  tailE E (OrderEmbedding.subtype B)

/-- Actual membership is the dense regularization of exact piece decisions. -/
def pieceU (E : FunctionDecisions P I V) (B : Set I) : RegularName P V :=
  tailU (J := B) E (OrderEmbedding.subtype B)

theorem pieceU_holds_of_decision (E : FunctionDecisions P I V) (B : Set I)
    {p : P} {j : B} {x : V} (hx : (pieceE E B).decides p j x) :
    (pieceU E B).holds p x :=
  tailU_holds_of_decision (J := B) E (OrderEmbedding.subtype B) hx

theorem pieceU_denseCoverage (E : FunctionDecisions P I V) (B : Set I) :
    DenseCoverage (pieceE E B) (pieceU E B) :=
  tailU_dense_coverage (J := B) E (OrderEmbedding.subtype B)

theorem pieceE_actual (E : FunctionDecisions P I V) (U : RegularName P V)
    (hmem : ∀ p j x, E.decides p j x → U.holds p x) (B : Set I) :
    ∀ p j x, (pieceE E B).decides p j x → U.holds p x :=
  fun p j x hx => hmem p j.val x hx

theorem pieceU_sub (E : FunctionDecisions P I V) (U : RegularName P V)
    (hmem : ∀ p j x, E.decides p j x → U.holds p x) (B : Set I) :
    ∀ p x, (pieceU E B).holds p x → U.holds p x :=
  tailU_sub (J := B) E U (OrderEmbedding.subtype B) hmem

/-- An exact source decision belongs to one of the ground domain pieces. -/
theorem exists_decision_in_piece (E : FunctionDecisions P I V) (U : RegularName P V)
    (hcoverage : DenseCoverage E U) (D : Set (Set I))
    (hDcover : ⋃₀ D = Set.univ) (p : P) (x : V) (hx : U.holds p x) :
    ∃ q : P, q ≤ p ∧ ∃ B ∈ D, ∃ j : B, (pieceE E B).decides q j x := by
  obtain ⟨q, hqp, i, hi⟩ := hcoverage p x hx
  have hiD : i ∈ ⋃₀ D := by rw [hDcover]; exact Set.mem_univ i
  obtain ⟨B, hBD, hiB⟩ := hiD
  exact ⟨q, hqp, B, hBD, ⟨i, hiB⟩, hi⟩

/-- Exact piece decisions are available below every refinement of an
actual source membership, not just at one compatible condition. -/
theorem dense_decisions_in_pieces (E : FunctionDecisions P I V) (U : RegularName P V)
    (hcoverage : DenseCoverage E U) (D : Set (Set I)) (hDcover : ⋃₀ D = Set.univ)
    (p : P) (x : V) (hx : U.holds p x) :
    ∀ q : P, q ≤ p → ∃ r : P, r ≤ q ∧ ∃ B ∈ D,
      ∃ j : B, (pieceE E B).decides r j x :=
  fun q hqp => exists_decision_in_piece E U hcoverage D hDcover q x (U.persistent hqp hx)

/-- The source is exactly the regularized union of its actual piece names. -/
theorem eq_join_pieces (E : FunctionDecisions P I V) (U : RegularName P V)
    (hcoverage : DenseCoverage E U) (hmem : ∀ p j x, E.decides p j x → U.holds p x)
    (D : Set (Set I)) (hDcover : ⋃₀ D = Set.univ) :
    U = join (fun B : D => pieceU E B.val) := by
  apply RegularName.ext
  intro p x
  constructor
  · intro hx q hqp
    obtain ⟨r, hrq, B, hBD, j, hj⟩ :=
      dense_decisions_in_pieces E U hcoverage D hDcover p x hx q hqp
    exact ⟨r, hrq, ⟨B, hBD⟩, pieceU_holds_of_decision E B hj⟩
  · intro hx
    apply U.of_dense p x
    intro q hqp
    obtain ⟨r, hrq, B, hB⟩ := hx q hqp
    exact ⟨r, hrq, pieceU_sub E U hmem B.val r x hB⟩

variable [LinearOrder V]

theorem pieceE_ordered (E : FunctionDecisions P I V) (hordered : OrderedDecisions E)
    (B : Set I) : OrderedDecisions (pieceE E B) :=
  tailE_ordered (J := B) E (OrderEmbedding.subtype B) hordered

variable [WellFoundedLT I]

/-- Every allowed pure piece is genuinely nonempty. -/
theorem powerPiece_nonempty {n : ℕ} {B : Set I} (h : PowerPiece n B) : B.Nonempty := by
  have hne : typeLT B ≠ 0 := by
    rcases h with hsingle | ⟨k, _, htype⟩
    · rw [hsingle]
      exact one_ne_zero
    · rw [htype]
      exact (Ordinal.opow_pos _ (Ordinal.omega_pos 1)).ne'
  obtain ⟨b⟩ : Nonempty B := Ordinal.type_ne_zero_iff_nonempty.mp hne
  exact ⟨b.val, b.property⟩

/-- The fixed shorter domain decomposes into countably many nonempty
pieces with their exact original index subsets retained. -/
theorem exists_named_domain_pieces (n : ℕ) (E : FunctionDecisions P I V)
    (U : RegularName P V) (hordered : OrderedDecisions E)
    (hcoverage : DenseCoverage E U) (hmem : ∀ p j x, E.decides p j x → U.holds p x)
    (htype : typeLT I < (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal)) :
    ∃ D : Set (Set I), D.Countable ∧ ⋃₀ D = Set.univ ∧
      (∀ B ∈ D, B.Nonempty ∧ PowerPiece n B ∧ OrderedDecisions (pieceE E B) ∧
        DenseCoverage (pieceE E B) (pieceU E B) ∧
          ∀ p j x, (pieceE E B).decides p j x → U.holds p x) ∧
      U = join (fun B : D => pieceU E B.val) ∧
      ∀ p x, U.holds p x → ∀ q : P, q ≤ p →
        ∃ r : P, r ≤ q ∧ ∃ B ∈ D, ∃ j : B, (pieceE E B).decides r j x := by
  have hunivType : typeLT (Set.univ : Set I) = typeLT I :=
    OrderIso.Set.univ.ordinalType_congr
  obtain ⟨D, hDcount, hDcover, hDpiece⟩ :=
    exists_countable_power_decomposition n (Set.univ : Set I) (hunivType.trans_lt htype)
  refine ⟨D, hDcount, hDcover, ?_, eq_join_pieces E U hcoverage hmem D hDcover,
    dense_decisions_in_pieces E U hcoverage D hDcover⟩
  intro B hBD
  exact ⟨powerPiece_nonempty (hDpiece B hBD), hDpiece B hBD, pieceE_ordered E hordered B,
    pieceU_denseCoverage E B, pieceE_actual E U hmem B⟩

/-- In an empty domain the nonempty-piece requirement forces the family
itself to be empty; no artificial singleton index is introduced. -/
theorem pieces_eq_empty_of_isEmpty [IsEmpty I] (D : Set (Set I))
    (hpieces : ∀ B ∈ D, B.Nonempty) : D = ∅ := by
  apply Set.Subset.antisymm _ (Set.empty_subset _)
  intro B hBD
  obtain ⟨i, _⟩ := hpieces B hBD
  exact isEmptyElim i

/-- Once the unique coordinate of a singleton-type domain is decided,
its actual regularized range is exactly that value throughout the cone. -/
theorem singleton_piece_frozen_of_decision (E : FunctionDecisions P I V) (B : Set I)
    (htype : typeLT B = 1) {q : P} {j : B} {x : V}
    (hx : (pieceE E B).decides q j x) :
    ∀ r : P, r ≤ q → ∀ z : V, (pieceU E B).holds r z ↔ z = x := by
  obtain ⟨uniqueB⟩ := Ordinal.type_eq_one_iff_unique.mp htype
  intro r hrq z
  constructor
  · intro hz
    obtain ⟨s, hsr, k, hk⟩ := hz r le_rfl
    have hkj : k = j := (uniqueB.uniq k).trans (uniqueB.uniq j).symm
    exact (pieceE E B).unique (hkj ▸ hk) ((pieceE E B).persistent (hsr.trans hrq) hx)
  · intro hzx
    subst z
    exact pieceU_holds_of_decision E B ((pieceE E B).persistent hrq hx)

/-- Decide the unique coordinate and expose both the exact singleton
membership law and equality with a ground singleton on the whole cone. -/
theorem exists_frozen_singleton_piece (E : FunctionDecisions P I V) (B : Set I)
    (htype : typeLT B = 1) (p0 : P) :
    ∃ q : P, q ≤ p0 ∧ ∃ j : B, ∃ x : V, (pieceE E B).decides q j x ∧
      (∀ r : P, r ≤ q → ∀ z : V, (pieceU E B).holds r z ↔ z = x) ∧
      onCone q (pieceU E B) = ground ({x} : Set V) := by
  obtain ⟨uniqueB⟩ := Ordinal.type_eq_one_iff_unique.mp htype
  let j : B := uniqueB.default
  obtain ⟨q, hqp0, x, hx⟩ := (pieceE E B).dense p0 j
  have hfrozen := singleton_piece_frozen_of_decision E B htype hx
  refine ⟨q, hqp0, j, x, hx, hfrozen, ?_⟩
  apply RegularName.ext
  intro r z
  exact hfrozen r.val r.property z

end Erdos1172Part3NamedDomainPieces
