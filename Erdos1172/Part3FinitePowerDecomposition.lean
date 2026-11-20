/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3FiniteOrderTypeIdeal

@[expose] public section

/-!
# Countable pure-power decomposition below a finite omegaOne power

Every subset of a well-order with type below omegaOne^(n+1) is covered
exactly by a countable family of singleton-type pieces and pieces of
type omegaOne^(k+1), k < n. The construction uses a principal-segment
embedding into the finite lexicographic index; no decomposition data
are assumed. This is the lower-power block decomposition needed in
the induction for arbitrary cofinal covers.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3FinitePowerDecomposition

open ErdosRadoCHAsym (W1)
open Erdos1172Part3FiniteTraceSchemes (Index typeLT_index)

variable {V : Type} [LinearOrder V] [WellFoundedLT V]

def PowerPiece (n : ℕ) (A : Set V) : Prop :=
  typeLT A = 1 ∨ ∃ k : ℕ, k < n ∧ typeLT A = (ω_ 1 : Ordinal.{0}) ^ ((k + 1 : ℕ) : Ordinal)

theorem powerPiece_mono {n m : ℕ} (hnm : n ≤ m) {A : Set V}
    (h : PowerPiece n A) : PowerPiece m A := by
  rcases h with h | ⟨k, hk, htype⟩
  · exact Or.inl h
  · exact Or.inr ⟨k, hk.trans_le hnm, htype⟩

theorem exists_countable_power_decomposition (n : ℕ) (A : Set V)
    (hA : typeLT A < (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal)) :
    ∃ D : Set (Set V), D.Countable ∧ ⋃₀ D = A ∧ ∀ B ∈ D, PowerPiece n B := by
  classical
  induction n generalizing A with
  | zero =>
    have hcount : A.Countable := by
      have hlt : typeLT A < ω_ 1 := by simpa only [Nat.zero_add, Nat.cast_one, Ordinal.opow_one] using hA
      rw [Cardinal.lt_omega_iff_card_lt, Ordinal.card_type] at hlt
      exact Cardinal.le_aleph0_iff_set_countable.mp (Cardinal.lt_aleph_one_iff.mp hlt)
    refine ⟨(fun x : V => ({x} : Set V)) '' A, hcount.image _, ?_, ?_⟩
    · ext x
      simp
    · rintro B ⟨x, _, rfl⟩
      exact Or.inl (Ordinal.type_eq_one_of_unique _)
  | succ n ih =>
    have htype : typeLT A < typeLT (Index (n + 1)) := by
      rw [typeLT_index]
      exact hA
    obtain ⟨e⟩ := Ordinal.type_lt_iff.mp htype
    let topRow : W1 := (ofLex e.top).1
    let row (i : W1) : Set V := {x | ∃ hx : x ∈ A, (ofLex (e ⟨x, hx⟩)).1 = i}
    have hrowSub (i : W1) : row i ⊆ A := fun _ hx => hx.choose
    have hrowType (i : W1) : typeLT (row i) ≤ (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal) := by
      let point (x : row i) : A := ⟨x.val, x.property.choose⟩
      have hfirst (x : row i) : (ofLex (e (point x))).1 = i := x.property.choose_spec
      let f : row i → Index n := fun x => (ofLex (e (point x))).2
      have hf : StrictMono f := by
        intro x y hxy
        have hexy : e (point x) < e (point y) := e.map_rel_iff.mpr hxy
        rw [Prod.Lex.lt_iff, hfirst x, hfirst y] at hexy
        exact hexy.resolve_left (lt_irrefl i) |>.2
      have hle := (RelEmbedding.ofMonotone f hf).ordinal_type_le
      exact hle.trans_eq (typeLT_index n)
    have hrows : (Set.Iic topRow).Countable :=
      Cardinal.le_aleph0_iff_set_countable.mp (Cardinal.lt_aleph_one_iff.mp
        (Erdos1172Part3ConvergentCore.mk_Iic_W1_lt topRow))
    have hrowCover : (⋃ i ∈ Set.Iic topRow, row i) = A := by
      apply Set.Subset.antisymm
      · rintro x hx
        obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
        obtain ⟨_, hx⟩ := Set.mem_iUnion.mp hx
        exact hrowSub i hx
      · intro x hx
        let i : W1 := (ofLex (e ⟨x, hx⟩)).1
        have hi : i ≤ topRow := by
          have hlt := e.lt_top (⟨x, hx⟩ : A)
          rw [Prod.Lex.lt_iff] at hlt
          exact hlt.elim (fun h => h.le) (fun h => h.1.le)
        exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hx, rfl⟩⟩
    have hpieces (i : W1) : ∃ D : Set (Set V), D.Countable ∧ ⋃₀ D = row i ∧
        ∀ B ∈ D, PowerPiece (n + 1) B := by
      rcases lt_or_eq_of_le (hrowType i) with hlt | heq
      · obtain ⟨D, hD, hcov, hpiece⟩ := ih (row i) hlt
        exact ⟨D, hD, hcov, fun B hB => powerPiece_mono (Nat.le_succ n) (hpiece B hB)⟩
      · exact ⟨{row i}, Set.countable_singleton _, by simp,
          fun B hB => by
            have he : B = row i := Set.mem_singleton_iff.mp hB
            subst B
            exact Or.inr ⟨n, Nat.lt_succ_self n, heq⟩⟩
    choose pieces hpiecesCount hpiecesCover hpiecesType using hpieces
    refine ⟨⋃ i ∈ Set.Iic topRow, pieces i, hrows.biUnion (fun i _ => hpiecesCount i), ?_, ?_⟩
    · apply Set.Subset.antisymm
      · rintro x ⟨B, hB, hx⟩
        obtain ⟨i, hB⟩ := Set.mem_iUnion.mp hB
        obtain ⟨_, hB⟩ := Set.mem_iUnion.mp hB
        exact hrowSub i (hpiecesCover i ▸ Set.mem_sUnion.mpr ⟨B, hB, hx⟩)
      · intro x hx
        rw [← hrowCover] at hx
        obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
        obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hx
        rw [← hpiecesCover i] at hx
        obtain ⟨B, hB, hx⟩ := hx
        exact ⟨B, Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hB⟩⟩, hx⟩
    · intro B hB
      obtain ⟨i, hB⟩ := Set.mem_iUnion.mp hB
      obtain ⟨_, hB⟩ := Set.mem_iUnion.mp hB
      exact hpiecesType i B hB

end Erdos1172Part3FinitePowerDecomposition
