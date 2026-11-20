/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.ForMathlib.Combinatorics.SimpleGraph.CliqueFamilyUnion
public import Mathlib.Order.Cofinal

@[expose] public section

/-!
# Exact final tails inside arbitrary well-ordered subsets

An ordinal sum decomposition of a subset is transported through an actual
order isomorphism. The right summand becomes a subset of exactly that order
type, and every discarded point precedes every retained point. If the right
summand is nonzero, a retained point bounds the discarded set. Cofinality
therefore transfers without any additional cofinality hypothesis on the
ambient well-order.
-/

open Ordinal Set Order

universe u

namespace Erdos1172Part3FinalTailSubset

variable {V : Type u} [LinearOrder V] [WellFoundedLT V]

/-- Extract the actual final summand, retaining strict separation from its
complement inside the original subset. The right summand may be zero. -/
theorem exists_final_tail (A : Set V) (ζ γ : Ordinal.{u})
    (htype : typeLT A = ζ + γ) :
    ∃ B : Set V, B ⊆ A ∧ typeLT B = γ ∧
      ∀ a ∈ A \ B, ∀ b ∈ B, a < b := by
  classical
  have hwf_lex : WellFounded (fun a b : ζ.ToType ⊕ₗ γ.ToType => a < b) := by
    refine Subrelation.wf (r := InvImage (Sum.Lex (· < ·) (· < ·)) ofLex) (fun h => h) ?_
    exact InvImage.wf ofLex (Sum.lex_wf wellFounded_lt wellFounded_lt)
  letI : WellFoundedLT (ζ.ToType ⊕ₗ γ.ToType) := hwf_lex
  have hsum : typeLT (ζ.ToType ⊕ₗ γ.ToType) = typeLT A := by
    calc
      typeLT (ζ.ToType ⊕ₗ γ.ToType) =
          (typeLT ζ.ToType) + (typeLT γ.ToType) := Ordinal.type_sum_lex _ _
      _ = ζ + γ := by rw [Ordinal.type_toType, Ordinal.type_toType]
      _ = typeLT A := htype.symm
  obtain ⟨e⟩ := Ordinal.type_eq.mp hsum
  let f : γ.ToType → V := fun i => (e (Sum.inrₗ i)).val
  have hf : StrictMono f := by
    intro i j hij
    exact e.map_rel_iff.mpr (Sum.Lex.inr_lt_inr_iff.mpr hij)
  refine ⟨Set.range f, ?_, ?_, ?_⟩
  · rintro a ⟨i, rfl⟩
    exact (e (Sum.inrₗ i)).property
  · rw [Ordinal.typeLT_range_of_strictMono f hf, Ordinal.type_toType]
  · intro a ha b hb
    rcases hb with ⟨j, rfl⟩
    obtain ⟨x, hx⟩ := e.surjective (⟨a, ha.1⟩ : A)
    induction x using Lex.rec with
    | _ x =>
      cases x with
      | inl i =>
        have hlt : (e (Sum.inlₗ i)).val < f j :=
          e.map_rel_iff.mpr (Sum.Lex.inl_lt_inr i j)
        simpa only [hx] using hlt
      | inr i =>
        exact False.elim (ha.2 ⟨i, congrArg (fun z : A => z.val) hx⟩)

/-- A nonempty final subset of a cofinal set is itself cofinal. -/
theorem isCofinal_of_nonempty_final_tail (A B : Set V)
    (hA : IsCofinal A) (hB : B.Nonempty)
    (hsep : ∀ a ∈ A \ B, ∀ b ∈ B, a < b) : IsCofinal B := by
  obtain ⟨b, hb⟩ := hB
  intro x
  obtain ⟨a, ha, hxa⟩ := hA x
  by_cases haB : a ∈ B
  · exact ⟨a, haB, hxa⟩
  · exact ⟨b, hb, hxa.trans (hsep a ⟨ha, haB⟩ b hb).le⟩

/-- A nonzero final summand discards a bounded set. The bound is an actual
retained point, rather than a bound in an ordinal completion. -/
theorem exists_bounded_final_tail (A : Set V) (ζ γ : Ordinal.{u})
    (hγ : 0 < γ) (htype : typeLT A = ζ + γ) :
    ∃ B : Set V, B ⊆ A ∧ typeLT B = γ ∧
      (∀ a ∈ A \ B, ∀ b ∈ B, a < b) ∧
      ∃ cut ∈ B, A \ B ⊆ Set.Iio cut := by
  obtain ⟨B, hBA, hBtype, hsep⟩ := exists_final_tail A ζ γ htype
  have hBzero : typeLT B ≠ 0 := by
    rw [hBtype]
    exact ne_of_gt hγ
  obtain ⟨b⟩ : Nonempty B := Ordinal.type_ne_zero_iff_nonempty.mp hBzero
  exact ⟨B, hBA, hBtype, hsep, b.val, b.property,
    fun a ha => hsep a ha b.val b.property⟩

/-- Transfer an exact nonzero ordinal tail to a cofinal subset while
keeping a bounded discarded prefix and the full final-segment separation. -/
theorem exists_cofinal_final_tail (A : Set V) (hA : IsCofinal A)
    (ζ γ : Ordinal.{u}) (hγ : 0 < γ) (htype : typeLT A = ζ + γ) :
    ∃ B : Set V, B ⊆ A ∧ typeLT B = γ ∧ IsCofinal B ∧
      (∀ a ∈ A \ B, ∀ b ∈ B, a < b) ∧
      ∃ cut ∈ B, A \ B ⊆ Set.Iio cut := by
  obtain ⟨B, hBA, hBtype, hsep, cut, hcut, hbound⟩ :=
    exists_bounded_final_tail A ζ γ hγ htype
  exact ⟨B, hBA, hBtype,
    isCofinal_of_nonempty_final_tail A B hA ⟨cut, hcut⟩ hsep,
    hsep, cut, hcut, hbound⟩

end Erdos1172Part3FinalTailSubset
