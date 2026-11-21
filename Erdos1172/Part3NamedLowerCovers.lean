/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedBoundedPiece
public import Erdos1172.Part3NamedCofinalRealization

@[expose] public section

/-!
# Aligned ground and named lower-power covers

The induction input supplies named cofinal covers at every strictly lower
rank. Their images in each endpoint order give one lower-cover family
with both its existing ground guarantees and actual named coverage.

If an endpoint order has no ground cofinal pure-power seed, it cannot
carry the corresponding ordered cofinal decision name on a nonempty
countably closed condition order. The proved cofinal realization theorem
discharges this branch; named completeness is not inferred from opaque
ground completeness.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedLowerCovers

open ErdosRadoCHAsym (W1)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName)
open Erdos1172Part3NamedCofinality (OrderedDecisions)
open Erdos1172Part3NamedFinalTail (DenseCoverage)
open Erdos1172Part3NamedCofinalEndpoint (CofinalBelow)
open Erdos1172Part3NamedCofinalCovers (NamedCofinalCovers)
open Erdos1172Part3NamedBoundedPiece
open Erdos1172Part3SupportedCoverRealization (coverName)
open Erdos1172Part3CofinalCoverSupport (FinitelySupported)
open Erdos1172Part3CofinalPowerCoverAssembly (LowerCovers)
open Erdos1172Part3CofinalPowerEndpoints (below)
open Erdos1172Part3FiniteTraceSchemes (Index typeLT_index mk_index_le)

variable {V : Type} [LinearOrder V] [WellFoundedLT V]

def BoundedNamedCoverage (k : ℕ) (y : V) (C : (W1 → W1) → Set V) : Prop :=
  ∀ (P I : Type) [Preorder P] [LinearOrder I] [WellFoundedLT I],
    CountablyClosed P → ∀ (U : RegularName P V) (E : FunctionDecisions P I V),
      typeLT I = (ω_ 1 : Ordinal.{0}) ^ ((k + 1 : ℕ) : Ordinal) →
      OrderedDecisions E → DenseCoverage E U →
      (∀ p i x, E.decides p i x → U.holds p x) →
      (∀ p x, U.holds p x → x < y) → (∀ p, CofinalBelow U p y) →
        ∃ F : FunctionDecisions P W1 W1,
          ∀ p x, U.holds p x → (coverName F C).holds p x

structure NamedLowerCovers (n : ℕ) (V : Type)
    [LinearOrder V] [WellFoundedLT V] extends LowerCovers n V where
  named_covers : ∀ y k, BoundedNamedCoverage k.val y (into y k)

theorem exists_namedLowerCovers (n : ℕ) (hV : #V ≤ ℵ_ 1)
    (hprovide : ∀ (y : V) (k : Fin n),
      (∃ B : Set (Set.Iio y), IsCofinal B ∧
        typeLT B = (ω_ 1 : Ordinal.{0}) ^ ((k.val + 1 : ℕ) : Ordinal)) →
          Nonempty (NamedCofinalCovers k.val (Set.Iio y))) :
    Nonempty (NamedLowerCovers n V) := by
  classical
  have hlocal (y : V) (k : Fin n) :
      ∃ C : (W1 → W1) → Set (Set.Iio y), Monotone C ∧ FinitelySupported C ∧
        (∀ f, typeLT (C f) ≤ (ω_ 1 : Ordinal.{0}) ^ ((k.val + 1 : ℕ) : Ordinal)) ∧
        (∀ B : Set (Set.Iio y), IsCofinal B →
          typeLT B = (ω_ 1 : Ordinal.{0}) ^ ((k.val + 1 : ℕ) : Ordinal) → ∃ f : W1 → W1, B ⊆ C f) ∧
        BoundedNamedCoverage k.val y (fun f => (Subtype.val : Set.Iio y → V) '' C f) := by
    by_cases hseed : ∃ B : Set (Set.Iio y), IsCofinal B ∧
        typeLT B = (ω_ 1 : Ordinal.{0}) ^ ((k.val + 1 : ℕ) : Ordinal)
    · obtain ⟨C⟩ := hprovide y k hseed
      refine ⟨C.family, C.mono, C.supported, fun f => (C.orderType f).le, C.covers, ?_⟩
      intro P I instP instI instWI hclosed U E htype hordered hcoverage hmem hbound hcofinal
      exact exists_named_cover_of_bounded_pure_piece k.val y C hclosed U E
        htype hordered hcoverage hmem hbound hcofinal
    · refine ⟨fun _ => ∅, fun _ _ _ => Set.Subset.rfl,
        Erdos1172Part3CofinalCoverSupport.constant_supported ∅, ?_, ?_, ?_⟩
      · intro f
        rw [Ordinal.type_eq_zero_of_empty]
        exact zero_le
      · intro B hB htype
        exact (hseed ⟨B, hB, htype⟩).elim
      · intro P I instP instI instWI hclosed U E htype hordered hcoverage hmem hbound hcofinal
        refine ⟨FunctionDecisions.ofFunction
          (fun _ => Ordinal.ToType.mk ⟨0, Ordinal.omega_pos 1⟩), ?_⟩
        intro p x _hx
        obtain ⟨G, hGorder, hGcofinal, -, -⟩ := exists_below_pure_enumeration k.val
          U E htype hordered hcoverage hmem y hbound hcofinal
        obtain ⟨A, hA, hAtype⟩ :=
          Erdos1172Part3NamedCofinalRealization.exists_ground_cofinal_set G hclosed p
            (mk_index_le k.val) ((Cardinal.mk_set_le (Set.Iio y)).trans hV) hGorder hGcofinal
        exact (hseed ⟨A, hA, hAtype.trans (typeLT_index k.val)⟩).elim
  choose C hmono hsupported htype hcov hnamed using hlocal
  refine ⟨{
    into := fun y k f => Subtype.val '' C y k f
    inside := ?_
    mono := ?_
    supported := fun y k => Erdos1172Part3CofinalCoverSupport.image_supported
      (C y k) (hsupported y k) Subtype.val
    type_le := ?_
    covers := ?_
    named_covers := hnamed }⟩
  · rintro y k f x ⟨z, _, rfl⟩
    exact z.property
  · intro y k f g hfg
    exact Set.image_mono (hmono y k hfg)
  · intro y k f
    have hf : StrictMono (Subtype.val : Set.Iio y → V) := fun _ _ h => h
    have heq : typeLT (C y k f) = typeLT ((Subtype.val : Set.Iio y → V) '' C y k f) :=
      ((hf.strictMonoOn (C y k f)).orderIso
        (Subtype.val : Set.Iio y → V) (C y k f)).ordinalType_congr
    exact heq.symm.trans_le (htype y k f)
  · intro y k B hsub hB hBtype
    obtain ⟨f, hf⟩ := hcov y k (below B y) hB hBtype
    exact ⟨f, fun x hx => ⟨⟨x, hsub hx⟩, hf hx, rfl⟩⟩

end Erdos1172Part3NamedLowerCovers
