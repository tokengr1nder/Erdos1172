/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CofinalPowerCoverCoverage

@[expose] public section

/-!
# Constructed monotone cofinal covers at every finite power

Strong induction supplies all lower-dimensional cover families. The
assembled two-dimensional profile is coded into one omegaOne function.
Thus every small well-order with a cofinal omegaOne^(n+1) subset has a
monotone family of exact cofinal covers containing every such subset.
There is no CH, domination, or lower-cover hypothesis in the final result.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3CofinalPowerCovers

open ErdosRadoCHAsym (W1)
open Erdos1172Part3CofinalPowerEndpoints (below)
open Erdos1172Part3CofinalPowerCoverAssembly (LowerCovers)
open Erdos1172Part3CofinalCoverSupport (FinitelySupported)

structure CofinalCovers (n : ℕ) (V : Type) [LinearOrder V] [WellFoundedLT V] where
  family : (W1 → W1) → Set V
  mono : Monotone family
  supported : FinitelySupported family
  cofinal : ∀ f, IsCofinal (family f)
  orderType : ∀ f, typeLT (family f) = (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal)
  covers : ∀ A : Set V, IsCofinal A →
    typeLT A = (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal) →
      ∃ f : W1 → W1, A ⊆ family f

variable {V : Type} [LinearOrder V] [WellFoundedLT V]

theorem exists_lowerCovers (n : ℕ)
    (hprovide : ∀ (y : V) (k : Fin n),
      (∃ B : Set (Set.Iio y), IsCofinal B ∧
        typeLT B = (ω_ 1 : Ordinal.{0}) ^ ((k.val + 1 : ℕ) : Ordinal)) →
          Nonempty (CofinalCovers k.val (Set.Iio y))) :
    Nonempty (LowerCovers n V) := by
  classical
  have hlocal (y : V) (k : Fin n) :
      ∃ C : (W1 → W1) → Set (Set.Iio y), Monotone C ∧ FinitelySupported C ∧
        (∀ f, typeLT (C f) ≤ (ω_ 1 : Ordinal.{0}) ^ ((k.val + 1 : ℕ) : Ordinal)) ∧
        ∀ B : Set (Set.Iio y), IsCofinal B →
          typeLT B = (ω_ 1 : Ordinal.{0}) ^ ((k.val + 1 : ℕ) : Ordinal) →
            ∃ f : W1 → W1, B ⊆ C f := by
    by_cases hseed : ∃ B : Set (Set.Iio y), IsCofinal B ∧
        typeLT B = (ω_ 1 : Ordinal.{0}) ^ ((k.val + 1 : ℕ) : Ordinal)
    · obtain ⟨C⟩ := hprovide y k hseed
      exact ⟨C.family, C.mono, C.supported, fun f => (C.orderType f).le, C.covers⟩
    · refine ⟨fun _ => ∅, fun _ _ _ => Set.Subset.rfl,
        Erdos1172Part3CofinalCoverSupport.constant_supported ∅, ?_, ?_⟩
      · intro f
        rw [Ordinal.type_eq_zero_of_empty]
        exact zero_le
      · intro B hB htype
        exact (hseed ⟨B, hB, htype⟩).elim
  choose C hmono hsupported htype hcov using hlocal
  refine ⟨{
    into := fun y k f => Subtype.val '' C y k f
    inside := ?_
    mono := ?_
    supported := fun y k => Erdos1172Part3CofinalCoverSupport.image_supported
      (C y k) (hsupported y k) Subtype.val
    type_le := ?_
    covers := ?_ }⟩
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

theorem exists_cofinalCovers (n : ℕ) :
    ∀ (V : Type) [LinearOrder V] [WellFoundedLT V], #V ≤ ℵ_ 1 →
      (∃ A : Set V, IsCofinal A ∧
        typeLT A = (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal)) →
          Nonempty (CofinalCovers n V) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V instOrder instWF hV hseed
    obtain ⟨seed, hseed, hseedType⟩ := hseed
    obtain ⟨data⟩ := Erdos1172Part3CofinalFiniteCuts.exists_finite_power_lineCutData
      hV n seed hseed hseedType
    obtain ⟨L⟩ := exists_lowerCovers n (fun y k hlocal =>
      ih k.val k.isLt (Set.Iio y) ((Cardinal.mk_set_le (Set.Iio y)).trans hV) hlocal)
    refine ⟨{
      family := fun f => Erdos1172Part3CofinalPowerCoverAssembly.cover data L seed
        (Erdos1172Part3CoverProfileTools.decode f)
      mono := (Erdos1172Part3CofinalPowerCoverAssembly.cover_mono data L seed).comp
        Erdos1172Part3CoverProfileTools.decode_mono
      supported := Erdos1172Part3CofinalCoverSupport.precompose_supported
        Erdos1172Part3CoverProfileTools.profileRank
        (Erdos1172Part3CofinalPowerCoverAssembly.cover data L seed)
        (Erdos1172Part3CofinalPowerCoverAssembly.cover_supported data L seed)
      cofinal := fun f => Erdos1172Part3CofinalPowerCoverAssembly.cover_cofinal data L seed hseed _
      orderType := fun f => Erdos1172Part3CofinalPowerCoverAssembly.cover_type data L seed hseed hseedType _
      covers := ?_ }⟩
    intro A hA htype
    obtain ⟨p, hp⟩ := Erdos1172Part3CofinalPowerCoverCoverage.exists_covering_profile
      data L seed A hA htype
    obtain ⟨f, hf⟩ := Erdos1172Part3CoverProfileTools.decode_surjective p
    exact ⟨f, by simpa only [hf] using hp⟩

theorem exists_monotone_cofinal_power_covers (n : ℕ) (hV : #V ≤ ℵ_ 1)
    (hseed : ∃ A : Set V, IsCofinal A ∧
      typeLT A = (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal)) :
    ∃ C : (W1 → W1) → Set V, Monotone C ∧
      (∀ f, IsCofinal (C f) ∧
        typeLT (C f) = (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal)) ∧
      ∀ A : Set V, IsCofinal A →
        typeLT A = (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal) →
          ∃ f : W1 → W1, A ⊆ C f := by
  obtain ⟨C⟩ := exists_cofinalCovers n V hV hseed
  exact ⟨C.family, C.mono, fun f => ⟨C.cofinal f, C.orderType f⟩, C.covers⟩

theorem exists_supported_cofinal_power_covers (n : ℕ) (hV : #V ≤ ℵ_ 1)
    (hseed : ∃ A : Set V, IsCofinal A ∧
      typeLT A = (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal)) :
    ∃ C : (W1 → W1) → Set V, Monotone C ∧ FinitelySupported C ∧
      (∀ f, IsCofinal (C f) ∧
        typeLT (C f) = (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal)) ∧
      ∀ A : Set V, IsCofinal A →
        typeLT A = (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal) →
          ∃ f : W1 → W1, A ⊆ C f := by
  obtain ⟨C⟩ := exists_cofinalCovers n V hV hseed
  exact ⟨C.family, C.mono, C.supported, fun f => ⟨C.cofinal f, C.orderType f⟩, C.covers⟩

end Erdos1172Part3CofinalPowerCovers
