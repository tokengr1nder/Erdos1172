/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CofinalPowerCovers
public import Erdos1172.Part3FinalPowerTail
public import Erdos1172.Part3FinalTailSubset
public import Erdos1172.Part3CenteredStationaryLoss

@[expose] public section

/-!
# Bounded-prefix profiles for short subsets of the omega-successor power

The cut and the finite exponent are retained as profile parameters.
For each fixed profile, membership has finite support and every cover
has order type strictly below omegaOne^(omega+1).
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3BoundedPrefixCovers

open ErdosRadoCHAsym (W1)
open Erdos1172Part3CofinalCoverSupport
open Erdos1172Part3CofinalPowerCovers

variable {V : Type} [LinearOrder V] [WellFoundedLT V]

/-- A cofinal-cover family with an empty fallback at exponents for which
the ambient order has no cofinal subset of that exact type. -/
structure OptionalCofinalCovers (n : ℕ) (V : Type) [LinearOrder V] [WellFoundedLT V] where
  family : (W1 → W1) → Set V
  mono : Monotone family
  supported : FinitelySupported family
  type_le : ∀ f, typeLT (family f) ≤ (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal)
  covers : ∀ A : Set V, IsCofinal A →
    typeLT A = (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal) →
      ∃ f : W1 → W1, A ⊆ family f

theorem exists_optionalCofinalCovers (hV : #V ≤ ℵ_ 1) (n : ℕ) :
    Nonempty (OptionalCofinalCovers n V) := by
  classical
  by_cases hseed : ∃ A : Set V, IsCofinal A ∧
      typeLT A = (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal)
  · obtain ⟨C⟩ := exists_cofinalCovers n V hV hseed
    exact ⟨⟨C.family, C.mono, C.supported, fun f => (C.orderType f).le, C.covers⟩⟩
  · refine ⟨⟨fun _ => ∅, fun _ _ _ => Set.Subset.rfl,
      constant_supported ∅, ?_, ?_⟩⟩
    · intro f
      rw [Ordinal.type_eq_zero_of_empty]
      exact zero_le
    · intro A hA htype
      exact (hseed ⟨A, hA, htype⟩).elim

def withPrefix {n : ℕ} (C : OptionalCofinalCovers n V) (cut : V) (f : W1 → W1) : Set V :=
  Set.Iio cut ∪ C.family f

theorem withPrefix_mono {n : ℕ} (C : OptionalCofinalCovers n V) (cut : V) :
    Monotone (withPrefix C cut) := by
  intro f g hfg
  exact Set.union_subset_union_right _ (C.mono hfg)

theorem withPrefix_supported {n : ℕ} (C : OptionalCofinalCovers n V) (cut : V) :
    FinitelySupported (withPrefix C cut) :=
  union_supported _ _ (constant_supported _) C.supported

theorem typeLT_prefix_union_le (cut : V) (A : Set V) :
    typeLT (Set.Iio cut ∪ A : Set V) ≤ typeLT (Set.Iio cut) + typeLT A := by
  have heq : (Set.Iio cut ∪ A : Set V) = Set.Iio cut ∪ (A ∩ Set.Ici cut) := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact Or.inl hx
      · by_cases hxc : x < cut
        · exact Or.inl hxc
        · exact Or.inr ⟨hx, le_of_not_gt hxc⟩
    · rintro (hx | hx)
      · exact Or.inl hx
      · exact Or.inr hx.1
  rw [heq, Ordinal.typeLT_union_of_forall_lt (fun x hx y hy => hx.trans_le hy.2)]
  exact add_le_add_right (Ordinal.type_mono
    (show A ∩ Set.Ici cut ⊆ A from Set.inter_subset_left)) _

theorem withPrefix_type_lt {n : ℕ} (C : OptionalCofinalCovers n V) (cut : V)
    (hV : typeLT V = (ω_ 1 : Ordinal.{0}) ^ (ω + 1)) (f : W1 → W1) :
    typeLT (withPrefix C cut f) < (ω_ 1 : Ordinal.{0}) ^ (ω + 1) := by
  have hcut : typeLT (Set.Iio cut) < (ω_ 1 : Ordinal.{0}) ^ (ω + 1) := by
    rw [Ordinal.type_Iio_lt]
    exact (Ordinal.typein_lt_type _ cut).trans_eq hV
  have hpower : (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal) <
      (ω_ 1 : Ordinal.{0}) ^ (ω + 1) := by
    apply (Ordinal.opow_lt_opow_iff_right
      (Ordinal.one_lt_omega0.trans_le (Ordinal.omega0_le_omega 1))).mpr
    exact (Ordinal.natCast_lt_omega0 (n + 1)).trans_le le_self_add
  exact (typeLT_prefix_union_le cut (C.family f)).trans_lt
    (Ordinal.isPrincipal_add_opow_of_isPrincipal_add (Ordinal.isPrincipal_add_omega 1) _
      hcut ((C.type_le f).trans_lt hpower))

theorem withPrefix_covers_tail {n : ℕ} (C : OptionalCofinalCovers n V)
    (cut : V) (A B : Set V) (hB : IsCofinal B)
    (htype : typeLT B = (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal))
    (hrest : A \ B ⊆ Set.Iio cut) :
    ∃ f : W1 → W1, A ⊆ withPrefix C cut f := by
  classical
  obtain ⟨f, hf⟩ := C.covers B hB htype
  refine ⟨f, fun x hx => ?_⟩
  by_cases hxB : x ∈ B
  · exact Or.inr (hf hxB)
  · exact Or.inl (hrest ⟨hx, hxB⟩)

/-- Every short cofinal subset has one exact finite-power final tail. -/
theorem exists_cofinal_power_tail (hV : typeLT V = (ω_ 1 : Ordinal.{0}) ^ (ω + 1))
    (A : Set V) (hA : IsCofinal A)
    (hsmall : typeLT A < (ω_ 1 : Ordinal.{0}) ^ (ω + 1)) :
    ∃ n : ℕ, ∃ B : Set V, B ⊆ A ∧ IsCofinal B ∧
      typeLT B = (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal) ∧
      ∃ cut : V, A \ B ⊆ Set.Iio cut := by
  have hcof : (typeLT A).cof = ℵ_ 1 := by
    rw [Ordinal.cof_type, Order.cof_eq_of_isCofinal hA, ← Ordinal.cof_type V, hV]
    exact Erdos1172Part3FinalPowerTail.cof_omegaSuccessor
  obtain ⟨ζ, n, htail⟩ := Erdos1172Part3FinalPowerTail.exists_final_power_tail hsmall hcof
  obtain ⟨B, hBA, hBtype, hBcof, -, cut, -, hbound⟩ :=
    Erdos1172Part3FinalTailSubset.exists_cofinal_final_tail A hA ζ _
      (Ordinal.opow_pos _ (Ordinal.omega_pos 1)) htail
  exact ⟨n, B, hBA, hBcof, hBtype, cut, hbound⟩

omit [LinearOrder V] [WellFoundedLT V] in
theorem mk_profiles_le (hV : #V ≤ ℵ_ 1) : #(V × ℕ) ≤ ℵ_ 1 := by
  simp only [Cardinal.mk_prod, Cardinal.mk_nat, Cardinal.lift_id]
  exact (mul_le_mul' hV (Cardinal.aleph0_le_aleph 1)).trans_eq
    (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1))

/-- All strictly short subsets are covered by finitely supported families
with at most alephOne profiles. There is no CH or ground domination premise.
This is a ground-set covering theorem, not yet its named analogue. -/
theorem exists_supported_short_covers (hcard : #V ≤ ℵ_ 1)
    (htype : typeLT V = (ω_ 1 : Ordinal.{0}) ^ (ω + 1)) :
    ∃ C : (V × ℕ) → (W1 → W1) → Set V,
      (∀ e, Monotone (C e) ∧ FinitelySupported (C e) ∧
        ∀ f, typeLT (C e f) < (ω_ 1 : Ordinal.{0}) ^ (ω + 1)) ∧
      ∀ A : Set V, typeLT A < (ω_ 1 : Ordinal.{0}) ^ (ω + 1) →
        ∃ e : V × ℕ, ∃ f : W1 → W1, A ⊆ C e f := by
  classical
  let L (n : ℕ) : OptionalCofinalCovers n V :=
    Classical.choice (exists_optionalCofinalCovers hcard n)
  refine ⟨fun e => withPrefix (L e.2) e.1, ?_, ?_⟩
  · intro e
    exact ⟨withPrefix_mono _ _, withPrefix_supported _ _,
      withPrefix_type_lt _ _ htype⟩
  · intro A hsmall
    by_cases hA : IsCofinal A
    · obtain ⟨n, B, -, hB, hBtype, cut, hbound⟩ :=
        exists_cofinal_power_tail htype A hA hsmall
      obtain ⟨f, hf⟩ := withPrefix_covers_tail (L n) cut A B hB hBtype hbound
      exact ⟨(cut, n), f, hf⟩
    · obtain ⟨cut, hcut⟩ := not_forall.mp hA
      have hbound : A ⊆ Set.Iio cut := by
        intro x hx
        apply lt_of_not_ge
        exact fun hcx => hcut ⟨x, hx, hcx⟩
      exact ⟨(cut, 0), fun _ => Ordinal.ToType.mk ⟨0, Ordinal.omega_pos 1⟩,
        fun x hx => Or.inl (hbound hx)⟩

/-- A stationary family of short ground subsets has one common profile.
The functions may still vary with the member of the stationary family. -/
theorem exists_stationary_supported_short_covers (hcard : #V ≤ ℵ_ 1)
    (htype : typeLT V = (ω_ 1 : Ordinal.{0}) ^ (ω + 1))
    (S : Set ErdosRadoCHAsym.W2) (hS : IsStationary S)
    (A : ErdosRadoCHAsym.W2 → Set V)
    (hA : ∀ a ∈ S, typeLT (A a) < (ω_ 1 : Ordinal.{0}) ^ (ω + 1)) :
    ∃ T : Set ErdosRadoCHAsym.W2, T ⊆ S ∧ IsStationary T ∧
      ∃ C : (W1 → W1) → Set V, Monotone C ∧ FinitelySupported C ∧
        (∀ f, typeLT (C f) < (ω_ 1 : Ordinal.{0}) ^ (ω + 1)) ∧
        ∀ a ∈ T, ∃ f : W1 → W1, A a ⊆ C f := by
  classical
  obtain ⟨C, hC, hcover⟩ := exists_supported_short_covers hcard htype
  have hwitness (a : S) := hcover (A a.val) (hA a.val a.property)
  choose profile f hf using hwitness
  have hsmall : #(V × ℕ) < ℵ_ 2 := (mk_profiles_le hcard).trans_lt
    (Cardinal.aleph_lt_aleph.mpr (by norm_num : (1 : Ordinal.{0}) < 2))
  obtain ⟨e, he⟩ := Erdos1172Part3CenteredStationaryLoss.exists_stationary_fiber_of_small
    hsmall hS profile
  refine ⟨{a | ∃ ha : a ∈ S, profile ⟨a, ha⟩ = e}, ?_, he,
    C e, (hC e).1, (hC e).2.1, (hC e).2.2, ?_⟩
  · rintro a ⟨ha, -⟩
    exact ha
  · rintro a ⟨ha, heq⟩
    exact ⟨f ⟨a, ha⟩, heq ▸ hf ⟨a, ha⟩⟩

end Erdos1172Part3BoundedPrefixCovers
