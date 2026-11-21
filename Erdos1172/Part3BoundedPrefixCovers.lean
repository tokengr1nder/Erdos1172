/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CofinalPowerCovers
public import Erdos1172.Part3FinalPowerTail
public import Erdos1172.Part3FinalTailSubset

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
  exact add_le_add_right (Ordinal.type_mono (show A ∩ Set.Ici cut ⊆ A from Set.inter_subset_left)) _

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

end Erdos1172Part3BoundedPrefixCovers
