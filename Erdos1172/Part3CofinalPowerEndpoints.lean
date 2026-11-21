/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3FinitePowerDecomposition

@[expose] public section

/-!
# Actual cofinal endpoints for bounded pure-power pieces

A bounded subset of limit order type has a least upper bound in its
ambient well-order and is cofinal strictly below that endpoint. The
subtype below the endpoint retains the exact order type. Combined with
the finite decomposition, this supplies genuine lower-power cofinal
pieces, not just abstract embeddings of smaller ordinals.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3CofinalPowerEndpoints

variable {V : Type} [LinearOrder V] [WellFoundedLT V]

def below (A : Set V) (bound : V) : Set (Set.Iio bound) := {x | x.val ∈ A}

theorem below_type (A : Set V) (bound : V) (hsub : A ⊆ Set.Iio bound) :
    typeLT (below A bound) = typeLT A := by
  let e : A ≃o below A bound := {
    toFun x := ⟨⟨x.val, hsub x.property⟩, x.property⟩
    invFun x := ⟨x.val.val, x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_rel_iff' := Iff.rfl }
  exact e.ordinalType_congr.symm

theorem exists_cofinal_endpoint (A : Set V) (cut : V) (hbound : A ⊆ Set.Iio cut)
    (hlimit : IsSuccPrelimit (typeLT A)) :
    ∃ bound : V, bound ≤ cut ∧ A ⊆ Set.Iio bound ∧ IsCofinal (below A bound) := by
  classical
  let upper : Set V := {x | ∀ a ∈ A, a ≤ x}
  have hupper : upper.Nonempty := ⟨cut, fun a ha => (hbound ha).le⟩
  let bound : V := wellFounded_lt.min upper hupper
  have hbupper : ∀ a ∈ A, a ≤ bound := wellFounded_lt.min_mem upper hupper
  have hbleast (x : V) (hx : ∀ a ∈ A, a ≤ x) : bound ≤ x := wellFounded_lt.min_le (s := upper) hx
  let : NoMaxOrder A := Ordinal.isSuccPrelimit_type_lt_iff.mp hlimit
  have hsub : A ⊆ Set.Iio bound := by
    intro a ha
    obtain ⟨b, hab⟩ := exists_gt (⟨a, ha⟩ : A)
    change a < b.val at hab
    exact hab.trans_le (hbupper b.val b.property)
  refine ⟨bound, hbleast cut (fun a ha => (hbound ha).le), hsub, ?_⟩
  intro x
  have hnot : ¬∀ a ∈ A, a ≤ x.val := fun h => (hbleast x.val h).not_gt x.property
  push Not at hnot
  obtain ⟨a, ha, hxa⟩ := hnot
  exact ⟨⟨a, hsub ha⟩, ha, hxa.le⟩

theorem exists_finite_power_cofinal_endpoint (n : ℕ) (A : Set V) (cut : V)
    (hbound : A ⊆ Set.Iio cut)
    (htype : typeLT A = (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal)) :
    ∃ bound : V, bound ≤ cut ∧ A ⊆ Set.Iio bound ∧ IsCofinal (below A bound) ∧
      typeLT (below A bound) = (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal) := by
  have hlimit : IsSuccPrelimit (typeLT A) := by
    rw [htype]
    exact (Ordinal.isSuccLimit_opow_left (Cardinal.isSuccLimit_omega 1)
      (by exact_mod_cast Nat.succ_ne_zero n)).isSuccPrelimit
  obtain ⟨bound, hbc, hsub, hcof⟩ := exists_cofinal_endpoint A cut hbound hlimit
  exact ⟨bound, hbc, hsub, hcof, (below_type A bound hsub).trans htype⟩

theorem exists_bounded_cofinal_power_decomposition (n : ℕ) (A : Set V) (cut : V)
    (hbound : A ⊆ Set.Iio cut)
    (htype : typeLT A < (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal)) :
    ∃ D : Set (Set V), D.Countable ∧ ⋃₀ D = A ∧ ∀ B ∈ D,
      typeLT B = 1 ∨ ∃ k : ℕ, k < n ∧ ∃ bound : V, bound ≤ cut ∧ B ⊆ Set.Iio bound ∧
        IsCofinal (below B bound) ∧
          typeLT (below B bound) = (ω_ 1 : Ordinal.{0}) ^ ((k + 1 : ℕ) : Ordinal) := by
  obtain ⟨D, hD, hcover, hpieces⟩ :=
    Erdos1172Part3FinitePowerDecomposition.exists_countable_power_decomposition n A htype
  refine ⟨D, hD, hcover, ?_⟩
  intro B hB
  rcases hpieces B hB with hsingle | ⟨k, hk, hktype⟩
  · exact Or.inl hsingle
  · have hBsub : B ⊆ A := by
      intro x hx
      rw [← hcover]
      exact ⟨B, hB, hx⟩
    obtain ⟨bound, hbc, hsub, hcof, htype⟩ :=
      exists_finite_power_cofinal_endpoint k B cut (hBsub.trans hbound) hktype
    exact Or.inr ⟨k, hk, bound, hbc, hsub, hcof, htype⟩

end Erdos1172Part3CofinalPowerEndpoints
