/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Flypitch4.BvmExtras
public import Mathlib.Order.Hom.CompleteLattice

@[expose] public section

/-!
# Transport of Boolean names along a complete homomorphism

The recursive map changes every hereditary Boolean coefficient. Equality,
membership, bounded subset values, and ground check names are preserved.
No claim is made about arbitrary unbounded quantifiers: the target algebra
can have names not arising by transport from the source algebra.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch

universe u

namespace bSet.ErdosNameTransport

variable {B C D : Type u}
variable [NontrivialCompleteBooleanAlgebra B]
variable [NontrivialCompleteBooleanAlgebra C]
variable [NontrivialCompleteBooleanAlgebra D]

/-- Transport all coefficients, not only the outermost layer of a name. -/
def mapNames (e : CompleteLatticeHom B C) : bSet B → bSet C
  | .mk ι X w => .mk ι (fun i => mapNames e (X i)) (fun i => e (w i))

theorem mapNames_mk (e : CompleteLatticeHom B C) {ι : Type u}
    (X : ι → bSet B) (w : ι → B) :
    mapNames e (.mk ι X w) = .mk ι (fun i => mapNames e (X i)) (fun i => e (w i)) := rfl

theorem map_imp (e : CompleteLatticeHom B C) (a b : B) :
    e (_root_.imp a b) = _root_.imp (e a) (e b) := by
  simp only [_root_.imp, map_sup, map_compl']

theorem map_bv_eq (e : CompleteLatticeHom B C) (x y : bSet B) :
    e (x =ᴮ y) = (mapNames e x =ᴮ mapNames e y) := by
  induction x generalizing y with
  | mk ι X w ih =>
    cases y with
    | mk κ Y v =>
      simp only [mapNames, bv_eq, map_inf, map_iInf, map_imp, map_iSup, ih]

theorem map_mem (e : CompleteLatticeHom B C) (x y : bSet B) :
    e (x ∈ᴮ y) = (mapNames e x ∈ᴮ mapNames e y) := by
  cases y with
  | mk ι Y w =>
    simp only [mapNames, bSet.mem, map_iSup, map_inf, map_bv_eq]

theorem map_subset (e : CompleteLatticeHom B C) (x y : bSet B) :
    e (x ⊆ᴮ y) = (mapNames e x ⊆ᴮ mapNames e y) := by
  cases x with
  | mk ι X w =>
    simp only [mapNames, bSet.subset, map_iInf, map_imp, map_mem]

theorem map_check (e : CompleteLatticeHom B C) (A : PSet.{u}) :
    mapNames e (check A) = check A := by
  induction A with
  | mk ι X ih =>
    simp only [check, mapNames, map_top, ih]

theorem mapNames_id (x : bSet B) :
    mapNames (CompleteLatticeHom.id B) x = x := by
  induction x with
  | mk ι X w ih =>
    simp only [mapNames, CompleteLatticeHom.id_apply, ih]

theorem mapNames_comp (e : CompleteLatticeHom B C) (f : CompleteLatticeHom C D)
    (x : bSet B) : mapNames (f.comp e) x = mapNames f (mapNames e x) := by
  induction x with
  | mk ι X w ih =>
    simp only [mapNames, CompleteLatticeHom.comp_apply, ih]

/-- An injective complete homomorphism also reflects each atomic forcing inequality. -/
theorem le_bv_eq_iff (e : CompleteLatticeHom B C) (he : Function.Injective e)
    (Γ : B) (x y : bSet B) :
    Γ ≤ x =ᴮ y ↔ e Γ ≤ mapNames e x =ᴮ mapNames e y := by
  rw [← map_bv_eq]
  constructor
  · intro h
    exact OrderHomClass.mono e h
  · intro h
    have hmeet : Γ ⊓ (x =ᴮ y) = Γ := he (by rw [map_inf, inf_eq_left.mpr h])
    exact inf_eq_left.mp hmeet

theorem le_mem_iff (e : CompleteLatticeHom B C) (he : Function.Injective e)
    (Γ : B) (x y : bSet B) :
    Γ ≤ x ∈ᴮ y ↔ e Γ ≤ mapNames e x ∈ᴮ mapNames e y := by
  rw [← map_mem]
  constructor
  · intro h
    exact OrderHomClass.mono e h
  · intro h
    have hmeet : Γ ⊓ (x ∈ᴮ y) = Γ := he (by rw [map_inf, inf_eq_left.mpr h])
    exact inf_eq_left.mp hmeet

theorem le_subset_iff (e : CompleteLatticeHom B C) (he : Function.Injective e)
    (Γ : B) (x y : bSet B) :
    Γ ≤ x ⊆ᴮ y ↔ e Γ ≤ mapNames e x ⊆ᴮ mapNames e y := by
  rw [← map_subset]
  constructor
  · intro h
    exact OrderHomClass.mono e h
  · intro h
    have hmeet : Γ ⊓ (x ⊆ᴮ y) = Γ := he (by rw [map_inf, inf_eq_left.mpr h])
    exact inf_eq_left.mp hmeet

end bSet.ErdosNameTransport
