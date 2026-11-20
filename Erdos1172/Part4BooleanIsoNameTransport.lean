/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanFunctionTransport
public import Erdos1172.Part4InternalFullGCH

@[expose] public section

/-!
# Transporting unbounded quantification under a Boolean algebra isomorphism

An isomorphism induces mutually inverse functions on hereditary Boolean names.
This identifies quantification over all names on either side, including mixed
names. Powersets are identified by Boolean-valued extensionality.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch

universe u

namespace bSet.ErdosNameTransport

variable {B C : Type u} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

abbrev isoHom (φ : B ≃o C) : CompleteLatticeHom B C :=
  CompleteLatticeHom.OrderIso.toCompleteLatticeHom φ

theorem mapNames_iso_inverse (φ : B ≃o C) (x : bSet B) :
    mapNames (isoHom φ.symm) (mapNames (isoHom φ) x) = x := by
  rw [← mapNames_comp]
  have he : (isoHom φ.symm).comp (isoHom φ) = CompleteLatticeHom.id B := by
    ext b
    exact φ.symm_apply_apply b
  rw [he, mapNames_id]

theorem mapNames_iso_rightInverse (φ : B ≃o C) (x : bSet C) :
    mapNames (isoHom φ) (mapNames (isoHom φ.symm) x) = x := mapNames_iso_inverse φ.symm x

def isoNames (φ : B ≃o C) : bSet B ≃ bSet C where
  toFun := mapNames (isoHom φ)
  invFun := mapNames (isoHom φ.symm)
  left_inv := mapNames_iso_inverse φ
  right_inv := mapNames_iso_rightInverse φ

theorem map_iso_iInf (φ : B ≃o C) (F : bSet B → B) :
    isoHom φ (⨅ x, F x) = ⨅ y, isoHom φ (F (mapNames (isoHom φ.symm) y)) := by
  rw [map_iInf]
  exact ((isoNames φ).symm.surjective.iInf_comp (fun x => isoHom φ (F x))).symm

theorem map_iso_iSup (φ : B ≃o C) (F : bSet B → B) :
    isoHom φ (⨆ x, F x) = ⨆ y, isoHom φ (F (mapNames (isoHom φ.symm) y)) := by
  rw [map_iSup]
  exact ((isoNames φ).symm.surjective.iSup_comp (fun x => isoHom φ (F x))).symm

theorem map_iso_Ord (φ : B ≃o C) (x : bSet B) :
    isoHom φ (Ord x) = Ord (mapNames (isoHom φ) x) := by
  simp only [Ord, epsilon_well_orders, epsilon_trichotomy, epsilon_well_founded, is_transitive,
    map_iso_iInf, map_iso_iSup, map_inf, map_sup, map_imp, map_compl', map_mem, map_bv_eq,
    map_subset, map_empty, mapNames_iso_rightInverse]

theorem map_iso_injects_into (φ : B ≃o C) (x y : bSet B) :
    isoHom φ (injects_into x y) = injects_into (mapNames (isoHom φ) x) (mapNames (isoHom φ) y) := by
  simp only [injects_into, is_func', is_func, is_inj, map_iso_iSup, map_iso_iInf, map_inf,
    map_imp, map_mem, map_bv_eq, map_is_total, map_pair, mapNames_iso_rightInverse]

theorem map_iso_hartogsProperty (φ : B ≃o C) (x y : bSet B) :
    isoHom φ (ErdosHartogs.hartogsProperty x y) =
      ErdosHartogs.hartogsProperty (mapNames (isoHom φ) x) (mapNames (isoHom φ) y) := by
  simp only [ErdosHartogs.hartogsProperty, map_iso_iInf, map_inf, map_compl', map_imp, map_mem,
    map_iso_Ord, map_iso_injects_into, mapNames_iso_rightInverse]

private theorem mem_powerset_value {A : Type u} [NontrivialCompleteBooleanAlgebra A]
    (x y : bSet A) : (y ∈ᴮ bv_powerset x) = (y ⊆ᴮ x) :=
  le_antisymm (mem_powerset_iff.mp le_rfl) (mem_powerset_iff.mpr le_rfl)

theorem map_iso_powerset (φ : B ≃o C) (x : bSet B) :
    (mapNames (isoHom φ) (bv_powerset x) =ᴮ bv_powerset (mapNames (isoHom φ) x)) = ⊤ := by
  apply top_unique
  apply le_trans _ (bSet_axiom_of_extensionality _ _)
  apply le_iInf
  intro y
  obtain ⟨z, rfl⟩ := (show Function.Surjective (mapNames (isoHom φ)) from (isoNames φ).surjective) y
  rw [← map_mem, mem_powerset_value, mem_powerset_value, map_subset]
  apply le_inf <;> rw [← deduction] <;> exact inf_le_right

theorem map_iso_gchAt (φ : B ≃o C) (x : bSet B) :
    isoHom φ (ErdosFullGCH.gchAt x) = ErdosFullGCH.gchAt (mapNames (isoHom φ) x) := by
  simp only [ErdosFullGCH.gchAt, map_iso_iSup, map_inf, map_iso_hartogsProperty,
    map_iso_injects_into, mapNames_iso_rightInverse]
  apply iSup_congr
  intro δ
  congr 1
  exact (bv_rw (map_iso_powerset φ x) (fun X => injects_into X δ)
    (h_congr := B_ext_injects_into_left)).symm

theorem map_iso_fullGCHValue (φ : B ≃o C) :
    isoHom φ (ErdosFullGCH.fullGCHValue : B) = (ErdosFullGCH.fullGCHValue : C) := by
  have hw : mapNames (isoHom φ) (omega : bSet B) = omega := map_check (isoHom φ) PSet.omega
  simp only [ErdosFullGCH.fullGCHValue, map_iso_iInf, map_imp, map_iso_injects_into,
    map_iso_gchAt, hw, mapNames_iso_rightInverse]

end bSet.ErdosNameTransport
