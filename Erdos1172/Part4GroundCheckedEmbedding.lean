/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4GroundNormalSeed
public import Flypitch4.BvmExtras

@[expose] public section

/-! # The collapsed ground ultrapower on checked set names

A family of ground pre-sets represents one pre-set in the transitive
ultrapower. Equality and membership of its checked names have Boolean
value top precisely on the corresponding ultrafilter tests. Every member
of the represented set has a representative family of its own.
-/

set_option autoImplicit false
noncomputable section
open Filter bSet
open scoped Flypitch
universe u

namespace Erdos1172GroundUltrapower

variable {I : Type u} (U : Ultrafilter I) [CountableInterFilter (U : Filter I)]

def groundPSet (A : I → PSet.{u}) : PSet.{u} :=
  (collapse U (Germ.ofFun (fun i => ZFSet.mk (A i)))).out

theorem mk_groundPSet (A : I → PSet.{u}) :
    ZFSet.mk (groundPSet U A) = collapse U (Germ.ofFun (fun i => ZFSet.mk (A i))) :=
  ZFSet.mk_out _

theorem groundPSet_equiv_iff (A D : I → PSet.{u}) :
    PSet.Equiv (groundPSet U A) (groundPSet U D) ↔ ∀ᶠ i in U, PSet.Equiv (A i) (D i) := by
  simp only [PSet.equiv_iff_eq, mk_groundPSet, (collapse_injective U).eq_iff, Germ.coe_eq]
  rfl

theorem groundPSet_mem_iff (A D : I → PSet.{u}) :
    groundPSet U A ∈ groundPSet U D ↔ ∀ᶠ i in U, A i ∈ D i := by
  simp only [PSet.mem_iff, mk_groundPSet, collapse_mem_collapse_iff, memRel_rep]

theorem mem_groundPSet_rep (A : I → PSet.{u}) (x : PSet.{u}) :
    x ∈ groundPSet U A ↔ ∃ F : I → PSet.{u},
      (∀ᶠ i in U, F i ∈ A i) ∧ PSet.Equiv (groundPSet U F) x := by
  constructor
  · intro hx
    have hz := PSet.mem_iff.mp hx
    rw [mk_groundPSet] at hz
    obtain ⟨w, hw, he⟩ := (mem_collapse_iff U _ _).mp hz
    induction w using Germ.inductionOn with
    | _ W =>
      refine ⟨fun i => (W i).out, ?_, ?_⟩
      · have hm : ∀ᶠ i in U, W i ∈ ZFSet.mk (A i) := hw
        exact hm.mono (fun i hi => PSet.mem_iff.mpr (by simpa only [ZFSet.mk_out] using hi))
      · apply PSet.equiv_iff_eq.mpr
        simpa only [mk_groundPSet, ZFSet.mk_out] using he
  · rintro ⟨F, hF, he⟩
    apply PSet.mem_iff.mpr
    rw [← PSet.equiv_iff_eq.mp he]
    exact PSet.mem_iff.mp ((groundPSet_mem_iff U F A).mpr hF)

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

theorem checked_groundPSet_eq_iff (A D : I → PSet.{u}) :
    ((check (groundPSet U A) : bSet B) =ᴮ check (groundPSet U D)) = ⊤ ↔
      ∀ᶠ i in U, PSet.Equiv (A i) (D i) :=
  check_bv_eq_iff.symm.trans (groundPSet_equiv_iff U A D)

theorem checked_groundPSet_mem_iff (A D : I → PSet.{u}) :
    ((check (groundPSet U A) : bSet B) ∈ᴮ check (groundPSet U D)) = ⊤ ↔
      ∀ᶠ i in U, A i ∈ D i :=
  check_mem_iff.symm.trans (groundPSet_mem_iff U A D)

section Critical

variable (κ : Cardinal.{u}) (V : Ultrafilter κ.ord.ToType)
variable [CountableInterFilter (V : Filter κ.ord.ToType)]
variable (hN : NormalRegressive κ V) (hT : ContainsStrictTails κ V)

include hN hT in
theorem groundPSet_ordinal_fixed (α : Ordinal.{u}) (hα : α < κ.ord) :
    PSet.Equiv (groundPSet V (fun _ => PSet.ordinalMk α)) (PSet.ordinalMk α) := by
  apply PSet.equiv_iff_eq.mpr
  rw [mk_groundPSet]
  exact diagonal_fix_ordinal κ V hN hT α hα

include hN hT in
theorem groundPSet_seed_equiv : PSet.Equiv
    (groundPSet V (fun i : κ.ord.ToType => PSet.ordinalMk i.toOrd.val))
    (PSet.ordinalMk κ.ord) := by
  apply PSet.equiv_iff_eq.mpr
  rw [mk_groundPSet]
  exact normalSeed_eq_critical κ V hN hT

include hN hT in
theorem checked_critical_mem_groundPSet_iff (A : κ.ord.ToType → PSet.{u}) :
    ((check (PSet.ordinalMk κ.ord) : bSet B) ∈ᴮ check (groundPSet V A)) = ⊤ ↔
      ∀ᶠ (i : κ.ord.ToType) in V, PSet.ordinalMk i.toOrd.val ∈ A i := by
  rw [← check_mem_iff, PSet.mem_iff, ← PSet.equiv_iff_eq.mp (groundPSet_seed_equiv κ V hN hT),
    ← PSet.mem_iff]
  exact groundPSet_mem_iff V _ A

include hN hT in
theorem checked_critical_mem_image : (⊤ : B) ≤
    check (PSet.ordinalMk κ.ord) ∈ᴮ check (groundPSet V (fun _ => PSet.ordinalMk κ.ord)) := by
  apply check_mem
  apply PSet.mem_iff.mpr
  rw [mk_groundPSet]
  exact critical_mem_diagonal κ V hN hT

end Critical
end Erdos1172GroundUltrapower
