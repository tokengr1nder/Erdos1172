/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4GroundUltrapower
public import Mathlib.SetTheory.ZFC.Ordinal

@[expose] public section

/-! # The identity seed of the normal ground ultrapower

Normality makes every predecessor of the identity germ constant modulo
the ultrafilter. Strict tails place all smaller constant ordinals below
the seed. Induction computes the transitive collapse of these ordinals
and identifies the first ordinal moved by the ground embedding.
-/

set_option autoImplicit false
noncomputable section
open Filter
universe u

namespace Erdos1172GroundUltrapower

variable (κ : Cardinal.{u}) (U : Ultrafilter κ.ord.ToType)

def ContainsStrictTails : Prop :=
  ∀ a : κ.ord.ToType, ∀ᶠ i in U, a < i

def NormalRegressive : Prop :=
  ∀ f : κ.ord.ToType → κ.ord.ToType, (∀ᶠ i in U, f i < i) →
    ∃ a : κ.ord.ToType, ∀ᶠ i in U, f i = a

variable [CountableInterFilter (U : Filter κ.ord.ToType)]

def normalSeed : ZFSet.{u} :=
  collapse U (Germ.ofFun (fun i : κ.ord.ToType => i.toOrd.val.toZFSet))

private theorem index_lt_iff (a b : κ.ord.ToType) : a < b ↔ a.toOrd.val < b.toOrd.val :=
  (Ordinal.ToType.mk.symm.lt_iff_lt (x := a) (y := b)).symm

omit [CountableInterFilter (U : Filter κ.ord.ToType)] in
private theorem represent_seed_predecessor (hN : NormalRegressive κ U) (x : Ground U)
    (hx : memRel U x (Germ.ofFun (fun i : κ.ord.ToType => i.toOrd.val.toZFSet))) :
    ∃ a : κ.ord.ToType, x = Germ.const a.toOrd.val.toZFSet := by
  classical
  induction x using Germ.inductionOn with
  | _ X =>
    have h : ∀ᶠ i in U, X i ∈ i.toOrd.val.toZFSet := hx
    let below (i : κ.ord.ToType) := ∃ a : κ.ord.ToType, a < i ∧ a.toOrd.val.toZFSet = X i
    have hbelow : ∀ᶠ i in U, below i := h.mono fun i hi => by
      obtain ⟨α, hα, ha⟩ := Ordinal.mem_toZFSet_iff.mp hi
      let b : Set.Iio κ.ord := ⟨α, hα.trans i.toOrd.property⟩
      refine ⟨Ordinal.ToType.mk b, (index_lt_iff κ _ _).mpr ?_, ?_⟩
      · simpa only [Ordinal.ToType.toOrd, OrderIso.symm_apply_apply] using hα
      · simpa only [Ordinal.ToType.toOrd, OrderIso.symm_apply_apply] using ha
    let f (i : κ.ord.ToType) := if hb : below i then hb.choose else i
    have hs : ∀ᶠ i in U, f i < i ∧ (f i).toOrd.val.toZFSet = X i :=
      hbelow.mono (fun i hi => by simpa only [f, dif_pos hi] using hi.choose_spec)
    obtain ⟨a, hconst⟩ := hN f (hs.mono fun _ hd => hd.1)
    refine ⟨a, Germ.coe_eq.mpr ?_⟩
    filter_upwards [hs, hconst] with i hi he
    exact (he ▸ hi.2 : a.toOrd.val.toZFSet = X i).symm

theorem mem_normalSeed_iff (hN : NormalRegressive κ U) (hT : ContainsStrictTails κ U)
    (z : ZFSet.{u}) : z ∈ normalSeed κ U ↔
      ∃ α < κ.ord, diagonal U α.toZFSet = z := by
  constructor
  · intro hz
    obtain ⟨x, hx, he⟩ := (mem_collapse_iff U _ _).mp hz
    obtain ⟨a, rfl⟩ := represent_seed_predecessor κ U hN x hx
    exact ⟨a.toOrd.val, a.toOrd.property, he⟩
  · rintro ⟨α, hα, rfl⟩
    let a : κ.ord.ToType := Ordinal.ToType.mk ⟨α, hα⟩
    have ha : a.toOrd.val = α := congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply ⟨α, hα⟩)
    apply (collapse_mem_collapse_iff U _ _).mpr
    change ∀ᶠ (i : κ.ord.ToType) in U, α.toZFSet ∈ i.toOrd.val.toZFSet
    exact (hT a).mono (fun i hi => Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (ha ▸ (index_lt_iff κ a i).mp hi))

private theorem diagonal_ordinal_subset_seed (hT : ContainsStrictTails κ U)
    (α : Ordinal.{u}) (hα : α < κ.ord) : diagonal U α.toZFSet ⊆ normalSeed κ U := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := (mem_collapse_iff U _ _).mp hz
  apply (collapse_mem_collapse_iff U _ _).mpr
  induction w using Germ.inductionOn with
  | _ f =>
    let a : κ.ord.ToType := Ordinal.ToType.mk ⟨α, hα⟩
    have ha : a.toOrd.val = α := congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply ⟨α, hα⟩)
    change ∀ᶠ i in U, f i ∈ i.toOrd.val.toZFSet
    have h : ∀ᶠ i in U, f i ∈ α.toZFSet := hw
    filter_upwards [h, hT a] with i hi hab
    exact Ordinal.toZFSet_monotone (ha ▸ ((index_lt_iff κ a i).mp hab).le) hi

private theorem diagonal_mem_iff (x y : ZFSet.{u}) : diagonal U x ∈ diagonal U y ↔ x ∈ y :=
  (seed_mem_diagonal U (fun _ => x) y).trans eventually_const

theorem diagonal_fix_ordinal (hN : NormalRegressive κ U) (hT : ContainsStrictTails κ U)
    (α : Ordinal.{u}) : α < κ.ord → diagonal U α.toZFSet = α.toZFSet := by
  induction α using WellFoundedLT.induction with
  | ind α ih =>
    intro hα
    ext z
    constructor
    · intro hz
      obtain ⟨β, hβ, rfl⟩ := (mem_normalSeed_iff κ U hN hT _).mp
        (diagonal_ordinal_subset_seed κ U hT α hα hz)
      have hβα := Ordinal.toZFSet_mem_toZFSet_iff.mp ((diagonal_mem_iff κ U _ _).mp hz)
      rw [ih β hβα hβ]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hβα
    · intro hz
      obtain ⟨β, hβ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
      rw [← ih β hβ (hβ.trans hα)]
      exact (diagonal_mem_iff κ U _ _).mpr (Ordinal.toZFSet_mem_toZFSet_iff.mpr hβ)

theorem normalSeed_eq_critical (hN : NormalRegressive κ U) (hT : ContainsStrictTails κ U) :
    normalSeed κ U = κ.ord.toZFSet := by
  ext z
  rw [mem_normalSeed_iff κ U hN hT, Ordinal.mem_toZFSet_iff]
  constructor <;> rintro ⟨α, hα, hz⟩ <;> refine ⟨α, hα, ?_⟩
  · rwa [diagonal_fix_ordinal κ U hN hT α hα] at hz
  · rwa [diagonal_fix_ordinal κ U hN hT α hα]

theorem critical_mem_diagonal (hN : NormalRegressive κ U) (hT : ContainsStrictTails κ U) :
    κ.ord.toZFSet ∈ diagonal U κ.ord.toZFSet := by
  have h : normalSeed κ U ∈ diagonal U κ.ord.toZFSet :=
    (seed_mem_diagonal U _ _).mpr (Eventually.of_forall
      (fun i : κ.ord.ToType => Ordinal.toZFSet_mem_toZFSet_iff.mpr i.toOrd.property))
  rwa [normalSeed_eq_critical κ U hN hT] at h

/-- At the critical ordinal, seed membership recovers the actual ground measure. -/
theorem critical_mem_diagonal_iff (hN : NormalRegressive κ U) (hT : ContainsStrictTails κ U)
    (X : ZFSet.{u}) : κ.ord.toZFSet ∈ diagonal U X ↔
      ∀ᶠ (i : κ.ord.ToType) in U, i.toOrd.val.toZFSet ∈ X := by
  rw [← normalSeed_eq_critical κ U hN hT]
  exact seed_mem_diagonal U _ X

end Erdos1172GroundUltrapower
