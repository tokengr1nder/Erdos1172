/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.Logic.Small.Set
public import Mathlib.Order.Filter.CountableInter
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.Order.WellFounded
public import Mathlib.SetTheory.ZFC.Basic

@[expose] public section

/-! # The transitive collapse of a countably complete ground ultrapower

Countable completeness rules out descending membership chains. Every
predecessor collection is small in the original universe, since its
representatives can be chosen pointwise from small sets. These facts allow
the collapse to take values in the original type of Zermelo–Fraenkel sets.
-/

set_option autoImplicit false
noncomputable section
open Filter
universe u

namespace Erdos1172GroundUltrapower

variable {I : Type u} (U : Ultrafilter I)

abbrev Ground := Germ (U : Filter I) ZFSet.{u}

def memRel (x y : Ground U) : Prop := Germ.LiftRel (fun a b : ZFSet.{u} => a ∈ b) x y

theorem memRel_rep (x y : I → ZFSet.{u}) :
    memRel U (Germ.ofFun x) (Germ.ofFun y) ↔ ∀ᶠ i in U, x i ∈ y i := Iff.rfl

variable [CountableInterFilter (U : Filter I)]

theorem memRel_wf : WellFounded (memRel U) := by
  apply wellFounded_iff_isEmpty_descending_chain.mpr
  constructor
  rintro ⟨f, hf⟩
  have hr (n : ℕ) : ∃ g : I → ZFSet.{u}, Germ.ofFun g = f n :=
    Germ.inductionOn (f n) (fun g => ⟨g, rfl⟩)
  choose g hg using hr
  have hd (n : ℕ) : ∀ᶠ i in U, g (n + 1) i ∈ g n i :=
    (memRel_rep U _ _).mp (by rw [hg, hg]; exact hf n)
  obtain ⟨i, hi⟩ := (eventually_countable_forall.mpr hd).exists
  exact (wellFounded_iff_isEmpty_descending_chain.mp ZFSet.mem_wf).false ⟨fun n => g n i, hi⟩

instance predecessorSmall (x : Ground U) : Small.{u} {y : Ground U // memRel U y x} := by
  classical
  induction x using Germ.inductionOn with
  | _ X =>
    let box (i : I) : ZFSet.{u} := insert ∅ (X i)
    let enc (v : ∀ i, ↥(box i)) : Ground U := Germ.ofFun (fun i => (v i).val)
    let (i : I) : Small.{u} ↥(box i) := ZFSet.small_coe (box i)
    let : Small.{u} (∀ i, ↥(box i)) := small_Pi _
    let : Small.{u} (Set.range enc) := small_range enc
    apply small_subset (s := Set.range enc)
    intro y
    induction y using Germ.inductionOn with
    | _ Y =>
      intro hY
      have h : ∀ᶠ i in U, Y i ∈ X i := hY
      let v (i : I) : ↥(box i) :=
        if hi : Y i ∈ X i then ⟨Y i, ZFSet.mem_insert_of_mem _ hi⟩
        else ⟨∅, ZFSet.mem_insert _ _⟩
      exact ⟨v, Germ.coe_eq.mpr (h.mono (fun i hi => by simp [v, hi]))⟩

omit [CountableInterFilter (U : Filter I)] in
private theorem eventually_subset (X Y : I → ZFSet.{u})
    (h : ∀ z, memRel U z (Germ.ofFun X) → memRel U z (Germ.ofFun Y)) :
    ∀ᶠ i in U, X i ⊆ Y i := by
  classical
  by_contra hn
  have H := U.eventually_not.mpr hn
  let bad (i : I) := ∃ z : ZFSet.{u}, z ∈ X i ∧ z ∉ Y i
  have hb : ∀ᶠ i in U, bad i := H.mono (fun i hi => by
    by_contra hnone
    apply hi
    intro z hz
    by_contra hz'
    exact hnone ⟨z, hz, hz'⟩)
  let z (i : I) : ZFSet.{u} := if hi : bad i then hi.choose else ∅
  have hz : ∀ᶠ i in U, z i ∈ X i ∧ z i ∉ Y i :=
    hb.mono (fun i hi => by simpa only [z, dif_pos hi] using hi.choose_spec)
  have hy := h (Germ.ofFun z) (hz.mono (fun _ => And.left))
  exact (U.eventually_not.mp (hz.mono (fun _ => And.right))) hy

omit [CountableInterFilter (U : Filter I)] in
theorem memRel_ext {x y : Ground U} (h : ∀ z, memRel U z x ↔ memRel U z y) : x = y := by
  induction x, y using Germ.inductionOn₂ with
  | _ X Y =>
    apply Germ.coe_eq.mpr
    exact ((eventually_subset U X Y (fun z => (h z).mp)).and
      (eventually_subset U Y X (fun z => (h z).mpr))).mono
        (fun _ hxy => ZFSet.ext (fun _ => ⟨fun ha => hxy.1 ha, fun hb => hxy.2 hb⟩))

def collapse : Ground U → ZFSet.{u} :=
  (memRel_wf U).fix fun x rec =>
    ZFSet.range (fun y : {y : Ground U // memRel U y x} => rec y.val y.property)

theorem mem_collapse_iff (a : ZFSet.{u}) (x : Ground U) :
    a ∈ collapse U x ↔ ∃ y, memRel U y x ∧ collapse U y = a := by
  rw [show collapse U x = ZFSet.range (fun y : {y : Ground U // memRel U y x} =>
    collapse U y.val) from WellFounded.fix_eq _ _ _, ZFSet.mem_range]
  exact ⟨fun ⟨y, h⟩ => ⟨y.val, y.property, h⟩, fun ⟨y, hy, h⟩ => ⟨⟨y, hy⟩, h⟩⟩

theorem collapse_injective : Function.Injective (collapse U) := by
  intro x
  induction x using (memRel_wf U).induction with
  | h x ih =>
    intro y hxy
    apply memRel_ext U
    intro z
    constructor
    · intro hz
      have hmem := (mem_collapse_iff U _ x).mpr ⟨z, hz, rfl⟩
      rw [hxy] at hmem
      obtain ⟨t, ht, he⟩ := (mem_collapse_iff U _ y).mp hmem
      exact (ih z hz he.symm).symm ▸ ht
    · intro hz
      have hmem := (mem_collapse_iff U _ y).mpr ⟨z, hz, rfl⟩
      rw [← hxy] at hmem
      obtain ⟨t, ht, he⟩ := (mem_collapse_iff U _ x).mp hmem
      exact ih t ht he ▸ ht

theorem collapse_mem_collapse_iff (x y : Ground U) :
    collapse U x ∈ collapse U y ↔ memRel U x y := by
  rw [mem_collapse_iff]
  exact ⟨fun ⟨z, hz, he⟩ => collapse_injective U he ▸ hz, fun h => ⟨x, h, rfl⟩⟩

def diagonal (x : ZFSet.{u}) : ZFSet.{u} := collapse U (Germ.const x)

end Erdos1172GroundUltrapower
