/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4GroundElementaryEmbedding
public import Mathlib.ModelTheory.ElementarySubstructures

@[expose] public section

/-! # The bounded-support hull of a ground ultrapower

A germ belongs to the hull when its value depends only on the part of the
index fiber below a fixed ordinal. Each finite parameter tuple has a common
bound, so its pointwise Skolem witnesses have bounded support as well.
-/

set_option autoImplicit false
noncomputable section
open Filter FirstOrder
universe u
namespace Erdos1172GroundUltrapower

variable {I : Type u} (U : Ultrafilter I) (θ : Cardinal.{u}) (a : I → Set θ.ord.ToType)

def boundedFiber (η : θ.ord.ToType) (i : I) : Set θ.ord.ToType := a i ∩ Set.Iio η

def BoundedSupport (x : Ground U) : Prop :=
  ∃ η : θ.ord.ToType, ∃ f : Set θ.ord.ToType → ZFSet.{u},
    Germ.ofFun (fun i => f (boundedFiber θ a η i)) = x

abbrev BoundedHull := {x : Ground U // BoundedSupport U θ a x}

def boundedConst [Nonempty θ.ord.ToType] (x : ZFSet.{u}) : BoundedHull U θ a :=
  ⟨Germ.const x, Classical.choice ‹Nonempty θ.ord.ToType›, fun _ => x, rfl⟩

theorem boundedFiber_restrict {η ν : θ.ord.ToType} (h : η ≤ ν) (i : I) :
    boundedFiber θ a ν i ∩ Set.Iio η = boundedFiber θ a η i := by
  ext v
  exact ⟨fun hv => ⟨hv.1.1, hv.2⟩, fun hv => ⟨⟨hv.1, hv.2.trans_le h⟩, hv.2⟩⟩

theorem exists_common_bounded_support [Nonempty θ.ord.ToType] {n : ℕ} (x : Fin n → BoundedHull U θ a) :
    ∃ η : θ.ord.ToType, ∃ f : Fin n → Set θ.ord.ToType → ZFSet.{u},
      ∀ j, Germ.ofFun (fun i => f j (boundedFiber θ a η i)) = (x j).val := by
  classical
  choose η f hf using fun j => (x j).property
  obtain ⟨ν, hν⟩ := (Set.finite_range η).bddAbove
  refine ⟨ν, fun j s => f j (s ∩ Set.Iio (η j)), fun j => ?_⟩
  simpa only [boundedFiber_restrict θ a (hν (Set.mem_range_self j))] using hf j

def boundedSubstructure : setLanguage.Substructure (AbstractModel U) where
  carrier := BoundedSupport U θ a
  fun_mem f := nomatch f

theorem snoc_los {n : ℕ} (φ : setLanguage.BoundedFormula Empty (n + 1))
    (e₀ : Empty → AbstractModel U) (e₁ : Empty → ZFSet.{u})
    (v : Fin n → I → ZFSet.{u}) (w : I → ZFSet.{u}) :
    φ.Realize e₀ (Fin.snoc (α := fun _ => AbstractModel U)
      (fun j => (v j : AbstractModel U)) (w : AbstractModel U)) ↔
    ∀ᶠ i in U, φ.Realize e₁ (Fin.snoc (α := fun _ => ZFSet.{u}) (fun j => v j i) (w i)) := by
  let t : Fin (n + 1) → I → ZFSet.{u} := Fin.snoc v w
  let e : Empty → I → ZFSet.{u} := default
  have h := Language.Ultraproduct.boundedFormula_realize_cast
    (M := fun _ : I => ZFSet.{u}) (u := U) φ e t
  have ht : (fun j => (t j : AbstractModel U)) =
      Fin.snoc (α := fun _ => AbstractModel U) (fun j => (v j : AbstractModel U)) (w : AbstractModel U) :=
    Fin.comp_snoc (fun f : I → ZFSet.{u} => (f : AbstractModel U)) v w
  have hi (i : I) : (fun j => t j i) =
      Fin.snoc (α := fun _ => ZFSet.{u}) (fun j => v j i) (w i) :=
    Fin.comp_snoc (fun f : I → ZFSet.{u} => f i) v w
  have he : (fun j => (e j : AbstractModel U)) = e₀ := Subsingleton.elim _ _
  have hei (i : I) : (fun j => e j i) = e₁ := Subsingleton.elim _ _
  simp only [he, ht, hi, hei] at h
  exact h

def boundedElementary [Nonempty θ.ord.ToType] :
    setLanguage.ElementarySubstructure (AbstractModel U) := by
  classical
  apply (boundedSubstructure U θ a).toElementarySubstructure
  intro n φ x t ht
  obtain ⟨η, f, hf⟩ := exists_common_bounded_support U θ a (fun j => x j)
  let v (j : Fin n) (i : I) := f j (boundedFiber θ a η i)
  have hv : (fun j => (Germ.ofFun (v j) : Ground U)) = Subtype.val ∘ x := funext hf
  obtain ⟨w, rfl⟩ : ∃ w : I → ZFSet.{u}, Germ.ofFun w = t :=
    Germ.inductionOn t (fun w => ⟨w, rfl⟩)
  rw [← hv] at ht
  have hpoint := (snoc_los U φ _ (Empty.elim : Empty → ZFSet.{u}) v w).mp ht
  let W (s : Set θ.ord.ToType) := Classical.epsilon fun y : ZFSet.{u} =>
    φ.Realize (Empty.elim : Empty → ZFSet.{u}) (Fin.snoc (fun j => f j s) y)
  let z (i : I) := W (boundedFiber θ a η i)
  refine ⟨⟨Germ.ofFun z, η, W, rfl⟩, ?_⟩
  rw [← hv]
  apply (snoc_los U φ _ (Empty.elim : Empty → ZFSet.{u}) v z).mpr
  exact hpoint.mono fun i hi => Classical.epsilon_spec
    (p := fun y => φ.Realize (Empty.elim : Empty → ZFSet.{u}) (Fin.snoc (fun j => v j i) y)) ⟨w i, hi⟩

variable [CountableInterFilter (U : Filter I)]

def boundedMem (x y : BoundedHull U θ a) : Prop := memRel U x.val y.val

theorem boundedMem_wf : WellFounded (boundedMem U θ a) := InvImage.wf Subtype.val (memRel_wf U)

instance boundedPredecessorSmall (x : BoundedHull U θ a) :
    Small.{u} {y : BoundedHull U θ a // boundedMem U θ a y x} := by
  let F (y : {y : BoundedHull U θ a // boundedMem U θ a y x}) :
      {z : Ground U // memRel U z x.val} := ⟨y.val.val, y.property⟩
  apply small_of_injective (f := F)
  intro y z h
  exact Subtype.ext (Subtype.ext (show y.val.val = z.val.val from congrArg (fun q => q.val) h))

def boundedCollapse : BoundedHull U θ a → ZFSet.{u} :=
  (boundedMem_wf U θ a).fix fun x rec =>
    ZFSet.range (fun y : {y : BoundedHull U θ a // boundedMem U θ a y x} => rec y.val y.property)

theorem mem_boundedCollapse_iff (z : ZFSet.{u}) (x : BoundedHull U θ a) :
    z ∈ boundedCollapse U θ a x ↔ ∃ y, boundedMem U θ a y x ∧ boundedCollapse U θ a y = z := by
  rw [show boundedCollapse U θ a x = ZFSet.range
    (fun y : {y : BoundedHull U θ a // boundedMem U θ a y x} => boundedCollapse U θ a y.val)
    from WellFounded.fix_eq _ _ _, ZFSet.mem_range]
  exact ⟨fun ⟨y, h⟩ => ⟨y.val, y.property, h⟩, fun ⟨y, hy, h⟩ => ⟨⟨y, hy⟩, h⟩⟩

variable [Nonempty θ.ord.ToType]

omit [CountableInterFilter (U : Filter I)] in
private theorem bounded_subset_test (x y : BoundedHull U θ a)
    (h : ∀ z, boundedMem U θ a z x → boundedMem U θ a z y) :
    ∀ z : Ground U, memRel U z x.val → memRel U z y.val := by
  classical
  obtain ⟨η, f, hf⟩ := exists_common_bounded_support U θ a ![x, y]
  let s (i : I) := boundedFiber θ a η i
  have hx : Germ.ofFun (fun i => f 0 (s i)) = x.val := by simpa using hf 0
  have hy : Germ.ofFun (fun i => f 1 (s i)) = y.val := by simpa using hf 1
  have hs : ∀ᶠ i in U, f 0 (s i) ⊆ f 1 (s i) := by
    by_contra hn
    have hb := U.eventually_not.mpr hn
    let W (t : Set θ.ord.ToType) := Classical.epsilon (fun w : ZFSet.{u} => w ∈ f 0 t ∧ w ∉ f 1 t)
    have hW : ∀ᶠ i in U, W (s i) ∈ f 0 (s i) ∧ W (s i) ∉ f 1 (s i) := by
      filter_upwards [hb] with i hi
      apply Classical.epsilon_spec (p := fun w : ZFSet.{u} => w ∈ f 0 (s i) ∧ w ∉ f 1 (s i))
      by_contra! hnone
      exact hi (fun z hz => hnone z hz)
    let z : BoundedHull U θ a := ⟨Germ.ofFun (fun i => W (s i)), η, W, rfl⟩
    have hzx : memRel U z.val x.val := hx ▸ hW.mono (fun _ => And.left)
    have hzy := h z hzx
    change memRel U z.val y.val at hzy
    rw [← hy] at hzy
    exact (U.eventually_not.mp (hW.mono (fun _ => And.right))) hzy
  intro z
  induction z using Germ.inductionOn with
  | _ Z =>
    rw [← hx, ← hy, memRel_rep, memRel_rep]
    intro hz
    exact (hs.and hz).mono fun _ h' => h'.1 h'.2

omit [CountableInterFilter (U : Filter I)] in
theorem boundedMem_ext {x y : BoundedHull U θ a}
    (h : ∀ z, boundedMem U θ a z x ↔ boundedMem U θ a z y) : x = y :=
  Subtype.ext (memRel_ext U (fun z => ⟨bounded_subset_test U θ a x y (fun w => (h w).mp) z,
    bounded_subset_test U θ a y x (fun w => (h w).mpr) z⟩))

theorem boundedCollapse_injective : Function.Injective (boundedCollapse U θ a) := by
  intro x
  induction x using (boundedMem_wf U θ a).induction with
  | h x ih =>
    intro y hxy
    apply boundedMem_ext U θ a
    intro z
    constructor
    · intro hz
      have hm := (mem_boundedCollapse_iff U θ a _ x).mpr ⟨z, hz, rfl⟩
      rw [hxy] at hm
      obtain ⟨t, ht, he⟩ := (mem_boundedCollapse_iff U θ a _ y).mp hm
      exact (ih z hz he.symm).symm ▸ ht
    · intro hz
      have hm := (mem_boundedCollapse_iff U θ a _ y).mpr ⟨z, hz, rfl⟩
      rw [← hxy] at hm
      obtain ⟨t, ht, he⟩ := (mem_boundedCollapse_iff U θ a _ x).mp hm
      exact ih t ht he ▸ ht

theorem boundedCollapse_mem_boundedCollapse_iff (x y : BoundedHull U θ a) :
    boundedCollapse U θ a x ∈ boundedCollapse U θ a y ↔ boundedMem U θ a x y := by
  rw [mem_boundedCollapse_iff]
  exact ⟨fun ⟨z, hz, he⟩ => boundedCollapse_injective U θ a he ▸ hz, fun h => ⟨x, h, rfl⟩⟩

def boundedTargetClass : Set ZFSet.{u} := Set.range (boundedCollapse U θ a)

instance boundedTargetStructure : setLanguage.Structure (boundedTargetClass U θ a) where
  RelMap | .mem => fun x => (x 0).val ∈ (x 1).val

def boundedCollapseIso : boundedElementary U θ a ≃[setLanguage] boundedTargetClass U θ a where
  toEquiv := Equiv.ofInjective (boundedCollapse U θ a) (boundedCollapse_injective U θ a)
  map_fun' := fun f => nomatch f
  map_rel' := by
    intro n r v
    cases r
    let X (k : Fin 2) : BoundedHull U θ a := ⟨(v k).val, (v k).property⟩
    exact (boundedCollapse_mem_boundedCollapse_iff U θ a (X 0) (X 1)).trans
      ((collapse_mem_collapse_iff U (X 0).val (X 1).val).symm.trans
        ((collapseIso U).map_rel MemSymbol.mem (fun k => (v k).val)))

def boundedDiagonalEmbedding : ZFSet.{u} ↪ₑ[setLanguage] boundedElementary U θ a where
  toFun := boundedConst U θ a
  map_formula' := by
    intro n φ v
    have h₁ := (boundedElementary U θ a).subtype.map_formula φ
      (fun j => (boundedConst U θ a (v j) : boundedElementary U θ a))
    have h₂ := Language.Ultraproduct.realize_formula_cast
      (M := fun _ : I => ZFSet.{u}) (u := U) φ (fun j _ => v j)
    exact h₁.symm.trans (h₂.trans eventually_const)

def boundedGroundEmbedding : ZFSet.{u} ↪ₑ[setLanguage] boundedTargetClass U θ a :=
  (boundedCollapseIso U θ a).toElementaryEmbedding.comp (boundedDiagonalEmbedding U θ a)

theorem boundedGroundEmbedding_val (x : ZFSet.{u}) :
    (boundedGroundEmbedding U θ a x).val = boundedCollapse U θ a (boundedConst U θ a x) := rfl

end Erdos1172GroundUltrapower
