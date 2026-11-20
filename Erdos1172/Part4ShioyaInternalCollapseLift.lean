/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalCollapsePrefix

@[expose] public section

/-! # Exact one-step lifting for the native ordinal collapse paths -/

set_option autoImplicit false
noncomputable section
universe u
open scoped Flypitch
open Lattice
namespace bSet.ErdosShioyaInternal.CollapsePath
open ErdosBoundedFunctionValue ErdosInjectionExtension
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

def append (f length q : N) : N := bSet.insert1 (pair length q) f

theorem append_func {Γ : B} {P f l q : N} (hf : Γ ≤ is_function l P f) (hq : Γ ≤ q ∈ᴮ P) :
    Γ ≤ is_function (succ l) P (append f l q) := by
  have fresh : Γ ≤ (l ∈ᴮ l)ᶜ := by rw [← imp_bot,← deduction]; exact bot_of_mem_self' inf_le_right
  exact le_inf (le_inf (is_func_insertPair hf fresh) (is_total_insertPair hf hq)) (insertPair_subset_prod hf hq)

private theorem pre_survives {Γ : B} {A B' x : N} (eq : Γ ≤ A =ᴮ B') (hx : Γ ≤ survives A x) :
    Γ ≤ survives B' x := allIn_intro fun hd _ hc => allIn_elim (hd.trans hx)
      (mem_congr bv_refl (bv_symm (hd.trans eq)) hc)

private theorem refl_order {Γ : B} {P R x : N} (po : Γ ≤ partialOrderValue P R) (hx : Γ ≤ x ∈ᴮ P) :
    Γ ≤ edge R x x := allIn_elim (f := fun z => edge R z z) (po.trans (inf_le_right.trans inf_le_left)) hx

def Represents (Γ : B) (P R l h p : N) : Prop :=
  Γ ≤ p ∈ᴮ P ∧ ∀ {Δ : B}, Δ ≤ Γ → ∀ {x : N}, Δ ≤ x ∈ᴮ P →
    (Δ ≤ survives (image l (bv_powerset P) h) x ↔ Δ ≤ edge R x p)

/-- Prolonging a named string can only strengthen its evaluation. -/
theorem evaluation_mono {Γ : B} {P R a b f g h k x y : N} (po : Γ ≤ partialOrderValue P R)
    (ord : Γ ≤ Ord a) (hf : Γ ≤ is_function a P f) (hg : Γ ≤ is_function b P g)
    (sub : Γ ≤ f ⊆ᴮ g) (hh : Γ ≤ is_function a (bv_powerset P) h)
    (hk : Γ ≤ is_function b (bv_powerset P) k) (hlaw : Γ ≤ trace P R f h) (klaw : Γ ≤ trace P R g k)
    (old : Represents Γ P R a h x) (new : Represents Γ P R b k y) : Γ ≤ edge R y x := by
  have keep := (new.2 le_rfl new.1).mpr (refl_order po new.1)
  have agreement := prefix_image ord hf hg sub hh hk hlaw klaw
  apply (old.2 le_rfl new.1).mp
  apply pre_survives (bv_symm agreement)
  apply allIn_intro
  intro Δ hd C hc
  obtain ⟨j,hj⟩ := exists_convert (mem_image_iff.mp hc).2 (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  have jb := mem_of_mem_subset (hd.trans (length_mono hf hg sub)) (hj.trans inf_le_left)
  exact allIn_elim (hd.trans keep) (mem_image (hj.trans inf_le_right) jb (mem_image_iff.mp hc).1)

/-- Appending a proposed stronger target returns that very target. All
later quantification ranges over arbitrary names and Boolean subconditions. -/
theorem append_represents {Γ : B} {P R a f h k x q : N} (po : Γ ≤ partialOrderValue P R)
    (ord : Γ ≤ Ord a) (hf : Γ ≤ is_function a P f) (hh : Γ ≤ is_function a (bv_powerset P) h)
    (hlaw : Γ ≤ trace P R f h) (old : Represents Γ P R a h x)
    (hq : Γ ≤ q ∈ᴮ P) (hqx : Γ ≤ edge R q x) (hk : Γ ≤ is_function (succ a) (bv_powerset P) k)
    (klaw : Γ ≤ trace P R (append f a q) k) : Represents Γ P R (succ a) k q := by
  let V := bv_powerset P
  let g := append f a q
  let C := graphValue V k a
  have hg := append_func hf hq
  have hprefix := prefix_image ord hf hg subset_insertPair hh hk hlaw klaw
  have ms (t : N) : (t ∈ᴮ succ a) = (t =ᴮ a) ⊔ (t ∈ᴮ a) := mem_insert1
  have asucc : Γ ≤ a ∈ᴮ succ a := by rw [ms]; exact bv_refl.trans le_sup_left
  have last : Γ ≤ edge k a C := graphValue_pair_mem hk asucc
  have label : Γ ≤ graphValue P g a =ᴮ q := graphValue_eq_of_pair hg pair_mem_insertPair
  have held : Γ ≤ survives (image a V k) q := pre_survives hprefix ((old.2 le_rfl hq).mpr hqx)
  have labelHeld : Γ ≤ survives (image a V k) (graphValue P g a) := allIn_intro fun hd _ hc =>
    mem_congr (bv_symm (hd.trans label)) bv_refl (allIn_elim (hd.trans held) hc)
  refine ⟨hq,?_⟩
  intro Δ hd z hz
  constructor
  · intro surviving
    have zc := allIn_elim surviving (mem_image (hd.trans last) (hd.trans asucc)
      (projection_function_bounds (hd.trans hk) (hd.trans last)).2)
    have cmp := (row_mem (hd.trans klaw) (hd.trans last)).mp zc
    exact mem_congr (pair_congr bv_refl (hd.trans label)) bv_refl
      (projection_imp.mp cmp.2.2 Δ le_rfl (hd.trans labelHeld))
  · intro zq
    have zx := internalOrder_trans (hd.trans po) zq (hd.trans hqx)
    have zPast := pre_survives (hd.trans hprefix) ((old.2 hd hz).mpr zx)
    have zLast : Δ ≤ z ∈ᴮ C := (row_mem (hd.trans klaw) (hd.trans last)).mpr
      ⟨hz,zPast,projection_imp.mpr fun _ ds _ => mem_congr (pair_congr bv_refl (bv_symm ((ds.trans hd).trans label)))
        bv_refl (ds.trans zq)⟩
    apply allIn_intro
    intro d dΔ row hrow
    obtain ⟨j,hj⟩ := exists_convert (mem_image_iff.mp hrow).2 (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    have where' := hj.trans inf_le_left
    rw [ms] at where'
    apply (le_inf le_rfl where').trans
    rw [inf_sup_left]
    apply sup_le
    · have eq := eq_of_is_function_of_eq ((inf_le_left.trans (dΔ.trans hd)).trans hk) inf_le_right
        (inf_le_left.trans (hj.trans inf_le_right)) ((inf_le_left.trans (dΔ.trans hd)).trans last)
      exact mem_congr bv_refl (bv_symm eq) ((inf_le_left.trans dΔ).trans zLast)
    · exact allIn_elim ((inf_le_left.trans dΔ).trans zPast) (mem_image (inf_le_left.trans (hj.trans inf_le_right))
        inf_le_right (inf_le_left.trans (mem_image_iff.mp hrow).1))

/-- The named extension and an actual new evaluation history coexist on the original guard. -/
theorem exists_exact_lift {Γ : B} {K P R a f h x q : N} (po : Γ ≤ partialOrderValue P R)
    (ord : Γ ≤ Ord a) (short : Γ ≤ succ a ∈ᴮ K) (hf : Γ ≤ is_function a P f)
    (hh : Γ ≤ is_function a (bv_powerset P) h) (hlaw : Γ ≤ trace P R f h)
    (old : Represents Γ P R a h x) (hq : Γ ≤ q ∈ᴮ P) (hqx : Γ ≤ edge R q x) :
    ∃ g k : N, Γ ≤ f ⊆ᴮ g ∧ Γ ≤ succ a ∈ᴮ K ∧ Γ ≤ is_function (succ a) P g ∧
      Γ ≤ is_function (succ a) (bv_powerset P) k ∧ Γ ≤ trace P R g k ∧ Represents Γ P R (succ a) k q := by
  let g := append f a q
  obtain ⟨k,hk,klaw⟩ := exists_trace P R g (Ord_succ ord)
  exact ⟨g,k,subset_insertPair,short,append_func hf hq,hk,klaw,append_represents po ord hf hh hlaw old hq hqx hk klaw⟩

end bSet.ErdosShioyaInternal.CollapsePath
