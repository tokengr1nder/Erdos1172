/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanFunctionTransport
public import Erdos1172.Part4CohenIndexedBinaryAssignment
public import Erdos1172.Part4CohenIterationDensity

@[expose] public section

/-! # Binary names for the dual Shioya forcing

Definition 23 and Lemma 24 in §3 of Eskew and Hayut, *Dense ideals*
(arXiv:2410.14359v1), compare the translated binary function graphs by
extension at the stronger condition. The domain ordinal is fixed in the
ground model. Its individual bits have arbitrary Boolean truth values.
-/

set_option autoImplicit false
noncomputable section
open bSet bSet.ErdosNameTransport bSet.ErdosCohen Lattice
open scoped Flypitch
universe u

namespace Erdos1172Shioya

structure StringName (B : Type u) [NontrivialCompleteBooleanAlgebra B] (γ : Ordinal.{u}) where
  name : bSet B
  isFunction : (⊤ : B) ≤ is_function (check (PSet.ordinalMk γ)) (check (PSet.ofNat 2)) name

variable {B C D : Type u} [NontrivialCompleteBooleanAlgebra B]
  [NontrivialCompleteBooleanAlgebra C] [NontrivialCompleteBooleanAlgebra D]
variable {γ δ η : Ordinal.{u}}

namespace StringName

def map (e : CompleteLatticeHom B C) (s : StringName B γ) : StringName C γ where
  name := mapNames e s.name
  isFunction := by
    simpa only [TopHomClass.map_top, map_check] using map_is_function_of e s.isFunction

theorem map_id (s : StringName B γ) : s.map (CompleteLatticeHom.id B) = s := by
  cases s
  simp only [map, mapNames_id]

theorem map_comp (e : CompleteLatticeHom B C) (f : CompleteLatticeHom C D) (s : StringName B γ) :
    s.map (f.comp e) = (s.map e).map f := by
  cases s
  simp only [map, mapNames_comp]

def indices (γ : Ordinal.{u}) : PSet.{u} :=
  .mk γ.ToType (fun i => PSet.ordinalMk i.toOrd.val)

theorem indices_sep (γ : Ordinal.{u}) (i j : (indices γ).Type) (hne : i ≠ j) :
    ¬ PSet.Equiv ((indices γ).Func i) ((indices γ).Func j) :=
  fun he => hne (Ordinal.ToType.mk.symm.injective (Subtype.ext (PSet.eq_of_mk_equiv he)))

def ofBits (γ : Ordinal.{u}) (b : γ.ToType → B) : StringName B γ where
  name := indexedBinaryAssignment (indices γ) b (indices_sep γ)
  isFunction := by
    rw [PSet.ordinalMk_eq_def γ]
    exact indexedBinaryAssignment_is_function (indices γ) b (indices_sep γ)

def label (i : γ.ToType) : bSet B := check (PSet.ordinalMk i.toOrd.val)

def bits (s : StringName B γ) (i : γ.ToType) : B := pair (label i) (1 : bSet B) ∈ᴮ s.name

private theorem ofBits_one (b : γ.ToType → B) (i : γ.ToType) :
    b i ≤ (ofBits γ b).bits i :=
  indexedBinaryAssignment_one (indices γ) b (indices_sep γ) i

private theorem ofBits_zero (b : γ.ToType → B) (i : γ.ToType) :
    (b i)ᶜ ≤ pair (label i) (0 : bSet B) ∈ᴮ (ofBits γ b).name :=
  indexedBinaryAssignment_zero (indices γ) b (indices_sep γ) i

theorem zero_value (s : StringName B γ) (i : γ.ToType) :
    (pair (label i) (0 : bSet B) ∈ᴮ s.name) = (s.bits i)ᶜ := by
  apply le_antisymm
  · apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff_inf_le.mpr
    exact bot_of_zero_eq_one (eq_of_is_function_of_eq (le_top.trans s.isFunction)
      bv_refl inf_le_left inf_le_right)
  · let z := pair (label i) (0 : bSet B) ∈ᴮ s.name
    have hm : (⊤ : B) ≤ label i ∈ᴮ check (PSet.ordinalMk γ) :=
      check_mem (PSet.mk_mem_mk_of_lt i.toOrd.property)
    have ht : (⊤ : B) ≤ ⨆ y : bSet B, (y ∈ᴮ two) ⊓ (pair (label i) y ∈ᴮ s.name) :=
      (le_inf ((is_total_of_is_function s.isFunction).trans (iInf_le _ (label i))) hm).trans bv_imp_elim
    rw [← bounded_exists (h_congr := B_ext_pair_mem_right)] at ht
    have hcov : (⊤ : B) ≤ z ⊔ s.bits i := by
      apply ht.trans
      apply iSup_le
      intro j
      rcases Erdos1172CohenIteration.two_child_eq_zero_or_one j with hj | hj
      · rw [hj]
        exact inf_le_right.trans le_sup_left
      · rw [hj]
        exact inf_le_right.trans le_sup_right
    calc
      (s.bits i)ᶜ ≤ (s.bits i)ᶜ ⊓ (z ⊔ s.bits i) := le_inf le_rfl (le_top.trans hcov)
      _ ≤ z := by rw [inf_sup_left, compl_inf_self, sup_bot_eq]; exact inf_le_right

theorem bits_ofBits (b : γ.ToType → B) (i : γ.ToType) : (ofBits γ b).bits i = b i := by
  apply le_antisymm _ (ofBits_one b i)
  have hz := (ofBits_zero b i).trans_eq (zero_value (ofBits γ b) i)
  simpa only [compl_compl] using compl_le_compl hz

/-- The checked input positions and the two literal outputs suffice to
compare the graphs, including on conditions where their members are mixed. -/
theorem subset_of_coordinates (s : StringName B γ) (T : bSet B) (Γ : B)
    (h : ∀ i : γ.ToType, ∀ n : bSet B, n = 0 ∨ n = 1 →
      Γ ⊓ (pair (label i) n ∈ᴮ s.name) ≤ pair (label i) n ∈ᴮ T) : Γ ≤ s.name ⊆ᴮ T := by
  rw [subset_unfold']
  apply le_iInf
  intro z
  rw [← deduction]
  let d := Γ ⊓ (z ∈ᴮ s.name)
  have hz : d ≤ z ∈ᴮ prod (check (PSet.ordinalMk γ)) (two : bSet B) :=
    mem_of_mem_subset (le_top.trans (subset_prod_of_is_function s.isFunction)) inf_le_right
  rw [PSet.ordinalMk_eq_def γ, check_unfold, mem_unfold] at hz
  apply (le_inf (le_refl d) hz).trans
  rw [inf_iSup_eq]
  apply iSup_le
  rintro ⟨i, j⟩
  let n := (two : bSet B).func j
  let y := pair (label (B := B) i) n
  have hy : d ⊓ ((⊤ ⊓ (two : bSet B).bval j) ⊓ (z =ᴮ y)) ≤ z =ᴮ y := inf_le_right.trans inf_le_right
  apply bv_rw' hy (h_congr := B_ext_mem_left)
  exact (le_inf (inf_le_left.trans inf_le_left)
    (bv_rw'' hy (inf_le_left.trans inf_le_right) B_ext_mem_left)).trans
    (h i n (Erdos1172CohenIteration.two_child_eq_zero_or_one j))

theorem bits_map (e : CompleteLatticeHom B C) (s : StringName B γ) (i : γ.ToType) :
    (s.map e).bits i = e (s.bits i) := by
  change _ = e (pair (check (PSet.ordinalMk i.toOrd.val)) (check (PSet.ofNat 1)) ∈ᴮ s.name)
  rw [map_mem, map_pair, map_check, map_check]
  rfl

def includeIndex (h : γ ≤ δ) (i : γ.ToType) : δ.ToType :=
  Ordinal.ToType.mk (o := δ) ⟨i.toOrd.val, lt_of_lt_of_le (show i.toOrd.val < γ from i.toOrd.property) h⟩

theorem includeIndex_toOrd (h : γ ≤ δ) (i : γ.ToType) :
    (includeIndex h i).toOrd.val = i.toOrd.val :=
  congrArg Subtype.val ((Ordinal.ToType.mk (o := δ)).symm_apply_apply _)

def empty (B : Type u) [NontrivialCompleteBooleanAlgebra B] : StringName B 0 :=
  ofBits 0 (fun _ => ⊥)

end StringName

def extensionValue (e : CompleteLatticeHom B C) (s : StringName B γ) (t : StringName C δ) : C :=
  (s.map e).name ⊆ᴮ t.name

theorem extensionValue_refl (s : StringName B γ) :
    (⊤ : B) ≤ extensionValue (CompleteLatticeHom.id B) s s := by
  rw [extensionValue, StringName.map_id]
  exact subset_self

theorem extensionValue_trans (e : CompleteLatticeHom B C) (f : CompleteLatticeHom C D)
    (s : StringName B γ) (t : StringName C δ) (v : StringName D η) {p : D} {q : C}
    (hpq : p ≤ f q) (hq : q ≤ extensionValue e s t) (hp : p ≤ extensionValue f t v) :
    p ≤ extensionValue (f.comp e) s v := by
  unfold extensionValue at *
  rw [StringName.map_comp]
  apply subset_trans' _ hp
  exact hpq.trans ((OrderHomClass.mono f hq).trans_eq (map_subset f _ _))

open StringName

private theorem part_compl {V : Type u} [BooleanAlgebra V] {p a b : V}
    (h : p ⊓ a = p ⊓ b) : p ⊓ aᶜ ≤ bᶜ := by
  apply le_compl_iff_disjoint_right.mpr
  apply disjoint_iff_inf_le.mpr
  calc
    (p ⊓ aᶜ) ⊓ b = (p ⊓ b) ⊓ aᶜ := by ac_rfl
    _ = (p ⊓ a) ⊓ aᶜ := by rw [h]
    _ ≤ ⊥ := (inf_le_inf_right _ inf_le_right).trans inf_compl_eq_bot.le

theorem extensionValue_of_bits (e : CompleteLatticeHom B C) (s : StringName B γ)
    (t : StringName C δ) (h : γ ≤ δ) (Γ : C)
    (hb : ∀ i, Γ ⊓ e (s.bits i) = Γ ⊓ t.bits (includeIndex h i)) : Γ ≤ extensionValue e s t := by
  apply subset_of_coordinates
  intro i n hn
  have hl : (label (includeIndex h i) : bSet C) = label i := congrArg
    (fun o => (check (PSet.ordinalMk o) : bSet C)) (includeIndex_toOrd h i)
  rcases hn with rfl | rfl
  · rw [zero_value, ← hl, zero_value, bits_map]
    exact part_compl (hb i)
  · change Γ ⊓ (s.map e).bits i ≤ _
    rw [bits_map, ← hl]
    exact (hb i).le.trans inf_le_right

theorem length_le_of_extensionValue (e : CompleteLatticeHom B C) (s : StringName B γ)
    (t : StringName C δ) {Γ : C} (hΓ : Γ ≠ ⊥) (h : Γ ≤ extensionValue e s t) : γ ≤ δ := by
  by_contra! hlen
  let x : bSet C := check (PSet.ordinalMk δ)
  have hx : Γ ≤ x ∈ᴮ check (PSet.ordinalMk γ) := check_mem (PSet.mk_mem_mk_of_lt hlen)
  have ht : Γ ≤ ⨆ y : bSet C, (y ∈ᴮ two) ⊓ (pair x y ∈ᴮ (s.map e).name) :=
    (le_inf (le_top.trans ((is_total_of_is_function (s.map e).isFunction).trans (iInf_le _ x))) hx).trans bv_imp_elim
  obtain ⟨y, hy⟩ := exists_convert ht (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have hm := mem_domain_of_is_function (mem_of_mem_subset h (hy.trans inf_le_right)) (le_top.trans t.isFunction)
  exact hΓ (bot_unique (hm.trans_eq (not_check_mem_iff.mp (PSet.mem_irrefl _))))

private theorem part_inf_eq {V : Type u} [BooleanAlgebra V] {p a b : V}
    (ha : p ⊓ a ≤ b) (hc : p ⊓ aᶜ ≤ bᶜ) : p ⊓ a = p ⊓ b := by
  refine le_antisymm (le_inf inf_le_left ha) (le_inf inf_le_left (disjoint_compl_right_iff.mp ?_))
  apply disjoint_iff_inf_le.mpr
  calc
    (p ⊓ b) ⊓ aᶜ = (p ⊓ aᶜ) ⊓ b := by ac_rfl
    _ ≤ bᶜ ⊓ b := inf_le_inf_right _ hc
    _ ≤ ⊥ := (compl_inf_self b).le

theorem extensionValue_iff_bits (e : CompleteLatticeHom B C) (s : StringName B γ)
    (t : StringName C δ) {Γ : C} (hΓ : Γ ≠ ⊥) :
    Γ ≤ extensionValue e s t ↔ ∃ h : γ ≤ δ, ∀ i,
      Γ ⊓ e (s.bits i) = Γ ⊓ t.bits (includeIndex h i) := by
  constructor
  · intro hs
    let h := length_le_of_extensionValue e s t hΓ hs
    refine ⟨h, ?_⟩
    intro i
    have hl : (label (includeIndex h i) : bSet C) = label i := congrArg
      (fun o => (check (PSet.ordinalMk o) : bSet C)) (includeIndex_toOrd h i)
    have hpair (n : bSet C) :
        Γ ⊓ (pair (label i) n ∈ᴮ (s.map e).name) ≤ pair (label (includeIndex h i)) n ∈ᴮ t.name := by
      rw [hl]
      exact mem_of_mem_subset (inf_le_left.trans hs) inf_le_right
    apply part_inf_eq
    · rw [← bits_map]
      exact hpair 1
    · have hzero := hpair 0
      rw [zero_value, zero_value, bits_map] at hzero
      exact hzero
  · rintro ⟨h, hb⟩
    exact extensionValue_of_bits e s t h Γ hb

end Erdos1172Shioya
