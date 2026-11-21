/-
Local Lean 4.33.1 compatibility changes for E1172, 2026-09-19.
Theorem statements and mathematical definitions are preserved.
See ../PROVENANCE.md for the pinned upstream source and modifications.
-/
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/pSet_ordinal.lean (lines 1-500) — Task 6a -/
module

public import Flypitch4.ToMathlib
public import Mathlib.SetTheory.ZFC.Basic
public import Mathlib.SetTheory.ZFC.Ordinal
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section

/-!
## Port notes (src/pSet_ordinal.lean → Flypitch4.PSetOrdinal)

### Key API renames

- `tactic.tidy` → `aesop` / `simp` / hand proofs
- `ordinal.limit_rec_on` → `induction η using Ordinal.limitRecOn`
- `ordinal.is_limit` → `Order.IsSuccLimit`
- `ordinal.lt_succ` / `lt_succ_self` → `Order.lt_succ`
- `ordinal.succ η` → `Order.succ η`
- `pSet` → `PSet`; `pSet.equiv` → `PSet.Equiv`; `pSet.mem.mk` → `PSet.Mem.mk`
- `pSet.succ x = insert x x` → `PSet.succ_ord x`
- `ordinal.mk` (Lean 3) → `Ordinal.toPSet` (mathlib4, aliased as `PSet.ordinalMk`)
- `mem_Union` → `PSet.mem_sUnion`
- `Set` (Lean 3 ZFC quotient) → `ZFSet`
- `Set.regularity` → `ZFSet.regularity`
- `push_neg` → `push Not` (deprecated, warning only)
- `ZFSet.not_mem_empty` → `ZFSet.notMem_empty`
- `⟦x⟧ : ZFSet` → `ZFSet.mk x` (more reliable elaboration)
- `typein` (in PSet namespace) → `Ordinal.typein` (fully qualified)
- `PSet.Type ∅ = PEmpty` (not `ULift Empty` as in Lean 3)
- `ordinal.mk_zero_type` etc: adapted to mathlib4 universe conventions

### Namespace choices for 6b, 6c

All declarations in `namespace PSet`.
`ordinalMk = Ordinal.toPSet`.
`succ_ord = insert x x`.
-/

universe u

noncomputable section

-- ============================================================
-- Ordinal namespace: tiny helper
-- ============================================================

namespace Ordinal

end Ordinal

-- ============================================================
-- PSet namespace
-- Lines 30+ of src/pSet_ordinal.lean
-- ============================================================

namespace PSet

-- `ordinalMk η` = `Ordinal.toPSet η` (the von Neumann ordinal as a pre-set).
abbrev ordinalMk : Ordinal.{u} → PSet.{u} := Ordinal.toPSet

-- `succ_ord x = insert x x` — the pre-set ordinal successor.
-- Named `succ_ord` to avoid collision with `Order.succ`.
@[reducible] def succ_ord (x : PSet) : PSet := insert x x

/-! ### Basic structural lemmas -/

@[simp] lemma mem_mk' {x : PSet} {i} : x.Func i ∈ x := PSet.func_mem x i

lemma mem_unfold {x y : PSet} : x ∈ y ↔ ∃ j : y.Type, Equiv x (y.Func j) := by
  cases y; rfl

/-! ### Key facts about ordinalMk = Ordinal.toPSet -/

-- The type of `ordinalMk η` is `η.ToType`
@[simp] lemma ordinalMk_type {η : Ordinal} : (ordinalMk η).Type = η.ToType :=
  Ordinal.type_toPSet η

-- Membership characterization (the main tool)
lemma mem_ordinalMk_iff {η : Ordinal} {x : PSet} :
    x ∈ ordinalMk η ↔ ∃ a < η, Equiv x (ordinalMk a) :=
  Ordinal.mem_toPSet_iff

-- Elementary membership
lemma mk_mem_mk_of_lt {ξ η : Ordinal} (H_lt : ξ < η) :
    ordinalMk ξ ∈ ordinalMk η :=
  mem_ordinalMk_iff.mpr ⟨ξ, H_lt, PSet.Equiv.refl _⟩

-- The zero case: ordinalMk 0 ≡ ∅ (extensionally equivalent)
-- Note: this is Equiv, not equality, since Ordinal.ToType 0 ≠ PEmpty definitionally
lemma ordinalMk_zero_equiv : PSet.Equiv (ordinalMk (0 : Ordinal.{u})) (∅ : PSet.{u}) := by
  apply PSet.Mem.ext; intro z
  simp [mem_ordinalMk_iff]

-- Successor: membership in ordinalMk(succ η) ↔ in ordinalMk η or ≡ ordinalMk η
lemma ordinalMk_succ_mem_iff {η : Ordinal} {x : PSet} :
    x ∈ ordinalMk (Order.succ η) ↔ x ∈ ordinalMk η ∨ Equiv x (ordinalMk η) := by
  rw [mem_ordinalMk_iff, mem_ordinalMk_iff]
  constructor
  · rintro ⟨a, ha, heq⟩
    rw [Order.lt_succ_iff] at ha
    rcases ha.eq_or_lt with rfl | hlt
    · right; exact heq
    · left; exact ⟨a, hlt, heq⟩
  · rintro (⟨a, ha, heq⟩ | heq)
    · exact ⟨a, ha.trans (Order.lt_succ η), heq⟩
    · exact ⟨η, Order.lt_succ η, heq⟩

/-! ### Epsilon well-orders and pre-set ordinals -/

def epsilon_well_orders (x : PSet.{u}) : Prop :=
  (∀ y, y ∈ x → (∀ z, z ∈ x → (Equiv y z ∨ y ∈ z ∨ z ∈ y))) ∧
  (∀ u, u ⊆ x → (¬ (Equiv u (∅ : PSet.{u})) → ∃ y, (y ∈ u ∧ (∀ z', z' ∈ u → ¬ z' ∈ y))))

def is_transitive (x : PSet) : Prop := ∀ y, y ∈ x → y ⊆ x

def Ord (x : PSet) : Prop := epsilon_well_orders x ∧ is_transitive x

lemma equiv_iff_eq {x y : PSet} : Equiv x y ↔ ZFSet.mk x = ZFSet.mk y :=
  ⟨ZFSet.sound, ZFSet.exact⟩

-- PSet membership ↔ ZFSet membership
lemma mem_iff {x y : PSet} : x ∈ y ↔ ZFSet.mk x ∈ ZFSet.mk y := by
  simp [ZFSet.mk_mem_iff]

-- Helpers for insert membership
lemma mem_insert_mem {x y z : PSet} (H : x ∈ insert y z) : Equiv x y ∨ x ∈ z :=
  PSet.mem_insert_iff.mp H

lemma mem_insert_intro {x y z : PSet} (H : Equiv x y ∨ x ∈ z) : x ∈ insert y z :=
  PSet.mem_insert_iff.mpr H

lemma subset_of_all_mem {x y : PSet} (H : ∀ z, z ∈ y → z ∈ x) : y ⊆ x :=
  PSet.subset_iff.mpr (fun _ hz => H _ hz)

lemma all_mem_of_subset {x y : PSet} (H : y ⊆ x) : ∀ z, z ∈ y → z ∈ x :=
  fun z hz => PSet.mem_of_subset H hz

lemma exists_mem_of_nonempty {x : PSet.{u}} (H : ¬ Equiv x (∅ : PSet.{u})) : ∃ y, y ∈ x := by
  by_contra h
  push_neg at h
  exact H (PSet.Mem.ext (fun w => ⟨fun hw => absurd hw (h w),
    fun hw => absurd hw (PSet.notMem_empty w)⟩))

lemma not_empty_of_not_equiv_empty {x : PSet.{u}} (H : ¬ Equiv x (∅ : PSet.{u})) :
    ZFSet.mk x ≠ ∅ := by
  intro H'
  apply H
  -- ZFSet.mk x = ∅ = ZFSet.mk ∅, so exact ZFSet.exact H'
  have : ZFSet.mk x = ZFSet.mk (∅ : PSet.{u}) := by
    rw [H']; rfl
  exact ZFSet.exact this

lemma is_epsilon_well_founded (x : PSet.{u}) :
    ∀ (u : PSet.{u}), u ⊆ x → ¬ Equiv u (∅ : PSet.{u}) →
    ∃ (y : PSet), y ∈ u ∧ ∀ (z' : PSet), z' ∈ u → z' ∉ y := by
  intro u _Hu Hu_ne_empty
  classical
  by_contra h
  push_neg at h
  -- h : ∀ y ∈ u, ∃ z ∈ u, z ∈ y
  have Hu_ne : ZFSet.mk u ≠ ∅ := not_empty_of_not_equiv_empty Hu_ne_empty
  obtain ⟨y, Hy₁, Hy₂⟩ := ZFSet.regularity (ZFSet.mk u) Hu_ne
  -- y is a ZFSet with y ∈ ZFSet.mk u and (ZFSet.mk u) ∩ y = ∅
  -- Get a PSet representative: y.out is a PSet with ZFSet.mk y.out = y
  have Hy₁' : y.out ∈ u := by
    have : ZFSet.mk y.out ∈ ZFSet.mk u := by
      rw [ZFSet.mk_out y]; exact Hy₁
    exact mem_iff.mpr this
  obtain ⟨z, Hz₁, Hz₂⟩ := h y.out Hy₁'
  -- z ∈ u and z ∈ y.out → contradiction since ZFSet.mk u ∩ y = ∅
  apply ZFSet.notMem_empty (ZFSet.mk z)
  rw [← Hy₂]
  apply ZFSet.mem_inter.mpr
  exact ⟨mem_iff.mp Hz₁, by rw [← ZFSet.mk_out y]; exact mem_iff.mp Hz₂⟩

@[simp] lemma Ord_empty : Ord (∅ : PSet.{u}) := by
  refine ⟨⟨fun y hy => absurd hy (PSet.notMem_empty y), ?_⟩,
    fun y hy => absurd hy (PSet.notMem_empty y)⟩
  intro u Hu H₂
  exact absurd (PSet.Mem.ext (fun w => ⟨
    fun hw => absurd (all_mem_of_subset Hu w hw) (PSet.notMem_empty w),
    fun hw => absurd hw (PSet.notMem_empty w)⟩)) H₂

lemma well_founded (u : PSet.{u}) (H_nonempty : ¬ Equiv u (∅ : PSet.{u})) :
    ∃ (y : PSet), y ∈ u ∧ ∀ (z' : PSet), z' ∈ u → z' ∉ y := by
  have Hu_ne : ZFSet.mk u ≠ ∅ := not_empty_of_not_equiv_empty H_nonempty
  obtain ⟨y, H₁, H₂⟩ := ZFSet.regularity (ZFSet.mk u) Hu_ne
  refine ⟨y.out, ?_, ?_⟩
  · have : ZFSet.mk y.out ∈ ZFSet.mk u := by rw [ZFSet.mk_out y]; exact H₁
    exact mem_iff.mpr this
  · intro z' Hz' Hz''
    apply ZFSet.notMem_empty (ZFSet.mk z')
    rw [← H₂]
    exact ZFSet.mem_inter.mpr
      ⟨mem_iff.mp Hz', by rw [← ZFSet.mk_out y]; exact mem_iff.mp Hz''⟩

lemma transitive_succ_ord (x : PSet) (H : is_transitive x) : is_transitive (succ_ord x) := by
  intro y Hy
  rcases mem_insert_mem Hy with heq | hin
  · exact subset_of_all_mem fun z hz =>
      mem_insert_intro (Or.inr ((PSet.Mem.congr_right heq).mp hz))
  · exact subset_of_all_mem fun z hz =>
      mem_insert_intro (Or.inr (all_mem_of_subset (H y hin) z hz))

@[simp] lemma Ord_succ_ord (x : PSet) (H : Ord x) : Ord (succ_ord x) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro y Hy z Hz
    rcases mem_insert_mem Hy with heq1 | hin1 <;>
    rcases mem_insert_mem Hz with heq2 | hin2
    · left; exact PSet.Equiv.trans heq1 heq2.symm
    · right; right; exact (PSet.Mem.congr_right heq1).mpr hin2
    · right; left; exact (PSet.Mem.congr_right heq2).mpr hin1
    · exact H.left.left y hin1 z hin2
  · intro u _Hu H_nonempty; exact well_founded u H_nonempty
  · exact transitive_succ_ord x H.right

lemma ordinalMk_lt_of_mem {ξ η : Ordinal} (H : ordinalMk ξ ∈ ordinalMk η) : ξ < η := by
  rw [mem_ordinalMk_iff] at H
  obtain ⟨a, ha, heq⟩ := H
  rcases lt_trichotomy ξ a with h | rfl | h
  · exact h.trans ha
  · exact ha
  · exfalso
    have h1 : ordinalMk a ∈ ordinalMk ξ := mk_mem_mk_of_lt h
    -- heq : Equiv (ordinalMk ξ) (ordinalMk a)
    -- Mem.congr_right heq : ∀ {w}, w ∈ ordinalMk ξ ↔ w ∈ ordinalMk a
    have h2 : ordinalMk a ∈ ordinalMk a := (PSet.Mem.congr_right heq).mp h1
    exact PSet.mem_irrefl _ h2

lemma equiv_mk_of_mem_mk {η : Ordinal} :
    ∀ x, x ∈ ordinalMk η → ∃ ρ < η, Equiv x (ordinalMk ρ) :=
  fun x hx => mem_ordinalMk_iff.mp hx

lemma Ord_limit : ∀ (o : Ordinal), Order.IsSuccLimit o →
    (∀ (o' : Ordinal), o' < o → Ord (ordinalMk o')) → Ord (ordinalMk o) := by
  intro η _Hη _ih
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x Hx z Hz
    obtain ⟨ξ₁, H₁, H₂⟩ := equiv_mk_of_mem_mk x Hx
    obtain ⟨ξ₂, H₁', H₂'⟩ := equiv_mk_of_mem_mk z Hz
    rcases lt_trichotomy ξ₁ ξ₂ with hlt | rfl | hlt
    · right; left
      rw [PSet.Mem.congr_left H₂, PSet.Mem.congr_right H₂']
      exact mk_mem_mk_of_lt hlt
    · left; exact PSet.Equiv.trans H₂ H₂'.symm
    · right; right
      rw [PSet.Mem.congr_right H₂, PSet.Mem.congr_left H₂']
      exact mk_mem_mk_of_lt hlt
  · intro u _Hu H_nonempty; exact well_founded u H_nonempty
  · intro y Hy
    obtain ⟨ρ, Hρ, Heq⟩ := equiv_mk_of_mem_mk y Hy
    rw [PSet.Subset.congr_left Heq]
    apply subset_of_all_mem; intro z Hz
    obtain ⟨σ, Hσ, Heq'⟩ := equiv_mk_of_mem_mk z Hz
    rw [PSet.Mem.congr_left Heq']
    exact mk_mem_mk_of_lt (Hσ.trans Hρ)

-- Ord is invariant under PSet.Equiv
lemma Ord_equiv {x y : PSet.{u}} (hxy : PSet.Equiv x y) (hx : Ord x) : Ord y := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- trichotomy: a ∈ y, b ∈ y → a and b are trichotomous
    intro a Ha b Hb
    have Ha' : a ∈ x := (PSet.Mem.congr_right hxy.symm).mp Ha
    have Hb' : b ∈ x := (PSet.Mem.congr_right hxy.symm).mp Hb
    exact hx.left.left a Ha' b Hb'
  · -- well-foundedness
    intro u _Hu H_ne; exact well_founded u H_ne
  · -- transitivity: a ∈ y → a ⊆ y
    intro a Ha
    have Ha' : a ∈ x := (PSet.Mem.congr_right hxy.symm).mp Ha
    -- a ⊆ x (from hx.right)
    have hax : a ⊆ x := hx.right a Ha'
    -- a ⊆ y: for w ∈ a, w ∈ x, so w ∈ y
    apply subset_of_all_mem
    intro w Hw
    exact (PSet.Mem.congr_right hxy).mp (all_mem_of_subset hax w Hw)

-- Key: ordinalMk (Order.succ η) ≡ succ_ord (ordinalMk η)
lemma ordinalMk_succ_equiv {η : Ordinal} :
    PSet.Equiv (ordinalMk (Order.succ η)) (succ_ord (ordinalMk η)) := by
  apply PSet.Mem.ext; intro z
  rw [ordinalMk_succ_mem_iff, PSet.mem_insert_iff]
  tauto

@[simp] lemma Ord_mk (η : Ordinal) : Ord (ordinalMk η) := by
  induction η using Ordinal.limitRecOn with
  | zero => exact Ord_equiv ordinalMk_zero_equiv.symm Ord_empty
  | add_one η ih =>
    -- ordinalMk_succ_equiv : Equiv (ordinalMk (succ η)) (succ_ord (ordinalMk η))
    -- Ord_succ_ord _ ih : Ord (succ_ord (ordinalMk η))
    -- Apply Ord_equiv in reverse: Equiv y x → Ord y → Ord x
    exact Ord_equiv ordinalMk_succ_equiv.symm (Ord_succ_ord _ ih)
  | limit η H_limit ih => exact Ord_limit η H_limit ih

-- ============================================================
-- Task 6b additions: lines 512-1000 of src/pSet_ordinal.lean
-- ============================================================

/-! ### Injectivity of ordinalMk (src lines 512-618) -/

/-- Helper: structural equation for `Ordinal.toPSet`. The `eq_def` form. -/
lemma ordinalMk_eq_def (o : Ordinal.{u}) :
    ordinalMk o = ⟨o.ToType, fun a : o.ToType => ordinalMk a.toOrd.val⟩ :=
  Ordinal.toPSet.eq_def o

/-- Injectivity: `ordinalMk η₁ ≡ ordinalMk η₂` → `η₁ = η₂`.
    Port of `eq_of_mk_equiv` (src/pSet_ordinal.lean:604). -/
lemma eq_of_mk_equiv {η₁ η₂ : Ordinal} (H_equiv : Equiv (ordinalMk η₁) (ordinalMk η₂)) :
    η₁ = η₂ := by
  refine le_antisymm ?_ ?_
  · rw [← not_lt]; intro H_lt
    -- H_lt : η₂ < η₁ (from not_lt of η₁ ≤ η₂)
    -- H_mem : ordinalMk η₂ ∈ ordinalMk η₁
    have H_mem := mk_mem_mk_of_lt H_lt
    -- Want: ordinalMk η₁ ∈ ordinalMk η₁
    -- Mem.congr_left H_equiv : ordinalMk η₁ ∈ w ↔ ordinalMk η₂ ∈ w
    -- .mpr H_mem (H_mem : ordinalMk η₂ ∈ ordinalMk η₁) gives ordinalMk η₁ ∈ ordinalMk η₁
    exact PSet.mem_irrefl _ ((PSet.Mem.congr_left H_equiv).mpr H_mem)
  · rw [← not_lt]; intro H_lt
    -- H_lt : η₁ < η₂ (from not_lt of η₂ ≤ η₁)
    have H_mem := mk_mem_mk_of_lt H_lt
    -- Mem.congr_left H_equiv.symm : ordinalMk η₂ ∈ w ↔ ordinalMk η₁ ∈ w
    -- .mpr H_mem (H_mem : ordinalMk η₁ ∈ ordinalMk η₂) gives ordinalMk η₂ ∈ ordinalMk η₂
    exact PSet.mem_irrefl _ ((PSet.Mem.congr_left H_equiv.symm).mpr H_mem)

/-- The func of ordinalMk η at distinct indices gives inequivalent pSets.
    Port of `ordinal.mk_inj` (src/pSet_ordinal.lean:595). -/
lemma ordinalMk_inj (η : Ordinal.{u}) :
    ∀ (i j : (ordinalMk η).Type), i ≠ j →
      ¬ Equiv ((ordinalMk η).Func i) ((ordinalMk η).Func j) := by
  intro i j hij heq
  apply hij
  -- Extract the HEq characterization of `(ordinalMk η).Func`.
  have hfunc : HEq (ordinalMk η).Func
      (fun a : η.ToType => ordinalMk a.toOrd.val) := by
    rw [ordinalMk_eq_def]; rfl
  -- Type equality.
  have htype : (ordinalMk η).Type = η.ToType := ordinalMk_type
  -- Cast i, j to η.ToType.
  let i' : η.ToType := cast htype i
  let j' : η.ToType := cast htype j
  have hi : HEq i i' := (cast_heq htype i).symm
  have hj : HEq j j' := (cast_heq htype j).symm
  -- `congr_heq` produces `Eq` directly when applied to a `Pi` and a `Sigma` of HEq.
  have heqi : (ordinalMk η).Func i = ordinalMk i'.toOrd.val :=
    congr_heq hfunc hi
  have heqj : (ordinalMk η).Func j = ordinalMk j'.toOrd.val :=
    congr_heq hfunc hj
  rw [heqi, heqj] at heq
  -- heq : Equiv (ordinalMk i'.toOrd.val) (ordinalMk j'.toOrd.val)
  have h_ord_eq : i'.toOrd.val = j'.toOrd.val := eq_of_mk_equiv heq
  have h_toOrd : i'.toOrd = j'.toOrd := Subtype.ext h_ord_eq
  have h_inj : i' = j' :=
    Ordinal.ToType.mk.symm.injective h_toOrd
  -- Cast both back.
  have : (cast htype.symm (cast htype i) : (ordinalMk η).Type) =
         cast htype.symm (cast htype j) :=
    congrArg (cast htype.symm) h_inj
  simpa using this

/-! ### Cardinal type size lemmas (src lines 620-666) -/

open Cardinal in
/-- The cardinality of `(ordinalMk (κ.ord)).Type` equals `κ`, for infinite `κ`.
    Port of `mk_type_mk_eq` (src/pSet_ordinal.lean:620). -/
lemma mk_type_mk_eq (κ : Cardinal) (H_inf : ℵ₀ ≤ κ) :
    Cardinal.mk (ordinalMk (Cardinal.ord κ)).Type = κ := by
  simp only [ordinalMk_type]
  exact Cardinal.mk_ord_toType κ

open Cardinal in
/-- The cardinality of `(ordinalMk η).Type` is `η.card`.
    Port of `ordinal.mk_card` (src/pSet_ordinal.lean:645). -/
lemma ordinalMk_card {η : Ordinal} : Cardinal.mk (ordinalMk η).Type = η.card := by
  simp [Cardinal.mk_toType]

open Cardinal in
@[simp] lemma mk_omega_eq_mk_omega :
    Cardinal.mk (PSet.omega).Type = ℵ₀ := by
  simp only [PSet.omega]
  rw [show (⟨ULift ℕ, fun n => PSet.ofNat n.down⟩ : PSet).Type = ULift ℕ from rfl]
  simp [Cardinal.mk_nat]

/-! ### Ordinal arithmetic helpers (src lines 668-697) -/

/-! ### Subset helpers (src lines 698-704) -/

lemma subset_trans {x y z : PSet} : x ⊆ y → y ⊆ z → x ⊆ z := by
  intro Hxy Hyz
  apply subset_of_all_mem
  intro w hw
  exact all_mem_of_subset Hyz w (all_mem_of_subset Hxy w hw)

@[simp] lemma subset_self {x : PSet} : x ⊆ x :=
  subset_of_all_mem fun _ h => h

/-! ### ofNat lemmas (src lines 706-768) -/
-- In mathlib4, Lean 3's `of_nat` is `PSet.ofNat`.
-- Lean 3 omega.type = ℕ-indexed; mathlib4 uses ULift ℕ.

lemma ofNat_succ {k : ℕ} : PSet.ofNat (k + 1) = succ_ord (PSet.ofNat k) := by
  simp [PSet.ofNat, succ_ord]

lemma ofNat_of_mem_ofNat {y : PSet.{u}} {k : ℕ}
    (H_mem : y ∈ (PSet.ofNat k : PSet.{u})) :
    ∃ j, Equiv y (PSet.ofNat j : PSet.{u}) := by
  induction k with
  | zero => exact absurd H_mem (PSet.notMem_empty _)
  | succ k ih =>
    rw [ofNat_succ, succ_ord] at H_mem
    rcases PSet.mem_insert_iff.mp H_mem with heq | hin
    · exact ⟨k, heq⟩
    · exact ih hin

lemma ofNat_mem_of_lt {k₁ k₂ : ℕ} (H_lt : k₁ < k₂) :
    (PSet.ofNat k₁ : PSet.{u}) ∈ (PSet.ofNat k₂ : PSet.{u}) := by
  induction H_lt with
  | refl =>
    rw [ofNat_succ, succ_ord]
    exact PSet.mem_insert_iff.mpr (Or.inl (PSet.Equiv.refl _))
  | step _ ih =>
    rw [ofNat_succ, succ_ord]
    exact PSet.mem_insert_iff.mpr (Or.inr ih)

/-! ### Transitivity and well-orders for omega (src lines 770-800) -/

lemma is_transitive_omega : is_transitive (PSet.omega : PSet.{u}) := by
  intro z Hz
  rw [PSet.mem_def] at Hz
  obtain ⟨⟨k⟩, Hk⟩ := Hz
  apply subset_of_all_mem; intro y Hy
  rw [PSet.mem_def]
  -- omega.Type = ULift ℕ; Func ⟨k⟩ = ofNat k
  simp only [PSet.omega]
  -- Hy : y ∈ z, Hk : Equiv z (ofNat k)
  -- So y ∈ ofNat k; find j with y ≡ ofNat j
  obtain ⟨j, hj⟩ := ofNat_of_mem_ofNat ((PSet.Mem.congr_right Hk).mp Hy)
  exact ⟨⟨j⟩, hj⟩

lemma is_ewo_omega : epsilon_well_orders (PSet.omega : PSet.{u}) := by
  constructor
  · -- trichotomy
    intro y Hy z Hz
    rw [PSet.mem_def] at Hy Hz
    obtain ⟨⟨k₁⟩, Hk₁⟩ := Hy
    obtain ⟨⟨k₂⟩, Hk₂⟩ := Hz
    rcases lt_trichotomy k₁ k₂ with h | rfl | h
    · right; left
      rw [PSet.Mem.congr_left Hk₁, PSet.Mem.congr_right Hk₂]
      exact ofNat_mem_of_lt h
    · left; exact PSet.Equiv.trans Hk₁ Hk₂.symm
    · right; right
      rw [PSet.Mem.congr_left Hk₂, PSet.Mem.congr_right Hk₁]
      exact ofNat_mem_of_lt h
  · exact is_epsilon_well_founded _

/-- Injectivity of `ofNat`.
    Port of `of_nat_inj` (src/pSet_ordinal.lean:792). -/
lemma ofNat_inj {n k : ℕ} (H_neq : n ≠ k) :
    ¬ Equiv (PSet.ofNat n : PSet.{u}) (PSet.ofNat k : PSet.{u}) := by
  intro H
  rcases lt_trichotomy n k with h | rfl | h
  · exact PSet.mem_irrefl (PSet.ofNat n)
      ((PSet.Mem.congr_right H).mpr (ofNat_mem_of_lt h))
  · exact H_neq rfl
  · exact PSet.mem_irrefl (PSet.ofNat k)
      ((PSet.Mem.congr_right H.symm).mpr (ofNat_mem_of_lt h))

/-- The indexing function for omega is injective.
    Port of `omega_inj` (src/pSet_ordinal.lean:798). -/
lemma omega_inj {n k : PSet.omega.Type} :
    Equiv (PSet.omega.Func n) (PSet.omega.Func k) → n = k := by
  intro H
  cases n with | up n => cases k with | up k =>
  suffices h : n = k by subst h; rfl
  by_contra H'
  exact ofNat_inj H' H

/-! ### Pair and product for pSets (src lines 945-984) -/

/-- The ordered pair pSet `{{x}, {x, y}}`. -/
def pSet_pair (x y : PSet.{u}) : PSet.{u} := {{x}, {x, y}}

lemma pSet_pair_sound {x y : PSet.{u}} :
    ZFSet.mk (pSet_pair x y) = ZFSet.pair (ZFSet.mk x) (ZFSet.mk y) := rfl

lemma equiv_iff_eq_pSet_pair {x y x' y' : PSet.{u}} :
    Equiv x x' ∧ Equiv y y' ↔ Equiv (pSet_pair x y) (pSet_pair x' y') := by
  constructor
  · rintro ⟨H₁, H₂⟩
    apply ZFSet.exact
    simp only [pSet_pair_sound]
    rw [ZFSet.pair_inj]
    exact ⟨ZFSet.sound H₁, ZFSet.sound H₂⟩
  · intro H
    have h : ZFSet.pair (ZFSet.mk x) (ZFSet.mk y) =
             ZFSet.pair (ZFSet.mk x') (ZFSet.mk y') := by
      rw [← pSet_pair_sound, ← pSet_pair_sound]; exact ZFSet.sound H
    exact ⟨ZFSet.exact (ZFSet.pair_inj.mp h).1, ZFSet.exact (ZFSet.pair_inj.mp h).2⟩

/-- The cartesian product pSet. -/
def pSet_prod (x y : PSet.{u}) : PSet.{u} :=
  ⟨x.Type × y.Type, fun pr => pSet_pair (x.Func pr.1) (y.Func pr.2)⟩

/-! ### Injection predicates (src lines 986-990) -/

/-! ### Subset characterization via ZFSet (src/pSet_ordinal.lean:994-1000) -/

-- ============================================================
-- Task 6c additions: lines 1000-1391 of src/pSet_ordinal.lean
-- ============================================================

/-! ### is_func characterization (src lines 1002-1045) -/

/-! ### powerset_sound (src line 1047) -/

/-! ### set_of_indicator, functions, mem_functions_iff (src lines 1049-1067) -/

def set_of_indicator {x : PSet.{u}} (χ : x.Type → Prop) : PSet.{u} :=
  ⟨{i // χ i}, fun p => x.Func p.1⟩

/-! ### card_ex_aleph_exists_mem (src line 1071) -/

/-! ### function.mk and related (src lines 1080-1132) -/

namespace function_mk

/-- Build a pSet function graph from a family `ψ : x.Type → PSet`.
    Port of `pSet.function.mk` (src/pSet_ordinal.lean:1080). -/
def mk {x : PSet.{u}} (ψ : x.Type → PSet.{u})
    (H_ext : ∀ i j, Equiv (x.Func i) (x.Func j) → Equiv (ψ i) (ψ j)) : PSet.{u} :=
  ⟨x.Type, fun i => pSet_pair (x.Func i) (ψ i)⟩

end function_mk

/-! ### P_ext predicate (src lines 1144-1161) -/

/-! ### mem_sep_iff (src line 1163) -/

/-! ### sep_subset (src line 1134) -/

/-! ### sep_equiv_iff (src line 1179) -/

/-! ### mem_two (src line 1186) -/

/-! ### pair_mem.congr_right/left (src lines 1194-1215) -/

/-! ### section injects_powerset (src lines 1218-1369) -/

section injects_powerset

variable {x : PSet.{u}}

end injects_powerset

/-! ### eq_of_is_func_of_eq (src line 1372) -/

/-! ### exists_mem_of_nonzero, exists_mem_of_regular (src lines 1384-1388) -/

lemma exists_mem_of_nonzero {η : Ordinal} (H_nonzero : 0 < η) :
    ∃ z : PSet, z ∈ ordinalMk η :=
  ⟨ordinalMk 0, mk_mem_mk_of_lt H_nonzero⟩

end PSet

end -- noncomputable section
