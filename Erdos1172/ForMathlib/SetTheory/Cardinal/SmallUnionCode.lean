/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.Data.W.Cardinal
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Cardinal-controlled codes for small unions and complements

These are well-founded expression trees, not finite-depth expressions.
Consequently their evaluations are closed under the stated infinitary union
operation. The cardinal estimate follows from the least-pre-fixed-point
property of W-types; no closure or enumeration assumption is introduced.
-/

open Cardinal Set

namespace SmallUnionCode

/-- Empty sets, complements, small unions, and the supplied atoms. -/
abbrev Arity (I B : Type) : Fin 3 ⊕ B → Type
  | .inl 0 => Empty
  | .inl 1 => Unit
  | .inl 2 => I
  | .inr _ => Empty

abbrev Code (I B : Type) : Type := WType (Arity I B)

variable {I B V : Type}

def empty : Code I B := WType.mk (.inl 0) Empty.elim

def compl (c : Code I B) : Code I B :=
  WType.mk (.inl 1) (fun _ => c)

def union (c : I → Code I B) : Code I B := WType.mk (.inl 2) c

def atom (b : B) : Code I B := WType.mk (.inr b) Empty.elim

def operate (atoms : B → Set V) :
    (Σ n, Arity I B n → Set V) → Set V
  | ⟨.inl 0, _⟩ => ∅
  | ⟨.inl 1, f⟩ => (f ())ᶜ
  | ⟨.inl 2, f⟩ => ⋃ i, f i
  | ⟨.inr b, _⟩ => atoms b

def eval (atoms : B → Set V) : Code I B → Set V :=
  WType.elim _ (operate atoms)

@[simp] theorem eval_empty (atoms : B → Set V) :
    eval atoms (empty : Code I B) = ∅ := rfl

@[simp] theorem eval_compl (atoms : B → Set V) (c : Code I B) :
    eval atoms (compl c) = (eval atoms c)ᶜ := rfl

@[simp] theorem eval_union (atoms : B → Set V) (c : I → Code I B) :
    eval atoms (union c) = ⋃ i, eval atoms (c i) := rfl

@[simp] theorem eval_atom (atoms : B → Set V) (b : B) :
    eval atoms (atom b : Code I B) = atoms b := rfl

/-- A cardinal bound for the full, infinitarily closed syntax. -/
theorem mk_code_le {μ κ : Cardinal.{0}}
    (hμ : 1 ≤ μ) (hκ : ℵ₀ ≤ κ) (hI : #I ≤ μ) (hB : #B ≤ κ)
    (hpower : κ ^ μ ≤ κ) : #(Code I B) ≤ κ := by
  have hshape : #(Fin 3 ⊕ B) ≤ κ := by
    simp only [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.mk_fin]
    exact (add_le_add ((Cardinal.natCast_le_aleph0 : (3 : Cardinal) ≤ ℵ₀).trans
      hκ) hB).trans_eq (Cardinal.add_eq_self hκ)
  have harity : ∀ n : Fin 3 ⊕ B, #(Arity I B n) ≤ μ := by
    rintro (n | b)
    · fin_cases n
      · simpa only [Arity, Cardinal.mk_eq_zero] using (_root_.zero_le : 0 ≤ μ)
      · simpa only [Arity, Cardinal.mk_eq_one Unit] using hμ
      · exact hI
    · simpa only [Arity, Cardinal.mk_eq_zero] using (_root_.zero_le : 0 ≤ μ)
  apply WType.cardinalMk_le_of_le
  calc
    (Cardinal.sum fun n : Fin 3 ⊕ B => κ ^ #(Arity I B n)) ≤
        #(Fin 3 ⊕ B) * ⨆ n : Fin 3 ⊕ B, κ ^ #(Arity I B n) :=
      Cardinal.sum_le_mk_mul_iSup _
    _ ≤ κ * κ := mul_le_mul' hshape (ciSup_le' fun n =>
      (Cardinal.power_le_power_left (Cardinal.aleph0_pos.trans_le hκ).ne'
        (harity n)).trans hpower)
    _ = κ := Cardinal.mul_eq_self hκ

/-- The represented sets, retaining explicit codes for subsequent reflection. -/
def family (atoms : B → Set V) : Set (Set V) := Set.range (eval (I := I) atoms)

theorem mk_family_le {μ κ : Cardinal.{0}} (atoms : B → Set V)
    (hμ : 1 ≤ μ) (hκ : ℵ₀ ≤ κ) (hI : #I ≤ μ) (hB : #B ≤ κ)
    (hpower : κ ^ μ ≤ κ) : #(family (I := I) atoms) ≤ κ :=
  Cardinal.mk_range_le.trans (mk_code_le hμ hκ hI hB hpower)

theorem empty_mem_family (atoms : B → Set V) :
    ∅ ∈ family (I := I) atoms := ⟨empty, rfl⟩

theorem atom_mem_family (atoms : B → Set V) (b : B) :
    atoms b ∈ family (I := I) atoms := ⟨atom b, rfl⟩

theorem compl_mem_family (atoms : B → Set V) {s : Set V}
    (hs : s ∈ family (I := I) atoms) : sᶜ ∈ family (I := I) atoms := by
  rcases hs with ⟨c, rfl⟩
  exact ⟨compl c, rfl⟩

theorem iUnion_mem_family (atoms : B → Set V) (s : I → Set V)
    (hs : ∀ i, s i ∈ family (I := I) atoms) :
    (⋃ i, s i) ∈ family (I := I) atoms := by
  choose c hc using hs
  exact ⟨union c, by simp only [eval_union, hc]⟩

/-- Padding an arbitrary smaller index type with the empty set gives closure
under all unions of cardinality at most the chosen arity. -/
theorem iUnion_mem_family_of_mk_le (atoms : B → Set V) {J : Type}
    (hJ : #J ≤ #I) (s : J → Set V)
    (hs : ∀ j, s j ∈ family (I := I) atoms) :
    (⋃ j, s j) ∈ family (I := I) atoms := by
  classical
  obtain ⟨e⟩ := (Cardinal.le_def J I).mp hJ
  let t : I → Set V := fun i => if h : ∃ j, e j = i then s h.choose else ∅
  have ht : ∀ i, t i ∈ family (I := I) atoms := by
    intro i
    dsimp only [t]
    split_ifs with h
    · exact hs h.choose
    · exact empty_mem_family atoms
  have hUnion : (⋃ i, t i) = ⋃ j, s j := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      dsimp only [t] at hi
      split_ifs at hi with h
      · exact ⟨h.choose, hi⟩
      · exact False.elim hi
    · rintro ⟨j, hj⟩
      refine ⟨e j, ?_⟩
      have h : ∃ j', e j' = e j := ⟨j, rfl⟩
      have he : h.choose = j := e.injective h.choose_spec
      simpa only [t, dif_pos h, he] using hj
  rw [← hUnion]
  exact iUnion_mem_family atoms t ht

end SmallUnionCode
