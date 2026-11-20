/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaCollapseConditions
public import Erdos1172.Part4BooleanWeightedDenseBasis
public import Erdos1172.Part4BooleanSurjectionTransport

@[expose] public section

/-! # The generic surjection of the uncountable Lévy collapse -/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion bSet Lattice
open scoped Flypitch
universe u

namespace Erdos1172Shioya.Collapse

abbrev Algebra (κ : Cardinal.{u}) (α : Type u) := Completion (Condition κ α)

variable (κ : Cardinal.{u}) {α : Type u}

def entry (i : κ.ord.ToType) (x : α) : Algebra κ α :=
  ⨆ p : {p : Condition κ α // (i, x) ∈ p.graph}, condition p.val

theorem condition_le_entry {p : Condition κ α} {i : κ.ord.ToType} {x : α} (h : (i, x) ∈ p.graph) :
    condition p ≤ entry κ i x :=
  le_iSup (fun q : {q : Condition κ α // (i, x) ∈ q.graph} => condition q.val) ⟨p, h⟩

theorem entry_disjoint (i : κ.ord.ToType) {x y : α} (h : x ≠ y) :
    entry κ i x ⊓ entry κ i y = ⊥ := by
  unfold entry
  erw [iSup_inf_eq]
  apply bot_unique
  apply iSup_le
  intro p
  erw [inf_iSup_eq]
  apply iSup_le
  intro q
  apply Eq.le
  by_contra hn
  obtain ⟨r, hrp, hrq⟩ := (condition_inf_ne_bot_iff p.val q.val).mp hn
  exact h (r.functional (le_iff.mp hrp p.property) (le_iff.mp hrq q.property))

theorem entry_row [Nonempty α] (hκ : Cardinal.aleph0 ≤ κ) (i : κ.ord.ToType) :
    (⨆ x : α, entry κ i x) = ⊤ := by
  let D : Set (Condition κ α) := {p | ∃ x, (i, x) ∈ p.graph}
  have hD := iSup_condition_eq_top_of_dense D (fun p => by
    obtain ⟨q, hq, hm⟩ := exists_assign hκ p i
    exact ⟨q, hm, hq⟩)
  apply eq_top_iff.mpr
  rw [← hD]
  apply iSup_le
  intro p
  obtain ⟨x, hx⟩ := p.property
  exact le_iSup_of_le x (condition_le_entry κ hx)

theorem entry_column (hκ : Cardinal.aleph0 ≤ κ) (x : α) :
    (⨆ i : κ.ord.ToType, entry κ i x) = ⊤ := by
  let D : Set (Condition κ α) := {p | ∃ i, (i, x) ∈ p.graph}
  have hD := iSup_condition_eq_top_of_dense D (fun p => by
    obtain ⟨q, hq, hm⟩ := exists_hit hκ p x
    exact ⟨q, hm, hq⟩)
  apply eq_top_iff.mpr
  rw [← hD]
  apply iSup_le
  intro p
  obtain ⟨i, hi⟩ := p.property
  exact le_iSup_of_le i (condition_le_entry κ hi)

variable [hκ : Fact (Cardinal.aleph0 ≤ κ)]

instance conditionNonempty : Nonempty (Condition κ α) := ⟨empty (Cardinal.aleph0_pos.trans_le hκ.out)⟩

instance algebraNontrivialCompleteBooleanAlgebra : NontrivialCompleteBooleanAlgebra (Algebra κ α) where
  toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra
  bot_lt_top := bot_lt_top

open bSet.ErdosWeightedDenseBasis

variable (o : Ordinal.{u})

def output (x : o.ToType) : bSet (Algebra κ o.ToType) := check (PSet.ordinalMk x.toOrd.val)

def row (i : κ.ord.ToType) : bSet (Algebra κ o.ToType) := mixture (entry κ i) (output κ o)

theorem row_agrees (i : κ.ord.ToType) (x : o.ToType) :
    entry κ i x ≤ row κ o i =ᴮ output κ o x := by
  apply mixing_lemma'
  intro y z
  by_cases h : y = z
  · subst z
    exact bv_refl
  · exact (entry_disjoint κ i h).le.trans bot_le

def genericGraph : bSet (Algebra κ o.ToType) := graph κ (fun _ => ⊤) (row κ o)

private theorem domain_eq_check :
    domain κ (fun _ => (⊤ : Algebra κ o.ToType)) = check (PSet.ordinalMk κ.ord) := by
  rw [PSet.ordinalMk_eq_def κ.ord, check_unfold]
  rfl

theorem generic_pair_of_entry (i : κ.ord.ToType) (x : o.ToType) :
    entry κ i x ≤ pair (label κ i) (output κ o x) ∈ᴮ genericGraph κ o :=
  mem_congr (pair_congr bv_refl (row_agrees κ o i x)) bv_refl
    (le_top.trans (pair_mem κ (fun _ => ⊤) (row κ o) i))

theorem generic_is_function [Nonempty o.ToType] :
    (⊤ : Algebra κ o.ToType) ≤ is_function (check (PSet.ordinalMk κ.ord))
      (check (PSet.ordinalMk o)) (genericGraph κ o) := by
  have H (i : κ.ord.ToType) : (⊤ : Algebra κ o.ToType) ≤ row κ o i ∈ᴮ check (PSet.ordinalMk o) := by
    rw [← entry_row (α := o.ToType) κ hκ.out i]
    apply iSup_le
    intro x
    apply bv_rw' (row_agrees κ o i x) (h_congr := B_ext_mem_left)
    exact check_mem (PSet.mk_mem_mk_of_lt x.toOrd.property)
  rw [← domain_eq_check κ o]
  have hfunc : (⊤ : Algebra κ o.ToType) ≤ is_func (genericGraph κ o) := by
    unfold genericGraph graph
    apply functionMk_is_func
  refine le_inf (le_inf hfunc ?_) ?_
  · apply le_iInf
    intro z
    rw [← deduction, top_inf_eq, mem_unfold]
    apply iSup_le
    intro i
    apply le_iSup_of_le (row κ o i)
    exact le_inf (le_top.trans (H i))
      (mem_congr (pair_congr (bv_symm inf_le_right) bv_refl) bv_refl
        (le_top.trans (pair_mem κ (fun _ => ⊤) (row κ o) i)))
  · rw [subset_unfold]
    apply le_iInf
    intro i
    change (⊤ : Algebra κ o.ToType) ≤ _root_.imp ⊤ _
    rw [top_imp]
    exact mem_prod_iff.mpr ⟨label_mem κ (fun _ => ⊤) i, H i⟩

theorem generic_is_surj :
    (⊤ : Algebra κ o.ToType) ≤ is_surj (check (PSet.ordinalMk κ.ord))
      (check (PSet.ordinalMk o)) (genericGraph κ o) := by
  unfold is_surj
  rw [← bounded_forall (h_congr := B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_pair_mem_right))]
  rw [PSet.ordinalMk_eq_def o, check_unfold]
  change (⊤ : Algebra κ o.ToType) ≤ ⨅ x : o.ToType, _root_.imp ⊤
    (⨆ z, z ∈ᴮ check (PSet.ordinalMk κ.ord) ⊓ pair z (output κ o x) ∈ᴮ genericGraph κ o)
  apply le_iInf
  intro x
  rw [top_imp]
  apply (entry_column κ hκ.out x).ge.trans
  apply iSup_le
  intro i
  exact le_iSup_of_le (label κ i) (le_inf (check_mem (PSet.mk_mem_mk_of_lt i.toOrd.property))
    (generic_pair_of_entry κ o i x))

theorem generic_surjection [Nonempty o.ToType] :
    (⊤ : Algebra κ o.ToType) ≤ is_function (check (PSet.ordinalMk κ.ord))
      (check (PSet.ordinalMk o)) (genericGraph κ o) ⊓ is_surj (check (PSet.ordinalMk κ.ord))
      (check (PSet.ordinalMk o)) (genericGraph κ o) :=
  le_inf (generic_is_function κ o) (generic_is_surj κ o)

theorem generic_pair_value (i : κ.ord.ToType) (x : o.ToType) :
    (pair (label κ i) (output κ o x) ∈ᴮ genericGraph κ o) = entry κ i x := by
  let : Nonempty o.ToType := ⟨x⟩
  apply le_antisymm _ (generic_pair_of_entry κ o i x)
  calc
    _ = (pair (label κ i) (output κ o x) ∈ᴮ genericGraph κ o) ⊓ (⨆ y : o.ToType, entry κ i y) := by
      rw [entry_row κ hκ.out]
      exact (inf_top_eq _).symm
    _ ≤ entry κ i x := by
      erw [inf_iSup_eq]
      apply iSup_le
      intro y
      by_cases he : x = y
      · subst y
        exact inf_le_right
      · have hne : ¬ PSet.Equiv (PSet.ordinalMk x.toOrd.val) (PSet.ordinalMk y.toOrd.val) :=
          fun h => he (Ordinal.ToType.mk.symm.injective (Subtype.ext (PSet.eq_of_mk_equiv h)))
        have hh : (pair (label κ i) (output κ o x) ∈ᴮ genericGraph κ o) ⊓ entry κ i y ≤
            output κ o x =ᴮ output κ o y := eq_of_is_function_of_eq (le_top.trans (generic_is_function κ o))
          (bv_refl : _ ≤ label κ i =ᴮ label κ i) inf_le_left
          (inf_le_right.trans (generic_pair_of_entry κ o i y))
        exact (hh.trans_eq (check_bv_eq_bot_of_not_equiv hne)).trans bot_le

theorem forces_surjects_onto [Nonempty o.ToType] :
    (⊤ : Algebra κ o.ToType) ≤ surjects_onto (check (PSet.ordinalMk κ.ord)) (check (PSet.ordinalMk o)) :=
  le_iSup_of_le (genericGraph κ o)
    (le_inf ((generic_is_function κ o).trans inf_le_left) (generic_is_surj κ o))

open bSet.ErdosNameTransport
variable {C : Type u} [NontrivialCompleteBooleanAlgebra C] (e : CompleteLatticeHom (Algebra κ o.ToType) C)

theorem mapped_pair_value (i : κ.ord.ToType) (x : o.ToType) :
    (pair (check (PSet.ordinalMk i.toOrd.val)) (check (PSet.ordinalMk x.toOrd.val)) ∈ᴮ
      mapNames e (genericGraph κ o)) = e (entry κ i x) := by
  simpa only [map_mem, map_pair, label, output, map_check] using congrArg e (generic_pair_value κ o i x)

theorem mapped_generic_surjection [Nonempty o.ToType] :
    (⊤ : C) ≤ is_function (check (PSet.ordinalMk κ.ord)) (check (PSet.ordinalMk o))
      (mapNames e (genericGraph κ o)) ⊓ is_surj (check (PSet.ordinalMk κ.ord)) (check (PSet.ordinalMk o))
      (mapNames e (genericGraph κ o)) := by
  exact le_inf (by simpa only [TopHomClass.map_top, map_check] using map_is_function_of e (generic_is_function κ o))
    (by simpa only [TopHomClass.map_top, map_check] using map_is_surj_of e (generic_is_surj κ o))

end Erdos1172Shioya.Collapse
