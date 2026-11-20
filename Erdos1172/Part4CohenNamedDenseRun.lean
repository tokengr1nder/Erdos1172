/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCohenCountableUnion
public import Erdos1172.Part4InternalNameSequence

@[expose] public section

/-! # A ground-length run meeting named dense sets in the internal Cohen order -/

set_option autoImplicit false
noncomputable section
open bSet ErdosCohen ErdosOmegaTwo Lattice
open scoped Flypitch
universe u
namespace Erdos1172CohenIteration.NamedRun
variable {R : Type u} [NontrivialCompleteBooleanAlgebra R] {Γ : R} {θ : Cardinal.{u}}
local notation "J" => θ.ord.ToType
local notation "N" => bSet R

def dense (D : N) : R := ⨅ q : N, condition omegaOne q ⟹
  ⨆ r : N, condition omegaOne r ⊓ (q ⊆ᴮ r ⊓ r ∈ᴮ D)

theorem extends_of_dense {q D : N} (hD : Γ ≤ dense D) (hq : Γ ≤ condition omegaOne q) :
    ∃ r : N, Γ ≤ condition omegaOne r ∧ Γ ≤ q ⊆ᴮ r ∧ Γ ≤ r ∈ᴮ D := by
  have h := (le_inf (hD.trans (iInf_le _ q)) hq).trans bv_imp_elim
  obtain ⟨r,hr⟩ := exists_convert h (B_ext_inf (condition_ext_graph omegaOne) (B_ext_inf B_ext_subset_right B_ext_mem_left))
  exact ⟨r,hr.trans inf_le_left,hr.trans (inf_le_right.trans inf_le_left),hr.trans (inf_le_right.trans inf_le_right)⟩

def family {V : Type u} (f : V → N) : N := .mk V f (fun _ => ⊤)

private theorem family_union_extends {V : Type u} (f : V → N) (v : V) : Γ ≤ f v ⊆ᴮ bv_union (family f) := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  exact (bv_union_spec_split (family f) x).mpr (le_iSup_of_le (f v) (le_inf (le_top.trans (mem_mk' (family f) v)) inf_le_right))

private theorem family_chain {V : Type u} [LinearOrder V] (f : V → N)
    (mono : ∀ i j, i ≤ j → Γ ≤ f i ⊆ᴮ f j) : Γ ≤ ErdosInjectionChain.inclusionChain (family f) := by
  let C := family f
  have main : Γ ≤ ⨅ x : N, _root_.imp (x ∈ᴮ C) (⨅ y : N, _root_.imp (y ∈ᴮ C) (x ⊆ᴮ y ⊔ y ⊆ᴮ x)) := by
    rw [← (bounded_forall (v := C) (h_congr := B_ext_iInf (h := fun _ => B_ext_imp
      (h₁ := B_ext_const) (h₂ := B_ext_sup (h₁ := B_ext_subset_left) (h₂ := B_ext_subset_right)))))]
    apply le_iInf
    intro i
    rw [← deduction,← (bounded_forall (v := C)
      (h_congr := B_ext_sup (h₁ := B_ext_subset_right) (h₂ := B_ext_subset_left)))]
    apply le_iInf
    intro j
    rw [← deduction]
    rcases @le_total V _ i j with h | h
    · exact (inf_le_left.trans inf_le_left).trans ((mono i j h).trans le_sup_left)
    · exact (inf_le_left.trans inf_le_left).trans ((mono j i h).trans le_sup_right)
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  have h : Γ ⊓ (x ∈ᴮ C ⊓ y ∈ᴮ C) ≤ ⨅ y : N, _root_.imp (y ∈ᴮ C) (x ⊆ᴮ y ⊔ y ⊆ᴮ x) :=
    (le_inf (inf_le_left.trans (main.trans (iInf_le _ x))) (inf_le_right.trans inf_le_left)).trans bv_imp_elim
  exact (le_inf (h.trans (iInf_le _ y)) (inf_le_right.trans inf_le_right)).trans bv_imp_elim

theorem prefix_union_condition (hs : Γ ≤ (omegaOne : N) =ᴮ check (PSet.ordinalMk θ.ord))
    (j : J) (s : Set.Iio j → N) (valid : ∀ i, Γ ≤ condition omegaOne (s i))
    (mono : ∀ i k, i ≤ k → Γ ≤ s i ⊆ᴮ s k) : Γ ≤ condition omegaOne (bv_union (family s)) := by
  let μ := Cardinal.mk (Set.Iio j)
  have hμ : μ < θ := (Cardinal.mk_Iio_lt j (by simp)).trans_eq (Cardinal.mk_ord_toType _)
  have sm : Γ ≤ injects_into (family s) (check (PSet.ordinalMk μ.ord)) :=
    le_top.trans (ErdosGroundIndexNameBound.injects_checked_cardinal_of_index_cardinal_le μ (family s) le_rfl)
  have mem : Γ ≤ check (PSet.ordinalMk μ.ord) ∈ᴮ (omegaOne : N) :=
    mem_congr bv_refl (bv_symm hs) (check_mem (PSet.mk_mem_mk_of_lt (Cardinal.ord_lt_ord.mpr hμ)))
  apply condition_union_of_countable_chain omegaOne_property _ (family_chain s mono)
    (injects_into_trans sm (omegaOne_member_injects mem))
  rw [subset_unfold]
  apply le_iInf
  intro i
  rw [← deduction]
  exact inf_le_left.trans (mem_conditions_iff.mpr (valid i))

/-- Each dense set has an actual mixed member in the descending run.
Every stage extends the specified master. Proper initial segments can
have any ground cardinality below θ, since they are internally countable. -/
theorem exists_dense_run (hs : Γ ≤ (omegaOne : N) =ᴮ check (PSet.ordinalMk θ.ord))
    (master : N) (hm : Γ ≤ condition omegaOne master) (D : J → N) (hd : ∀ j, Γ ≤ dense (D j)) :
    ∃ q : J → N, (∀ j, Γ ≤ condition omegaOne (q j)) ∧ (∀ j, Γ ≤ master ⊆ᴮ q j) ∧
      (∀ i j, i ≤ j → Γ ≤ q i ⊆ᴮ q j) ∧ ∀ j, Γ ≤ q j ∈ᴮ D j := by
  classical
  let good (j : J) (s : Set.Iio j → N) (q : N) :=
    Γ ≤ condition omegaOne q ∧ Γ ≤ master ⊆ᴮ q ∧ Γ ≤ q ∈ᴮ D j ∧ ∀ i, Γ ≤ s i ⊆ᴮ q
  let step (j : J) (s : ∀ i : J, i < j → N) := if h : ∃ q, good j (fun i => s i.val i.property) q then h.choose else master
  let q := (wellFounded_lt : WellFounded ((· < ·) : J → J → Prop)).fix step
  have eqn (j : J) : q j = step j (fun i _ => q i) := WellFounded.fix_eq _ _ _
  have ok (j : J) : good j (fun i => q i.val) (q j) := by
    induction j using (wellFounded_lt : WellFounded ((· < ·) : J → J → Prop)).induction with
    | h j ih =>
      let s (i : Set.Iio j) := q i.val
      have existsGood : ∃ v, good j s v := by
        by_cases ne : Nonempty (Set.Iio j)
        · let i := Classical.choice ne
          have mono (t l : Set.Iio j) (h : t ≤ l) : Γ ≤ s t ⊆ᴮ s l := by
            rcases h.lt_or_eq with h | rfl
            · exact (ih l.val l.property).2.2.2 ⟨t.val,h⟩
            · exact subset_self
          have pre := prefix_union_condition hs j s (fun t => (ih t.val t.property).1) mono
          obtain ⟨v,valid,ext,hit⟩ := extends_of_dense (hd j) pre
          exact ⟨v,valid,subset_trans' (ih i.val i.property).2.1 (subset_trans' (family_union_extends s i) ext),
            hit,fun m => subset_trans' (family_union_extends s m) ext⟩
        · obtain ⟨v,valid,ext,hit⟩ := extends_of_dense (hd j) hm
          exact ⟨v,valid,ext,hit,fun i => (ne ⟨i⟩).elim⟩
      rw [eqn j]
      change good j s (if h : ∃ v, good j s v then h.choose else master)
      rw [dif_pos existsGood]
      exact existsGood.choose_spec
  refine ⟨q,fun j => (ok j).1,fun j => (ok j).2.1,?_,fun j => (ok j).2.2.1⟩
  intro i j h
  rcases h.lt_or_eq with h | rfl
  · exact (ok j).2.2.2 ⟨i,h⟩
  · exact subset_self

end Erdos1172CohenIteration.NamedRun
