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

def family {V : Type u} (f : V → N) : N := .mk V f (fun _ => ⊤)

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

end Erdos1172CohenIteration.NamedRun
