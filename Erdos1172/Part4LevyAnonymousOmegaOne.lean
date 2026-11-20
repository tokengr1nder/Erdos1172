/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyAnonymousCheckedSequenceReading
public import Erdos1172.Part4LevyCohenOmegaOne

@[expose] public section

/-! # The internal first uncountable ordinal of the anonymous collapse

Read a surjective enumeration of a checked nonempty predecessor through
the anonymous algebra. On each reading piece, bounded surjectivity descends
along with the function, so the predecessor is countable there. The complete
inclusion sends any injection of checked κ into ω to an ambient injection.
These give the Hartogs characterization in the anonymous algebra itself.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172LevyCohen

open bSet ErdosNameTransport Erdos1172CompleteSubalgebra

private theorem is_surj_ext_graph {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (X Y : bSet B) : B_ext (fun f => is_surj X Y f) :=
  B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const)
    (h₂ := B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_mem_right)))

/-- A surjective supported enumeration covers the ambient condition by a
source truth value witnessing countability of the same checked set. -/
theorem anonymous_countable_of_surjective_sequence (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ) (A : PSet.{u})
    (Hsep : ∀ i j : A.Type, i ≠ j → ¬ PSet.Equiv (A.Func i) (A.Func j))
    {f : bSet (Algebra κ)} {Γ : Algebra κ}
    (Hf : Γ ≤ is_function omega (check A) f) (Hsurj : Γ ≤ is_surj omega (check A) f) :
    Γ ≤ inclusion (anonymousAlgebra κ)
      (injects_into (check A) (omega : bSet (anonymousAlgebra κ))) := by
  let e := inclusion (anonymousAlgebra κ)
  have Hcover := anonymous_checked_sequence_reading_cover κ Hκ Hunc A Hsep Hf
  apply (le_inf le_rfl Hcover).trans
  erw [inf_iSup_eq]
  apply iSup_le
  intro g
  let Δ := Γ ⊓ (e (is_function omega (check A) g) ⊓ (f =ᴮ mapNames e g))
  change Δ ≤ e (injects_into (check A) omega)
  have Hsurjg : Δ ≤ is_surj omega (check A) (mapNames e g) :=
    bv_rw'' (inf_le_right.trans inf_le_right) (inf_le_left.trans Hsurj)
      (is_surj_ext_graph omega (check A))
  have Hmap : e (is_surj omega (check A) g) =
      is_surj omega (check A) (mapNames e g) := by
    rw [map_is_surj]
    simp only [omega, map_check]
  have Hsource : is_function omega (check A) g ⊓ is_surj omega (check A) g ≤
      injects_into (check A) omega :=
    ErdosCHHartogs.injects_into_of_partial_surjection_ordinal Ord_omega subset_self
      (is_func'_of_is_function inf_le_left) inf_le_right
  apply le_trans _ (OrderHomClass.mono e Hsource)
  change Δ ≤ e (is_function omega (check A) g) ⊓ e (is_surj omega (check A) g)
  exact le_inf (inf_le_right.trans inf_le_left) (Hsurjg.trans_eq Hmap.symm)

theorem anonymous_checked_countable_of_ambient (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ) (A : PSet.{u})
    (Hsep : ∀ i j : A.Type, i ≠ j → ¬ PSet.Equiv (A.Func i) (A.Func j))
    (Hcount : (⊤ : Algebra κ) ≤ injects_into (check A) omega) :
    (⊤ : anonymousAlgebra κ) ≤ injects_into (check A) omega := by
  classical
  by_cases h : Nonempty A.Type
  · have Hnonempty : (⊤ : Algebra κ) ≤ exists_mem (check A) := by
      obtain ⟨i⟩ := h
      exact le_iSup_of_le (check (A.Func i)) (check_mem (PSet.func_mem A i))
    have Honto := surjects_onto_of_injects_into' Hcount Hnonempty
    change (⊤ : Algebra κ) ≤ inclusion (anonymousAlgebra κ)
      (injects_into (check A) omega)
    apply Honto.trans
    apply iSup_le
    intro f
    let Δ := is_func' omega (check A) f ⊓ is_surj omega (check A) f
    have Hweak : Δ ≤ is_func' omega (check A) f := inf_le_left
    exact anonymous_countable_of_surjective_sequence κ Hκ Hunc A Hsep
      (function_of_func'_is_function Hweak)
      (function_of_func'_surj_of_surj Hweak inf_le_right)
  · have Hequiv : PSet.Equiv A (∅ : PSet.{u}) := by
      apply PSet.equiv_iff.mpr
      exact ⟨fun i => (h ⟨i⟩).elim, fun j => nomatch j⟩
    have Heq : (⊤ : anonymousAlgebra κ) ≤ check A =ᴮ (∅ : bSet (anonymousAlgebra κ)) := by
      simpa only [check_empty_eq_empty] using
        (check_bv_eq Hequiv : (⊤ : anonymousAlgebra κ) ≤ check A =ᴮ check (∅ : PSet.{u}))
    exact bv_rw' Heq (ϕ := fun z => injects_into z omega)
      (h_congr := B_ext_injects_into_left) (H_new := injects_into_of_subset empty_subset)

theorem anonymous_checked_members_countable (κ : Cardinal.{u}) (Hκ : κ.IsInaccessible) :
    (⊤ : anonymousAlgebra κ) ≤ ⨅ x, _root_.imp (x ∈ᴮ check (PSet.ordinalMk κ.ord))
      (injects_into x (omega : bSet (anonymousAlgebra κ))) := by
  rw [PSet.ordinalMk_eq_def, check_unfold]
  rw [← bounded_forall (h_congr := B_ext_injects_into_left)]
  change (⊤ : anonymousAlgebra κ) ≤ ⨅ i : κ.ord.ToType, _root_.imp ⊤
    (injects_into (check (PSet.ordinalMk i.toOrd.val)) omega)
  apply le_iInf
  intro i
  rw [top_imp]
  exact anonymous_checked_countable_of_ambient κ Hκ.isRegular Hκ.aleph0_lt
    _ (PSet.ordinalMk_inj i.toOrd.val) (checked_predecessor_countable κ i)

theorem anonymous_checked_upper_not_countable (κ : Cardinal.{u}) (Hκ : κ.IsInaccessible) :
    (⊤ : anonymousAlgebra κ) ≤
      (injects_into (check (PSet.ordinalMk κ.ord)) (omega : bSet (anonymousAlgebra κ)))ᶜ := by
  let e := inclusion (anonymousAlgebra κ)
  let c : anonymousAlgebra κ := injects_into (check (PSet.ordinalMk κ.ord)) omega
  have Hord : e c ≤ Ord (mapNames e (omega : bSet (anonymousAlgebra κ))) := by
    change e c ≤ Ord (mapNames e (check PSet.omega))
    rw [map_check]
    exact Ord_omega
  have Hmapped := map_injects_into_of_ordinal e (show c ≤
    injects_into (check (PSet.ordinalMk κ.ord)) omega from le_rfl) Hord
  simp only [omega, map_check] at Hmapped
  have Hbot : e c = ⊥ := bot_unique (bv_absurd _ Hmapped (checked_upper_not_countable κ Hκ))
  have Hzero : c = ⊥ := inclusion_injective _ (Hbot.trans (map_bot e).symm)
  change ⊤ ≤ cᶜ
  rw [Hzero, compl_bot]

theorem anonymous_checked_upper_hartogsProperty (κ : Cardinal.{u}) (Hκ : κ.IsInaccessible) :
    (⊤ : anonymousAlgebra κ) ≤
      ErdosHartogs.hartogsProperty omega (check (PSet.ordinalMk κ.ord)) :=
  le_inf (check_Ord (PSet.Ord_mk κ.ord))
    (le_inf (anonymous_checked_upper_not_countable κ Hκ) (anonymous_checked_members_countable κ Hκ))

theorem anonymous_checked_upper_eq_omegaOne (κ : Cardinal.{u}) (Hκ : κ.IsInaccessible) :
    (⊤ : anonymousAlgebra κ) ≤ check (PSet.ordinalMk κ.ord) =ᴮ ErdosOmegaTwo.omegaOne :=
  ErdosOmegaTwo.omegaOne_property_unique (anonymous_checked_upper_hartogsProperty κ Hκ)

end Erdos1172LevyCohen
