/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Flypitch4.BvmExtras
public import Erdos1172.Part4BooleanNameIteration

@[expose] public section

/-!
# A small actual dense presentation of a Boolean-name iteration

A supported surjection from a checked ground set supplies mixed names for
its values. For every positive Boolean value and ground input label we fix
one positive canonical refinement of that mixed value. The range of these
refinements is an actual dense set of iteration conditions.

Surjectivity is used through a Boolean cover, so no mixed preimage is
required to have a single ground representative on the original condition.
The ground indexing set need not be nonempty or have distinct children.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch

universe u

namespace Erdos1172BooleanNameIteration

open bSet

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

theorem checked_surjection_preimages {I : Type u} {a : I → PSet.{u}} {Q f : bSet B}
    (surj : (⊤ : B) ≤ is_surj (check (PSet.mk I a)) Q f) (p : Condition Q) :
    p.value ≤ ⨆ i, pair (check (a i)) (name p) ∈ᴮ f := by
  have pre : p.value ≤ ⨆ x : bSet B, x ∈ᴮ check (PSet.mk I a) ⊓ pair x (name p) ∈ᴮ f := by
    exact (le_inf (le_top.trans (surj.trans (iInf_le _ (name p)))) (name_mem p)).trans Lattice.bv_imp_elim
  rw [← @bounded_exists B _ (check (PSet.mk I a)) (fun x => pair x (name p) ∈ᴮ f)
    (h_congr := B_ext_pair_mem_left)] at pre
  change p.value ≤ ⨆ i : I, (⊤ : B) ⊓ pair (check (a i)) (name p) ∈ᴮ f at pre
  simpa only [top_inf_eq] using pre

/-- A checked supported surjection yields an actual small dense set, not
merely a small family of Boolean generators. -/
theorem exists_dense_presentation_of_checked_surjection
    {A : PSet.{u}} {Q f : bSet B}
    (HF : (⊤ : B) ≤ is_function (check A) Q f)
    (Hsurj : (⊤ : B) ≤ is_surj (check A) Q f) :
    ∃ D : Set (Condition Q),
      Cardinal.mk D ≤ Cardinal.mk B * Cardinal.mk A.Type ∧
      ∀ p : Condition Q, ∃ d ∈ D, d ≤ p := by
  classical
  rcases A with ⟨I, a⟩
  let q : I → bSet B := fun i =>
    function_eval HF (check (a i)) (check_mem (PSet.func_mem (PSet.mk I a) i))
  have Hqmem (i : I) : (⊤ : B) ≤ q i ∈ᴮ Q := function_eval_mem_codomain
  have Hqpair (i : I) : (⊤ : B) ≤ pair (check (a i)) (q i) ∈ᴮ f := function_eval_pair_mem
  have Hex (z : {b : B // b ≠ ⊥} × I) :
      ∃ r : Condition Q, r.value ≤ z.1.val ∧ r.value ≤ q z.2 =ᴮ name r :=
    exists_canonical_refinement z.1.property (le_top.trans (Hqmem z.2))
  let d : {b : B // b ≠ ⊥} × I → Condition Q := fun z => (Hex z).choose
  refine ⟨Set.range d, ?_, ?_⟩
  · have Hembed : Function.Injective (fun z : {b : B // b ≠ ⊥} × I => (z.1.val, z.2)) := by
      intro x y H
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun z : B × I => z.1) H
      · exact congrArg (fun z : B × I => z.2) H
    calc
      Cardinal.mk (Set.range d) ≤ Cardinal.mk ({b : B // b ≠ ⊥} × I) := Cardinal.mk_range_le
      _ ≤ Cardinal.mk (B × I) := Cardinal.mk_le_of_injective Hembed
      _ = Cardinal.mk B * Cardinal.mk I := by
        simp only [Cardinal.mk_prod, Cardinal.lift_id]
  · intro p
    have Hpre := checked_surjection_preimages Hsurj p
    have Hpositive : ∃ i : I, p.value ⊓ pair (check (a i)) (name p) ∈ᴮ f ≠ ⊥ := by
      by_contra Hnone
      have Hbot : (⨆ i : I, p.value ⊓ pair (check (a i)) (name p) ∈ᴮ f) = ⊥ := by
        apply iSup_eq_bot.mpr
        intro i
        by_contra Hi
        exact Hnone ⟨i, Hi⟩
      apply p.nonzero
      calc
        p.value = p.value ⊓ ⨆ i : I, pair (check (a i)) (name p) ∈ᴮ f := (inf_eq_left.mpr Hpre).symm
        _ = ⨆ i : I, p.value ⊓ pair (check (a i)) (name p) ∈ᴮ f := inf_iSup_eq _ _
        _ = ⊥ := Hbot
    obtain ⟨i, Hi⟩ := Hpositive
    let z : {b : B // b ≠ ⊥} × I := (⟨p.value ⊓ pair (check (a i)) (name p) ∈ᴮ f, Hi⟩, i)
    have Hd : (d z).value ≤ p.value ⊓ pair (check (a i)) (name p) ∈ᴮ f := (Hex z).choose_spec.1
    have Heq : (d z).value ≤ q i =ᴮ name (d z) := (Hex z).choose_spec.2
    have Hpq : (d z).value ≤ name p =ᴮ q i :=
      eq_of_is_func_of_eq
        (le_top.trans (HF.trans (inf_le_left.trans inf_le_left))) bv_refl
        (Hd.trans inf_le_right) (le_top.trans (Hqpair i))
    exact ⟨d z, ⟨z, rfl⟩, Hd.trans inf_le_left, subset_of_eq (bv_trans Hpq Heq)⟩

end Erdos1172BooleanNameIteration
