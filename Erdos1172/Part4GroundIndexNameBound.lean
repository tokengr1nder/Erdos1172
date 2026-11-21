/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCHHartogs

@[expose] public section

/-!
# Ground cardinal bounds on the index type of an arbitrary name

An external embedding of a name's index type into separated ground labels
gives a concrete weighted partial surjection from the checked label set onto
the name. The source and graph retain exactly the target's coefficients.
Surjectivity is proved for arbitrary mixed target members, not merely for
the displayed children. For ordinal labels, least preimages give an internal
injection. In particular an external bound on all Boolean real codes yields
an internal powerset bound without assuming CH or an internal enumeration.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosGroundIndexNameBound

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- The actual weighted source and evaluation graph, including when the
target index type is empty or its coefficients are not top. -/
theorem exists_weighted_index_surjection (X : PSet.{u}) (Y : bSet 𝔹)
    (e : Y.type ↪ X.Type)
    (Hsep : ∀ i j : X.Type, i ≠ j → ¬ PSet.Equiv (X.Func i) (X.Func j)) :
    ∃ S f : bSet 𝔹, (⊤ : 𝔹) ≤ (S ⊆ᴮ check X ⊓ is_func' S Y f) ⊓ is_surj S Y f := by
  classical
  let S : bSet 𝔹 := ⟨Y.type, fun i => check (X.Func (e i)), Y.bval⟩
  have Hcongr : ∀ i j : S.type, S.func i =ᴮ S.func j ≤ Y.func i =ᴮ Y.func j := by
    intro i j
    by_cases hij : i = j
    · subst j
      exact bv_refl
    · change (check (X.Func (e i)) : bSet 𝔹) =ᴮ check (X.Func (e j)) ≤ _
      rw [check_bv_eq_bot_of_not_equiv (Hsep (e i) (e j) (fun heq => hij (e.injective heq)))]
      exact bot_le
  let f : bSet 𝔹 := functionMk (u := S) (fun i => Y.func i) Hcongr
  have Hpair (i : Y.type) :
      Y.bval i ≤ pair (S.func i) (Y.func i) ∈ᴮ f :=
    functionMk_self (u := S) (F := fun i => Y.func i) (h_congr := Hcongr)
  have Hmem (i : Y.type) : Y.bval i ≤ S.func i ∈ᴮ S := by
    rw [mem_unfold]
    exact le_iSup_of_le i (le_inf le_rfl bv_refl)
  have Hsubset : (⊤ : 𝔹) ≤ S ⊆ᴮ check X := by
    rw [subset_unfold]
    apply le_iInf
    intro i
    rw [← deduction]
    exact check_mem (PSet.func_mem X (e i))
  have Hfunc : (⊤ : 𝔹) ≤ is_func f := functionMk_is_func (u := S) (fun i => Y.func i) Hcongr
  have Htotal : (⊤ : 𝔹) ≤ is_total S Y f := by
    rw [is_total_iff_is_total']
    apply le_iInf
    intro i
    rw [← deduction]
    exact le_iSup_of_le i (le_inf inf_le_right (inf_le_right.trans (Hpair i)))
  have Hsurj : (⊤ : 𝔹) ≤ is_surj S Y f := by
    apply le_iInf
    intro z
    rw [← deduction, mem_unfold, inf_iSup_eq]
    apply iSup_le
    intro i
    apply le_iSup_of_le (S.func i)
    refine le_inf ((inf_le_right.trans inf_le_left).trans (Hmem i)) ?_
    exact bv_rw' (x := z) (y := Y.func i)
      (ϕ := fun w => pair (S.func i) w ∈ᴮ f)
      (inf_le_right.trans inf_le_right) (h_congr := B_ext_pair_mem_right)
      (H_new := (inf_le_right.trans inf_le_left).trans (Hpair i))
  exact ⟨S, f, le_inf (le_inf Hsubset (le_inf Hfunc Htotal)) Hsurj⟩

theorem larger_than_of_index_embedding (X : PSet.{u}) (Y : bSet 𝔹)
    (e : Y.type ↪ X.Type)
    (Hsep : ∀ i j : X.Type, i ≠ j → ¬ PSet.Equiv (X.Func i) (X.Func j)) :
    (⊤ : 𝔹) ≤ larger_than (check X) Y := by
  obtain ⟨S, f, H⟩ := exists_weighted_index_surjection X Y e Hsep
  exact le_iSup_of_le S (le_iSup_of_le f H)

/-- The injection uses internal least preimages in the checked ordinal. -/
theorem injects_checked_ordinal_of_index_embedding (η : Ordinal.{u})
    (Y : bSet 𝔹) (e : Y.type ↪ (PSet.ordinalMk η).Type) :
    (⊤ : 𝔹) ≤ injects_into Y (check (PSet.ordinalMk η)) :=
  ErdosCHHartogs.injects_into_of_larger_than_ordinal
    (check_Ord (PSet.Ord_mk η))
    (larger_than_of_index_embedding (PSet.ordinalMk η) Y e (PSet.ordinalMk_inj η))

/-- Only an external bound on the full index type is supplied. -/
theorem injects_checked_cardinal_of_index_cardinal_le (κ : Cardinal.{u})
    (Y : bSet 𝔹) (Hcard : Cardinal.mk Y.type ≤ κ) :
    (⊤ : 𝔹) ≤ injects_into Y (check (PSet.ordinalMk κ.ord)) := by
  have Hbound : Cardinal.mk Y.type ≤ Cardinal.mk (PSet.ordinalMk κ.ord).Type := by
    simpa only [PSet.ordinalMk_type, Cardinal.mk_ord_toType] using Hcard
  obtain ⟨e⟩ := (Cardinal.le_def Y.type (PSet.ordinalMk κ.ord).Type).mp Hbound
  exact injects_checked_ordinal_of_index_embedding κ.ord Y e

/-- In the powerset representation the complete index type is the type of
Boolean coefficient functions. This includes all mixed subset names. -/
theorem powerset_injects_checked_cardinal_of_index_cardinal_le
    (κ : Cardinal.{u}) (X : bSet 𝔹)
    (Hcard : Cardinal.mk (X.type → 𝔹) ≤ κ) :
    (⊤ : 𝔹) ≤ injects_into (bv_powerset X) (check (PSet.ordinalMk κ.ord)) :=
  injects_checked_cardinal_of_index_cardinal_le κ (bv_powerset X) Hcard

end bSet.ErdosGroundIndexNameBound
