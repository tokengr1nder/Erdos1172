/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalPartitionOrder

@[expose] public section

/-!
Actual internal graphs on omega constructed from numeral-indexed names.
Every graph law includes mixed internal natural names through Boolean-join
distribution; no global disjointness assumption on the values is imposed.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosOmegaSequence

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

theorem numeralValues_congr (v : ℕ → bSet 𝔹)
    (i j : (bSet.omega : bSet 𝔹).type) :
    (bSet.omega : bSet 𝔹).func i =ᴮ bSet.omega.func j ≤ v i.down =ᴮ v j.down := by
  change (of_nat i.down : bSet 𝔹) =ᴮ of_nat j.down ≤ v i.down =ᴮ v j.down
  by_cases h : i.down = j.down
  · rw [h]
    exact bv_refl
  · rw [of_nat_inj' h]
    exact bot_le

/-- An actual internal graph on all of omega, not a graph only on externally
chosen representatives of its members. The values may overlap arbitrarily. -/
def sequenceGraph (v : ℕ → bSet 𝔹) : bSet 𝔹 :=
  functionMk (u := bSet.omega) (fun n => v n.down) (numeralValues_congr v)

theorem mem_sequenceGraph (v : ℕ → bSet 𝔹) (z : bSet 𝔹) :
    z ∈ᴮ sequenceGraph v =
      ⨆ n : (bSet.omega : bSet 𝔹).type, z =ᴮ pair (of_nat n.down) (v n.down) := by
  rw [mem_unfold]
  change (⨆ n : ULift.{u} ℕ, (⊤ : 𝔹) ⊓
    z =ᴮ pair (of_nat n.down) (v n.down)) = _
  simp only [top_inf_eq]
  rfl

theorem sequenceGraph_pair {v : ℕ → bSet 𝔹} {n : ℕ} {Γ : 𝔹} :
    Γ ≤ pair (of_nat n) (v n) ∈ᴮ sequenceGraph v := by
  rw [mem_sequenceGraph]
  exact le_iSup_of_le ⟨n⟩ bv_refl

theorem sequenceGraph_is_func {v : ℕ → bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ is_func (sequenceGraph v) :=
  le_top.trans (functionMk_is_func _ _)

theorem pair_of_nat_mem_iff {v : ℕ → bSet 𝔹} {n : ℕ} {x : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair (of_nat n) x ∈ᴮ sequenceGraph v ↔ Γ ≤ x =ᴮ v n := by
  constructor
  · intro H
    exact eq_of_is_func_of_eq sequenceGraph_is_func bv_refl H sequenceGraph_pair
  · intro H
    exact mem_congr (pair_congr bv_refl (bv_symm H)) bv_refl sequenceGraph_pair

theorem sequenceGraph_is_function {v : ℕ → bSet 𝔹} {S : bSet 𝔹} {Γ : 𝔹}
    (Hv : ∀ n, Γ ≤ v n ∈ᴮ S) : Γ ≤ is_function bSet.omega S (sequenceGraph v) := by
  refine le_inf (le_inf sequenceGraph_is_func ?_) ?_
  · apply le_iInf
    intro x
    rw [← deduction, mem_unfold]
    change Γ ⊓ (⨆ n : ULift.{u} ℕ, (⊤ : 𝔹) ⊓ x =ᴮ of_nat n.down) ≤
      ⨆ y, (y ∈ᴮ S) ⊓ pair x y ∈ᴮ sequenceGraph v
    simp only [top_inf_eq]
    rw [inf_iSup_eq]
    apply iSup_le
    intro n
    apply le_iSup_of_le (v n.down)
    refine le_inf (inf_le_left.trans (Hv n.down)) ?_
    exact mem_congr (pair_congr (bv_symm inf_le_right) bv_refl) bv_refl
      sequenceGraph_pair
  · rw [subset_unfold]
    apply le_iInf
    intro n
    change Γ ≤ (⊤ : 𝔹) ⟹ pair (of_nat n.down) (v n.down) ∈ᴮ prod bSet.omega S
    rw [top_imp]
    exact mem_prod_iff.mpr ⟨of_nat_mem_omega, Hv n.down⟩

theorem of_nat_mem_eq_bot_of_not_lt {m n : ℕ} (h : ¬m < n) :
    (of_nat m : bSet 𝔹) ∈ᴮ of_nat n = ⊥ := by
  apply bot_unique
  by_cases heq : m = n
  · subst m
    exact bot_of_mem_self' le_rfl
  · have hnm : n < m := by omega
    exact bot_of_mem_mem' (of_nat m) (of_nat n) le_rfl (of_nat_mem_of_lt' hnm)

/-- Ordered numeral relations transfer to arbitrary mixed internal inputs
by distributing both graph membership joins under the same context. -/
theorem relation_of_sequenceGraph_pairs {v : ℕ → bSet 𝔹}
    {P : bSet 𝔹 → bSet 𝔹 → 𝔹} {Γ : 𝔹}
    (HPleft : ∀ y, B_ext (fun x => P x y)) (HPright : ∀ x, B_ext (P x))
    (Hnumeral : ∀ m n, m < n → Γ ≤ P (v m) (v n))
    {i j x y : bSet 𝔹} (Hij : Γ ≤ i ∈ᴮ j)
    (Hix : Γ ≤ pair i x ∈ᴮ sequenceGraph v)
    (Hjy : Γ ≤ pair j y ∈ᴮ sequenceGraph v) : Γ ≤ P x y := by
  apply (le_inf (le_refl Γ) (Hix.trans (mem_sequenceGraph v (pair i x)).le)).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro m
  apply (le_inf (le_refl (Γ ⊓ pair i x =ᴮ pair (of_nat m.down) (v m.down)))
    (inf_le_left.trans (Hjy.trans (mem_sequenceGraph v (pair j y)).le))).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro n
  let Δ := (Γ ⊓ pair i x =ᴮ pair (of_nat m.down) (v m.down)) ⊓
    pair j y =ᴮ pair (of_nat n.down) (v n.down)
  have Hm := pair_eq_pair_iff.mp
    (show Δ ≤ pair i x =ᴮ pair (of_nat m.down) (v m.down) from
      inf_le_left.trans inf_le_right)
  have Hn := pair_eq_pair_iff.mp
    (show Δ ≤ pair j y =ᴮ pair (of_nat n.down) (v n.down) from inf_le_right)
  have Hmn : Δ ≤ (of_nat m.down : bSet 𝔹) ∈ᴮ of_nat n.down :=
    mem_congr Hm.1 Hn.1 (inf_le_left.trans (inf_le_left.trans Hij))
  by_cases h : m.down < n.down
  · exact bv_rw' (ϕ := fun z => P z y) Hm.2 (h_congr := HPleft y)
      (H_new := bv_rw' (ϕ := P (v m.down)) Hn.2
        (h_congr := HPright (v m.down))
        (H_new := inf_le_left.trans (inf_le_left.trans (Hnumeral _ _ h))))
  · exact (Hmn.trans (of_nat_mem_eq_bot_of_not_lt h).le).trans bot_le

def pairwiseOn (A f : bSet 𝔹) (P : bSet 𝔹 → bSet 𝔹 → 𝔹) : 𝔹 :=
  ⨅ i, ⨅ j, ⨅ x, ⨅ y,
    _root_.imp ((((i ∈ᴮ A) ⊓ j ∈ᴮ A) ⊓ i ∈ᴮ j) ⊓
      ((pair i x ∈ᴮ f) ⊓ pair j y ∈ᴮ f)) (P x y)

theorem sequenceGraph_pairwise {v : ℕ → bSet 𝔹}
    {P : bSet 𝔹 → bSet 𝔹 → 𝔹} {Γ : 𝔹}
    (HPleft : ∀ y, B_ext (fun x => P x y)) (HPright : ∀ x, B_ext (P x))
    (Hnumeral : ∀ m n, m < n → Γ ≤ P (v m) (v n)) :
    Γ ≤ pairwiseOn bSet.omega (sequenceGraph v) P := by
  apply le_iInf; intro i; apply le_iInf; intro j
  apply le_iInf; intro x; apply le_iInf; intro y
  rw [← deduction]
  exact relation_of_sequenceGraph_pairs HPleft HPright
    (fun m n h => inf_le_left.trans (Hnumeral m n h))
    (inf_le_right.trans (inf_le_left.trans inf_le_right))
    (inf_le_right.trans (inf_le_right.trans inf_le_left))
    (inf_le_right.trans (inf_le_right.trans inf_le_right))

theorem sequenceGraph_increasing {v : ℕ → bSet 𝔹} {Γ : 𝔹}
    (Hinc : ∀ m n, m < n → Γ ≤ v m ∈ᴮ v n) :
    Γ ≤ ErdosPartition.increasingOn bSet.omega (sequenceGraph v) :=
  sequenceGraph_pairwise (fun _ => B_ext_mem_left) (fun _ => B_ext_mem_right) Hinc

theorem sequenceGraph_is_injective {v : ℕ → bSet 𝔹} {S : bSet 𝔹} {Γ : 𝔹}
    (Hv : ∀ n, Γ ≤ v n ∈ᴮ S) (Hinc : ∀ m n, m < n → Γ ≤ v m ∈ᴮ v n) :
    Γ ≤ is_injective_function bSet.omega S (sequenceGraph v) := by
  have Hf := sequenceGraph_is_function Hv
  refine le_inf Hf ?_
  apply le_iInf; intro i; apply le_iInf; intro j
  apply le_iInf; intro x; apply le_iInf; intro y
  rw [← deduction]
  let Δ := Γ ⊓ (((pair i x ∈ᴮ sequenceGraph v) ⊓ pair j y ∈ᴮ sequenceGraph v) ⊓ x =ᴮ y)
  have Hix : Δ ≤ pair i x ∈ᴮ sequenceGraph v :=
    inf_le_right.trans (inf_le_left.trans inf_le_left)
  have Hjy : Δ ≤ pair j y ∈ᴮ sequenceGraph v :=
    inf_le_right.trans (inf_le_left.trans inf_le_right)
  exact ErdosPartition.increasingOn_injective_on Ord_omega
    (inf_le_left.trans (sequenceGraph_increasing Hinc))
    (mem_domain_of_is_function Hix (inf_le_left.trans Hf))
    (mem_domain_of_is_function Hjy (inf_le_left.trans Hf))
    Hix Hjy (inf_le_right.trans inf_le_right)

end bSet.ErdosOmegaSequence
