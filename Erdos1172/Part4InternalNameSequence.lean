/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4GroundIndexNameBound
public import Erdos1172.Part4InternalInjectionChain

@[expose] public section

/-!
# The internal family of an external countable sequence of mixed names

The displayed names need not be distinct or unmixed. A weighted index
surjection proves internal countability; extensional bounded quantification
transfers their local membership and inclusion laws to all mixed members.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosNameSequence

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

def family (q : ℕ → bSet B) : bSet B :=
  .mk (ULift.{u} ℕ) (fun i => q i.down) (fun _ => ⊤)

theorem term_mem_family (q : ℕ → bSet B) (n : ℕ) {Γ : B} : Γ ≤ q n ∈ᴮ family q := by
  rw [mem_unfold]
  exact le_iSup_of_le ⟨n⟩ (le_inf le_top bv_refl)

theorem family_countable (q : ℕ → bSet B) {Γ : B} : Γ ≤ injects_into (family q) omega := by
  apply ErdosCHHartogs.injects_into_of_larger_than_ordinal Ord_omega
  exact le_top.trans
    (ErdosGroundIndexNameBound.larger_than_of_index_embedding PSet.omega (family q)
      (Function.Embedding.refl _) (fun i j Hij H => Hij (PSet.omega_inj H)))

theorem family_subset {q : ℕ → bSet B} {X : bSet B} {Γ : B}
    (H : ∀ n, Γ ≤ q n ∈ᴮ X) : Γ ≤ family q ⊆ᴮ X := by
  rw [subset_unfold]
  apply le_iInf
  intro i
  rw [← deduction]
  exact inf_le_left.trans (H i.down)

theorem family_inclusionChain {q : ℕ → bSet B} {Γ : B}
    (Hmono : ∀ m n, m ≤ n → Γ ≤ q m ⊆ᴮ q n) :
    Γ ≤ ErdosInjectionChain.inclusionChain (family q) := by
  have Hbounded : Γ ≤ ⨅ f : bSet B, _root_.imp (f ∈ᴮ family q)
      (⨅ g : bSet B, _root_.imp (g ∈ᴮ family q) (f ⊆ᴮ g ⊔ g ⊆ᴮ f)) := by
    rw [← (bounded_forall (v := family q)
      (h_congr := B_ext_iInf (h := fun _ => B_ext_imp
        (h₁ := B_ext_const)
        (h₂ := B_ext_sup (h₁ := B_ext_subset_left) (h₂ := B_ext_subset_right)))))]
    apply le_iInf
    intro i
    rw [← deduction]
    rw [← (bounded_forall (v := family q)
      (h_congr := B_ext_sup (h₁ := B_ext_subset_right) (h₂ := B_ext_subset_left)))]
    apply le_iInf
    intro j
    rw [← deduction]
    rcases le_total i.down j.down with Hij | Hji
    · exact ((inf_le_left.trans inf_le_left).trans (Hmono i.down j.down Hij)).trans le_sup_left
    · exact ((inf_le_left.trans inf_le_left).trans (Hmono j.down i.down Hji)).trans le_sup_right
  apply le_iInf
  intro f
  apply le_iInf
  intro g
  rw [← deduction]
  have Hfirst : Γ ⊓ (f ∈ᴮ family q ⊓ g ∈ᴮ family q) ≤
      ⨅ g : bSet B, _root_.imp (g ∈ᴮ family q) (f ⊆ᴮ g ⊔ g ⊆ᴮ f) :=
    (le_inf (inf_le_left.trans (Hbounded.trans (iInf_le _ f)))
      (inf_le_right.trans inf_le_left)).trans bv_imp_elim
  exact (le_inf (Hfirst.trans (iInf_le _ g)) (inf_le_right.trans inf_le_right)).trans bv_imp_elim

theorem term_subset_union (q : ℕ → bSet B) (n : ℕ) {Γ : B} : Γ ≤ q n ⊆ᴮ bv_union (family q) := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  exact (bv_union_spec_split (family q) x).mpr
    (le_iSup_of_le (q n) (le_inf (term_mem_family q n) inf_le_right))

end bSet.ErdosNameSequence
