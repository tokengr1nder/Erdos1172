/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalOrdinalLeast

@[expose] public section

/-!
# Least ordinal choice with an empty-set sentinel

The candidate name may be empty on only part of the Boolean condition.
Boolean case splitting followed by fullness constructs one actual value
at the original condition, rather than making an external emptiness test.
Uniqueness is unconditional. If every candidate is strictly below the
sentinel, equality with the sentinel detects exactly the empty case.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosOrdinalFallback

open ErdosOrdinalLeast

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

def leastOrTop (C top y : bSet 𝔹) : 𝔹 :=
  leastIn C y ⊔ ((C =ᴮ (∅ : bSet 𝔹)) ⊓ y =ᴮ top)

theorem leastOrTop_ext_value (C top : bSet 𝔹) : B_ext (leastOrTop C top) :=
  B_ext_sup (h₁ := leastIn_ext_value C)
    (h₂ := B_ext_inf B_ext_const B_ext_bv_eq_left)

theorem leastOrTop_ext_set (top y : bSet 𝔹) :
    B_ext (fun C => leastOrTop C top y) :=
  B_ext_sup (h₁ := leastIn_ext_set y)
    (h₂ := B_ext_inf B_ext_bv_eq_left B_ext_const)

theorem leastOrTop_ext_top (C y : bSet 𝔹) :
    B_ext (fun top => leastOrTop C top y) :=
  B_ext_sup (h₁ := B_ext_const)
    (h₂ := B_ext_inf B_ext_const B_ext_bv_eq_right)

theorem leastOrTop_of_least {C top y : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ leastIn C y) : Γ ≤ leastOrTop C top y := H.trans le_sup_left

theorem leastOrTop_of_empty {C top : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ C =ᴮ (∅ : bSet 𝔹)) : Γ ≤ leastOrTop C top top :=
  (le_inf H bv_refl).trans le_sup_right

private theorem choice_cases {C top y : bSet 𝔹} {Γ v : 𝔹}
    (H : Γ ≤ leastOrTop C top y)
    (Hleast : ∀ {Δ : 𝔹}, Δ ≤ Γ → Δ ≤ leastIn C y → Δ ≤ v)
    (Hempty : ∀ {Δ : 𝔹}, Δ ≤ Γ →
      Δ ≤ C =ᴮ (∅ : bSet 𝔹) ⊓ y =ᴮ top → Δ ≤ v) : Γ ≤ v := by
  exact (le_inf le_rfl H).trans
    (bv_or_elim_right (Hleast inf_le_left inf_le_right)
      (Hempty inf_le_left inf_le_right))

private theorem bot_of_least_empty {C y : bSet 𝔹} {Γ : 𝔹}
    (Hy : Γ ≤ leastIn C y) (Hempty : Γ ≤ C =ᴮ (∅ : bSet 𝔹)) : Γ ≤ ⊥ :=
  bot_of_mem_empty (mem_congr bv_refl Hempty (leastIn_mem Hy))

/-- No ordinal, bound, or nonempty assumption is needed for uniqueness. -/
theorem leastOrTop_unique {C top x y : bSet 𝔹} {Γ : 𝔹}
    (Hx : Γ ≤ leastOrTop C top x) (Hy : Γ ≤ leastOrTop C top y) :
    Γ ≤ x =ᴮ y := by
  apply choice_cases Hx
  · intro Δ HΔ Hleastx
    apply choice_cases (HΔ.trans Hy)
    · intro Λ HΛ Hleasty
      exact leastIn_unique (HΛ.trans Hleastx) Hleasty
    · intro Λ HΛ Hemptyy
      exact (bot_of_least_empty (HΛ.trans Hleastx) (Hemptyy.trans inf_le_left)).trans bot_le
  · intro Δ HΔ Hemptyx
    apply choice_cases (HΔ.trans Hy)
    · intro Λ HΛ Hleasty
      exact (bot_of_least_empty Hleasty
        (HΛ.trans (Hemptyx.trans inf_le_left))).trans bot_le
    · intro Λ HΛ Hemptyy
      exact bv_trans (HΛ.trans (Hemptyx.trans inf_le_right))
        (bv_symm (Hemptyy.trans inf_le_right))

theorem leastOrTop_unique_of_eq {C D top x y : bSet 𝔹} {Γ : 𝔹}
    (HCD : Γ ≤ C =ᴮ D) (Hx : Γ ≤ leastOrTop C top x)
    (Hy : Γ ≤ leastOrTop D top y) : Γ ≤ x =ᴮ y :=
  leastOrTop_unique
    (bv_rw'' (ϕ := fun A => leastOrTop A top x) HCD Hx (leastOrTop_ext_set top x)) Hy

/-- An empty candidate set necessarily selects the sentinel. -/
theorem eq_top_of_leastOrTop_empty {C top y : bSet 𝔹} {Γ : 𝔹}
    (Hchoice : Γ ≤ leastOrTop C top y) (Hempty : Γ ≤ C =ᴮ (∅ : bSet 𝔹)) :
    Γ ≤ y =ᴮ top := leastOrTop_unique Hchoice (leastOrTop_of_empty Hempty)

/-- If all candidates are strictly below the sentinel, selecting it forces
the candidate set to be empty. The subset premise is exactly this bound. -/
theorem empty_of_leastOrTop_eq {C top y : bSet 𝔹} {Γ : 𝔹}
    (Hbelow : Γ ≤ C ⊆ᴮ top) (Hchoice : Γ ≤ leastOrTop C top y)
    (Heq : Γ ≤ y =ᴮ top) : Γ ≤ C =ᴮ (∅ : bSet 𝔹) := by
  apply choice_cases Hchoice
  · intro Δ HΔ Hleast
    have Hy : Δ ≤ y ∈ᴮ top := mem_of_mem_subset (HΔ.trans Hbelow) (leastIn_mem Hleast)
    exact (bot_of_mem_self' (mem_congr (HΔ.trans Heq) bv_refl Hy)).trans bot_le
  · intro Δ _ Hempty
    exact Hempty.trans inf_le_left

theorem leastIn_of_leastOrTop_ne {C top y : bSet 𝔹} {Γ : 𝔹}
    (Hchoice : Γ ≤ leastOrTop C top y) (Hne : Γ ≤ (y =ᴮ top)ᶜ) :
    Γ ≤ leastIn C y := by
  apply choice_cases Hchoice
  · intro Δ _ Hleast
    exact Hleast
  · intro Δ HΔ Hempty
    exact (bv_absurd _ (Hempty.trans inf_le_right) (HΔ.trans Hne)).trans bot_le

theorem leastOrTop_mem_bound {κ C top y : bSet 𝔹} {Γ : 𝔹}
    (HC : Γ ≤ C ⊆ᴮ κ) (Htop : Γ ≤ top ∈ᴮ κ)
    (Hchoice : Γ ≤ leastOrTop C top y) : Γ ≤ y ∈ᴮ κ := by
  apply choice_cases Hchoice
  · intro Δ HΔ Hleast
    exact mem_of_mem_subset (HΔ.trans HC) (leastIn_mem Hleast)
  · intro Δ HΔ Hempty
    exact mem_congr (bv_symm (Hempty.trans inf_le_right)) bv_refl (HΔ.trans Htop)

/-- The Boolean existential covers both parts of the emptiness condition.
Neither branch is required to hold at the original condition by itself. -/
theorem leastOrTop_value {κ C top : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ) (HC : Γ ≤ C ⊆ᴮ κ) :
    Γ ≤ ⨆ y : bSet 𝔹, leastOrTop C top y := by
  calc
    Γ = (Γ ⊓ C =ᴮ (∅ : bSet 𝔹)) ⊔ (Γ ⊓ (C =ᴮ (∅ : bSet 𝔹))ᶜ) := by
      rw [← inf_sup_left, sup_compl_eq_top, inf_top_eq]
    _ ≤ ⨆ y : bSet 𝔹, leastOrTop C top y := by
      apply sup_le
      · exact le_iSup_of_le top (leastOrTop_of_empty inf_le_right)
      · obtain ⟨y, Hy⟩ := exists_least_of_nonempty
          (inf_le_left.trans Hκ) (inf_le_left.trans HC) inf_le_right
        exact le_iSup_of_le y (leastOrTop_of_least Hy)

/-- Fullness constructs one actual name satisfying the fallback rule at
the same arbitrary Boolean condition, even for mixed emptiness. -/
theorem exists_leastOrTop {κ C top : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ) (HC : Γ ≤ C ⊆ᴮ κ) :
    ∃ y : bSet 𝔹, Γ ≤ leastOrTop C top y :=
  exists_convert (leastOrTop_value Hκ HC) (leastOrTop_ext_value C top)

theorem exists_bounded_leastOrTop {κ C top : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ) (HC : Γ ≤ C ⊆ᴮ κ) (Htop : Γ ≤ top ∈ᴮ κ) :
    ∃ y : bSet 𝔹, Γ ≤ y ∈ᴮ κ ⊓ leastOrTop C top y := by
  obtain ⟨y, Hy⟩ := exists_leastOrTop (top := top) Hκ HC
  exact ⟨y, le_inf (leastOrTop_mem_bound HC Htop Hy) Hy⟩

end bSet.ErdosOrdinalFallback
