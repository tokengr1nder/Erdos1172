/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalShortInfima
public import Erdos1172.Part4ShioyaInternalOrder
public import Erdos1172.Part4InternalOmegaSequence

@[expose] public section

/-! # Computing greatest lower bounds of mixed countable sequences from their numeral values -/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
open Lattice
universe u
namespace bSet.ErdosShioyaInternal
open ErdosOmegaSequence
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

theorem numeralRows_iff {Γ : B} {P F : N} {v : ℕ → N} {test : N → B} (ext : B_ext test)
    (hf : Γ ≤ is_function omega P F) (vals : ∀ n, Γ ≤ edge F (of_nat n) (v n)) :
    Γ ≤ rowForall omega F test ↔ ∀ n, Γ ≤ test (v n) := by
  refine ⟨fun h n => rowForall_iff.mp h _ _ _ le_rfl of_nat_mem_omega (vals n),fun h => rowForall_iff.mpr ?_⟩
  intro i x Δ hd hi hx
  have hi' : Δ ≤ ⨆ n : ULift.{u} ℕ, i =ᴮ of_nat n.down := by
    rw [mem_unfold] at hi
    change Δ ≤ ⨆ n : ULift.{u} ℕ, (⊤ : B) ⊓ (i =ᴮ of_nat n.down) at hi
    simpa only [top_inf_eq] using hi
  apply (le_inf (le_refl Δ) hi').trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro n
  have eq := eq_of_is_function_of_eq (inf_le_left.trans (hd.trans hf)) inf_le_right
    (inf_le_left.trans hx) (inf_le_left.trans (hd.trans (vals n.down)))
  exact bv_rw' eq (h_congr := ext) (H_new := inf_le_left.trans (hd.trans (h n.down)))

theorem sequence_descending {v : ℕ → N} {Γ : B} {R : N} (h : ∀ m n, m < n → Γ ≤ edge R (v n) (v m)) :
    Γ ≤ descendingValue omega (sequenceGraph v) R :=
  sequenceGraph_pairwise (P := fun x y => edge R y x) (fun _ => B_ext_pair_mem_right)
    (fun _ => B_ext_pair_mem_left) h

theorem glb_numeral_iff {P R F p : N} {Γ : B} {v : ℕ → N}
    (hf : Γ ≤ is_function omega P F) (vals : ∀ n, Γ ≤ edge F (of_nat n) (v n)) :
    Γ ≤ glbValue omega F P R p ↔
      (Γ ≤ p ∈ᴮ P) ∧ (∀ n, Γ ≤ edge R p (v n)) ∧ ∀ (Δ : B) (t : N), Δ ≤ Γ → Δ ≤ t ∈ᴮ P →
        (∀ n, Δ ≤ edge R t (v n)) → Δ ≤ edge R t p := by
  have lows {Δ : B} (hd : Δ ≤ Γ) (x : N) :
      Δ ≤ lowerBoundValue omega F R x ↔ ∀ n, Δ ≤ edge R x (v n) :=
    numeralRows_iff (test := fun y => edge R x y) B_ext_pair_mem_right (hd.trans hf) (fun n => hd.trans (vals n))
  constructor
  · intro h
    refine ⟨h.trans (inf_le_left.trans inf_le_left),(lows le_rfl p).mp (h.trans (inf_le_left.trans inf_le_right)),?_⟩
    intro Δ t hd ht hb
    exact (le_inf (hd.trans (h.trans inf_le_right |>.trans (iInf_le _ t))) (le_inf ht ((lows hd t).mpr hb))).trans bv_imp_elim
  · rintro ⟨hp,hl,hg⟩
    refine le_inf (le_inf hp ((lows le_rfl p).mpr hl)) (le_iInf fun t => ?_)
    rw [← deduction]
    exact hg _ t inf_le_left (inf_le_right.trans inf_le_left)
      ((lows inf_le_left t).mp (inf_le_right.trans inf_le_right))

theorem exists_sequence_glb {K P R : N} {Γ : B} (hk : Γ ≤ omega ∈ᴮ K)
    (hc : Γ ≤ shortInfimaValue K P R) (v : ℕ → N) (hv : ∀ n, Γ ≤ v n ∈ᴮ P)
    (desc : ∀ m n, m < n → Γ ≤ edge R (v n) (v m)) :
    ∃ p : N, Γ ≤ glbValue omega (sequenceGraph v) P R p :=
  shortInfimaValue_iff.mp hc omega (sequenceGraph v) Γ le_rfl hk
    (sequenceGraph_is_function hv) (sequence_descending desc)

end bSet.ErdosShioyaInternal
