/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4CohenCountableFusion

@[expose] public section

/-!
# Same-condition reading and fusion of arbitrary Boolean covers

A completed Boolean cover gives an actual stronger condition lying below
one of its members. The canonical-refinement residual argument and fullness
then give one mixed graph extension whose readings cover the unchanged
first-stage context. Countably many such cover rows are fused by the actual
countable inclusion-chain union construction.

The index type of each row may be arbitrary and may vary with the natural
index. No disjointness, supplied successful chain, no-new-sequences principle,
or elementarity assumption is used. The conclusion retains Boolean joins of
readings, not an external selection of one label at the original context.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172CohenIteration

open bSet Erdos1172PosetCompletion

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- A nonzero cone meets some member of an arbitrary complete cover.
The resulting cone is represented by an actual stronger condition. -/
private theorem exists_condition_in_cover {K : bSet B} {I : Type u}
    (p : Conditions K) (c : I → Algebra K) (Hcover : (⨆ i, c i) = ⊤) :
    ∃ r : Conditions K, r ≤ p ∧ ∃ i : I, condition r ≤ c i := by
  have Hcone : condition p = ⨆ i : I, condition p ⊓ c i := by
    erw [← inf_iSup_eq, Hcover, inf_top_eq]
  have Hpositive : ⊥ < ⨆ i : I, condition p ⊓ c i :=
    (bot_lt_iff_ne_bot.mpr (condition_ne_bot p)).trans_le Hcone.le
  obtain ⟨i, Hi⟩ := nonzero_wit Hpositive
  obtain ⟨q, Hq⟩ := exists_condition_le (ne_of_gt Hi)
  have Hqp : q ∈ ((condition p).val : LowerSet (Conditions K)) :=
    condition_le_iff.mp (Hq.trans inf_le_left)
  obtain ⟨r, Hrq, Hrp⟩ := (mem_condition_iff p q).mp Hqp q le_rfl
  exact ⟨r, Hrp, i, (condition_mono Hrq).trans (Hq.trans inf_le_right)⟩

/-- Canonical extensions reading some member of the cover fill the entire
original first-stage context, not merely one positive subcondition. -/
theorem cover_reading_name_extension_cover {K q : bSet B} {Γ : B} {I : Type u}
    (Hq : Γ ≤ q ∈ᴮ ErdosCohen.conditions K)
    (c : I → Algebra K) (Hcover : (⨆ i, c i) = ⊤) :
    Γ ≤ ⨆ r : bSet B, r ∈ᴮ ErdosCohen.conditions K ⊓
      (q ⊆ᴮ r ⊓ ⨆ i : I, reads (c i) r) := by
  classical
  let V : B := ⨆ r : bSet B, r ∈ᴮ ErdosCohen.conditions K ⊓
    (q ⊆ᴮ r ⊓ ⨆ i : I, reads (c i) r)
  change Γ ≤ V
  by_contra Hnot
  have Hpositive : Γ ⊓ Vᶜ ≠ ⊥ := by
    intro Hzero
    apply Hnot
    have H : Γ ≤ (Vᶜ)ᶜ :=
      le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr Hzero.le)
    simpa only [compl_compl] using H
  obtain ⟨p, Hpb, Hpeq⟩ :=
    Erdos1172BooleanNameIteration.exists_canonical_refinement Hpositive
      (inf_le_left.trans Hq)
  obtain ⟨r, Hrp, i, Hi⟩ := exists_condition_in_cover p c Hcover
  have Hsub : r.value ≤ q ⊆ᴮ Erdos1172BooleanNameIteration.name r :=
    subset_trans' (subset_of_eq (Hrp.1.trans Hpeq)) Hrp.2
  have Hread : r.value ≤ ⨆ i : I,
      reads (c i) (Erdos1172BooleanNameIteration.name r) :=
    le_iSup_of_le i (value_le_reads Hi)
  have HrV : r.value ≤ V :=
    le_iSup_of_le (Erdos1172BooleanNameIteration.name r)
      (le_inf (Erdos1172BooleanNameIteration.name_mem r) (le_inf Hsub Hread))
  have HrnotV : r.value ≤ Vᶜ := Hrp.1.trans (Hpb.trans inf_le_right)
  exact r.nonzero (bot_unique ((le_inf HrV HrnotV).trans inf_compl_eq_bot.le))

/-- Fullness supplies an actual mixed extension whose reading join covers
the same condition. No label is chosen globally from that join. -/
theorem exists_cover_reading_extension {K q : bSet B} {Γ : B} {I : Type u}
    (Hq : Γ ≤ ErdosCohen.condition K q)
    (c : I → Algebra K) (Hcover : (⨆ i, c i) = ⊤) :
    ∃ r : bSet B, Γ ≤ ErdosCohen.condition K r ∧ Γ ≤ q ⊆ᴮ r ∧
      Γ ≤ ⨆ i : I, reads (c i) r := by
  obtain ⟨r, Hr⟩ := exists_convert
    (cover_reading_name_extension_cover (ErdosCohen.mem_conditions_iff.mpr Hq) c Hcover)
    (B_ext_inf B_ext_mem_left (B_ext_inf B_ext_subset_right
      (B_ext_iSup (h := fun i => reads_ext (c i)))))
  exact ⟨r, ErdosCohen.mem_conditions_iff.mp (Hr.trans inf_le_left),
    Hr.trans (inf_le_right.trans inf_le_left),
    Hr.trans (inf_le_right.trans inf_le_right)⟩

/-- A whole set-indexed reading cover persists under graph strengthening,
provided the new graph remains a valid condition at the same context. -/
theorem reads_cover_of_extension {K q r : bSet B} {Γ : B} {I : Type u}
    {c : I → Algebra K}
    (Hsub : Γ ≤ q ⊆ᴮ r) (Hr : Γ ≤ r ∈ᴮ ErdosCohen.conditions K)
    (Hread : Γ ≤ ⨆ i : I, reads (c i) q) :
    Γ ≤ ⨆ i : I, reads (c i) r := by
  calc
    Γ ≤ Γ ⊓ (⨆ i : I, reads (c i) q) := le_inf le_rfl Hread
    _ = ⨆ i : I, Γ ⊓ reads (c i) q := inf_iSup_eq _ _
    _ ≤ ⨆ i : I, reads (c i) r :=
      iSup_mono (fun _ => reads_mono_of_subset Hsub Hr)

/-- One actual mixed extension simultaneously reads countably many
arbitrary cover rows, with all conclusions at the original condition. -/
theorem exists_countable_cover_extension {K q : bSet B} {Γ : B}
    {I : ℕ → Type u}
    (HK : Γ ≤ ErdosHartogs.hartogsProperty omega K)
    (Hq : Γ ≤ ErdosCohen.condition K q)
    (c : ∀ n : ℕ, I n → Algebra K)
    (Hcover : ∀ n : ℕ, (⨆ i : I n, c n i) = ⊤) :
    ∃ r : bSet B, Γ ≤ ErdosCohen.condition K r ∧ Γ ≤ q ⊆ᴮ r ∧
      ∀ n : ℕ, Γ ≤ ⨆ i : I n, reads (c n i) r := by
  classical
  let State := {r : bSet B // Γ ≤ ErdosCohen.condition K r}
  have Hextend (n : ℕ) (s : State) :
      ∃ t : State, Γ ≤ s.val ⊆ᴮ t.val ∧
        Γ ≤ ⨆ i : I n, reads (c n i) t.val := by
    obtain ⟨r, Hr, Hsub, Hread⟩ := exists_cover_reading_extension s.property (c n) (Hcover n)
    exact ⟨⟨r, Hr⟩, Hsub, Hread⟩
  choose next hnext using Hextend
  let states : ℕ → State := Nat.rec ⟨q, Hq⟩ next
  let s : ℕ → bSet B := fun n => (states n).val
  have Hstep (n : ℕ) : Γ ≤ s n ⊆ᴮ s (n + 1) ∧
      Γ ≤ ⨆ i : I n, reads (c n i) (s (n + 1)) := hnext n (states n)
  have Hmono : ∀ n m : ℕ, m ≤ n → Γ ≤ s m ⊆ᴮ s n := by
    intro n
    induction n with
    | zero =>
      intro m hm
      have heq : m = 0 := Nat.eq_zero_of_le_zero hm
      subst m
      exact subset_self
    | succ n ih =>
      intro m hm
      rcases Nat.eq_or_lt_of_le hm with heq | hlt
      · subst m
        exact subset_self
      · exact subset_trans' (ih m (by omega)) (Hstep n).1
  let r : bSet B := bv_union (ErdosNameSequence.family s)
  have Hr : Γ ≤ ErdosCohen.condition K r :=
    ErdosCohen.condition_union_of_countable_chain HK
      (ErdosNameSequence.family_subset
        (fun n => ErdosCohen.mem_conditions_iff.mpr (states n).property))
      (ErdosNameSequence.family_inclusionChain (fun m n Hmn => Hmono n m Hmn))
      (ErdosNameSequence.family_countable s)
  refine ⟨r, Hr, ErdosNameSequence.term_subset_union s 0, ?_⟩
  intro n
  exact reads_cover_of_extension (ErdosNameSequence.term_subset_union s (n + 1))
    (ErdosCohen.mem_conditions_iff.mpr Hr) (Hstep n).2

end Erdos1172CohenIteration
