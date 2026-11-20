/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CountableRankClosure

@[expose] public section

/-!
# Countable rank closure with varying input types

Under CH a countable sequence of locally ranked objects has only
alephOne possibilities below any fixed cut. This also applies to
partial operations with an independently ranked output type.
-/

open Cardinal Ordinal Set Function Order

namespace Erdos1172Part3CountableFamilyRankClosure

open ErdosRadoCHAsym (W2 IsOmegaOneSup)
open Erdos1172Part3NeighborhoodCode (cof_W2 alephZero_lt_cof_W2)
open Erdos1172Part3CountableRankClosure (Local mk_local_le)

variable {A : ℕ → Type}

abbrev LocalSequence (r : ∀ n, A n ↪ W2) (a : W2) := ∀ n, Local (r n) a

theorem mk_localSequence_le (hCH : CH) (r : ∀ n, A n ↪ W2) (a : W2) :
    #(LocalSequence r a) ≤ ℵ_ 1 := by
  let f : LocalSequence r a → (ℕ → Set.Iio a) := fun c n => ⟨r n (c n).val, (c n).property⟩
  have hf : Function.Injective f := by
    intro c d h
    funext n
    exact Subtype.ext ((r n).injective (congrArg Subtype.val (congrFun h n)))
  have hlocal : #(Set.Iio a) ≤ ℵ_ 1 := mk_local_le (Function.Embedding.refl W2) a
  apply (Cardinal.mk_le_of_injective hf).trans
  rw [Cardinal.mk_arrow]
  simp only [Cardinal.lift_id, Cardinal.mk_nat]
  exact (Cardinal.power_le_power_right hlocal).trans_eq hCH.aleph_one_power_aleph_zero

theorem exists_sequenceBound (hCH : CH) (r : ∀ n, A n ↪ W2)
    (op : (∀ n, A n) → W2) (a : W2) :
    ∃ b : W2, ∀ c : LocalSequence r a, op (fun n => (c n).val) < b := by
  have hcard : #(Set.range (fun c : LocalSequence r a => op (fun n => (c n).val))) ≤ ℵ_ 1 :=
    Cardinal.mk_range_le.trans (mk_localSequence_le hCH r a)
  have hsmall := hcard.trans_lt (Cardinal.aleph_lt_aleph.mpr
    (by norm_num : (1 : Ordinal) < 2))
  rw [← cof_W2] at hsmall
  obtain ⟨b, hb⟩ := not_isCofinal_iff.mp (fun hc => hsmall.not_ge (Order.cof_le hc))
  exact ⟨b, fun c => hb _ ⟨c, rfl⟩⟩

noncomputable def sequenceBound (hCH : CH) (r : ∀ n, A n ↪ W2)
    (op : (∀ n, A n) → W2) (a : W2) : W2 :=
  (exists_sequenceBound hCH r op a).choose

theorem sequenceBound_spec (hCH : CH) (r : ∀ n, A n ↪ W2)
    (op : (∀ n, A n) → W2) (a : W2) (c : LocalSequence r a) :
    op (fun n => (c n).val) < sequenceBound hCH r op a :=
  (exists_sequenceBound hCH r op a).choose_spec c

theorem exists_club_countable_map (hCH : CH) (r : ∀ n, A n ↪ W2)
    (op : (∀ n, A n) → W2) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, IsOmegaOneSup a →
      ∀ c : ∀ n, A n, (∀ n, r n (c n) < a) → op c < a := by
  refine ⟨{a | ClubClosure.ClosedUnder (sequenceBound hCH r op) a},
    ClubClosure.isClub_closedUnder _ alephZero_lt_cof_W2, ?_⟩
  intro a hclosed ha c hc
  obtain ⟨b, hba, hb⟩ := ErdosRadoCHAsym.exists_strict_bound_of_countable_of_IsOmegaOneSup ha
    (seed := Set.range (fun n => r n (c n))) (by
      simpa only [Cardinal.mk_nat] using (Cardinal.mk_range_le (f := fun n => r n (c n))))
    (by rintro _ ⟨n, rfl⟩; exact hc n)
  exact (sequenceBound_spec hCH r op b (fun n => ⟨c n, hb _ ⟨n, rfl⟩⟩)).trans (hclosed b hba)

theorem exists_club_partial_countable_map {B : Type} (hCH : CH) (r : ∀ n, A n ↪ W2)
    (σ : B → W2) (op : (∀ n, A n) → Option B) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, IsOmegaOneSup a →
      ∀ c : ∀ n, A n, (∀ n, r n (c n) < a) → ∀ b, op c = some b → σ b < a := by
  obtain ⟨a0, _, _⟩ := ErdosRadoCHAsym.isStationary_isOmegaOneSup_omegaTwo IsClub.univ
  obtain ⟨club, hclub, h⟩ := exists_club_countable_map hCH r
    (fun c => ((op c).map σ).getD a0)
  refine ⟨club, hclub, ?_⟩
  intro a ha hsup c hc b hb
  simpa only [hb, Option.map_some, Option.getD_some] using h a ha hsup c hc

theorem exists_club_binary_map {C D : Type} (hCH : CH) (r : C ↪ W2) (s : D ↪ W2)
    (op : C → D → W2) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, IsOmegaOneSup a →
      ∀ c d, r c < a → s d < a → op c d < a := by
  let Inputs : ℕ → Type | 0 => C | _ + 1 => D
  let ranks : ∀ n, Inputs n ↪ W2 | 0 => r | _ + 1 => s
  obtain ⟨club, hclub, h⟩ := exists_club_countable_map hCH ranks (fun c => op (c 0) (c 1))
  refine ⟨club, hclub, ?_⟩
  intro a ha hsup c d hc hd
  let input : ∀ n, Inputs n | 0 => c | _ + 1 => d
  apply h a ha hsup input
  intro n
  cases n with
  | zero => exact hc
  | succ n => exact hd

end Erdos1172Part3CountableFamilyRankClosure
