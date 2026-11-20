/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingExternalStages

@[expose] public section

/-! # Ground stage matches with overlapping Boolean weights commute -/

set_option autoImplicit false
noncomputable section
universe u
open Cardinal bSet Lattice Erdos1172Collapse
open scoped Flypitch
namespace Erdos1172LevyCollapse.Matching

variable {J : Type u} [Preorder J] (B C : J → Type u)
  [∀ j, NontrivialCompleteBooleanAlgebra (B j)] [∀ j, NontrivialCompleteBooleanAlgebra (C j)]
  (b : ∀ {i j : J}, i ≤ j → CompleteLatticeHom (B i) (B j))
  (c : ∀ {i j : J}, i ≤ j → CompleteLatticeHom (C i) (C j))
  (D : Type u) [CompleteBooleanAlgebra D]

/-- Weights are indexed by ground stage matches. Matches with a common positive
weight commute on the whole earlier stage. Every stage is covered. -/
structure StageWeights where
  weight : ℕ → StageMatch B C → D
  covers : ∀ i : J, (⊤ : D) ≤ ⨆ n : ℕ, ⨆ s : {s : StageMatch B C // i ≤ s.1}, weight n s.val
  compatible : ∀ n m s t, weight n s ⊓ weight m t ≠ ⊥ →
    s = t ∨ ExtendsMatch B C b c s t ∨ ExtendsMatch B C b c t s

variable {B C D}

omit [Preorder J] in
private theorem compatible_of_ordered {R : StageMatch B C → StageMatch B C → Prop}
    {s t : StageMatch B C} {Γ : Algebra J} (hn : Γ ≠ ⊥)
    (h : Γ ≤ ⨆ v : {v : StageMatch B C × StageMatch B C // R v.1 v.2},
      (check (stageCode B C s) =ᴮ check (stageCode B C v.val.1)) ⊓
      (check (stageCode B C t) =ᴮ check (stageCode B C v.val.2))) : R s t := by
  by_contra bad
  apply hn
  apply bot_unique (h.trans ?_)
  apply iSup_le
  intro v
  by_cases hs : s = v.val.1
  · have ht : t ≠ v.val.2 := fun he => bad (hs ▸ he ▸ v.property)
    exact inf_le_right.trans_eq (check_bv_eq_bot_of_not_equiv fun hh => ht (stageCode_separated B C _ _ hh))
  · exact inf_le_left.trans_eq (check_bv_eq_bot_of_not_equiv fun hh => hs (stageCode_separated B C _ _ hh))

/-- Extract coherent Boolean weights from the actual matching graph forced
by the further collapse. No generic filter is part of the input. -/
theorem exists_external_stageWeights_from
    (hb : ∀ {i j} (h : i ≤ j), Function.Injective (b h))
    (hc : ∀ {i j} (h : i ≤ j), Function.Injective (c h))
    (bid : ∀ i (x : B i), b (le_refl i) x = x)
    (cid : ∀ i (x : C i), c (le_refl i) x = x)
    (bcomp : ∀ {i j k} (h : i ≤ j) (h' : j ≤ k) x, b (h.trans h') x = b h' (b h x))
    (ccomp : ∀ {i j k} (h : i ≤ j) (h' : j ≤ k) x, c (h.trans h') x = c h' (c h x))
    (pairing : ∀ i t, CollapsingPair B C i t) (start : StageMatch B C) :
    ∃ W : StageWeights B C b c (Algebra J), (⊤ : Algebra J) ≤ W.weight 0 start := by
  obtain ⟨f,initial,hf,hrel,cover⟩ := exists_external_matching_sequence_from b c hb hc bid cid bcomp ccomp pairing start
  let w (n : ℕ) (s : StageMatch B C) : Algebra J := pair (of_nat n) (check (stageCode B C s)) ∈ᴮ f
  refine ⟨⟨w,cover,?_⟩,initial⟩
  intro n m s t hne
  have ordered {k l : ℕ} {p q : StageMatch B C} (hlt : k < l) (hpq : w k p ⊓ w l q ≠ ⊥) :
      ExtendsMatch B C b c p q :=
    compatible_of_ordered hpq (hrel (le_top.trans (of_nat_mem_of_lt' hlt)) inf_le_left inf_le_right)
  rcases lt_trichotomy n m with h | rfl | h
  · exact Or.inr (Or.inl (ordered h hne))
  · left
    by_contra hst
    have eq : w n s ⊓ w n t ≤ check (stageCode B C s) =ᴮ check (stageCode B C t) :=
      eq_of_is_func_of_eq (le_top.trans (hf.trans (inf_le_left.trans inf_le_left))) bv_refl inf_le_left inf_le_right
    exact hne (bot_unique (eq.trans_eq (check_bv_eq_bot_of_not_equiv fun he => hst (stageCode_separated B C _ _ he))))
  · exact Or.inr (Or.inr (ordered h (fun he => hne ((inf_comm _ _).trans he))))

theorem hom_inf {V E : Type u} [CompleteBooleanAlgebra V] [CompleteBooleanAlgebra E]
    (k : CompleteLatticeHom V E) (x y : V) : k (x ⊓ y) = k x ⊓ k y := by
  rw [← sInf_pair,map_sInf,Set.image_pair,sInf_pair]

/-- Carry the weights through the embedding of the further collapse into a
joint forcing with the source algebra. -/
def StageWeights.map {E : Type u} [CompleteBooleanAlgebra E] (W : StageWeights B C b c D)
    (k : CompleteLatticeHom D E) : StageWeights B C b c E where
  weight n s := k (W.weight n s)
  covers i := by
    have cov := OrderHomClass.mono k (W.covers i)
    simpa only [map_top,map_iSup] using cov
  compatible n m s t hn := W.compatible n m s t fun h => hn <| by
    rw [← hom_inf,h,map_bot]

end Erdos1172LevyCollapse.Matching
