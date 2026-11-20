/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingStageWeights

@[expose] public section

/-! # Complete Boolean maps for the matched target stages -/

set_option autoImplicit false
noncomputable section
universe u
namespace Erdos1172LevyCollapse.Matching

private theorem le_of_cover {E A : Type u} [CompleteBooleanAlgebra E] (w : A → E)
    (cover : ⊤ ≤ ⨆ a, w a) {x y : E} (pieces : ∀ a, w a ⊓ x ≤ y) : x ≤ y := by
  apply (le_inf (le_top.trans cover) (le_refl x)).trans
  rw [iSup_inf_eq]
  exact iSup_le pieces

private theorem glue_homs {V E A : Type u} [CompleteBooleanAlgebra V] [CompleteBooleanAlgebra E]
    (w : A → E) (f : A → CompleteLatticeHom V E) (cover : ⊤ ≤ ⨆ a, w a)
    (agree : ∀ a d, w a ⊓ w d ≠ ⊥ → ∀ x, f a x = f d x) :
    ∃ k : CompleteLatticeHom V E, ∀ a x, w a ⊓ k x = w a ⊓ f a x := by
  let k (x : V) := ⨆ a, w a ⊓ f a x
  have loc (a : A) (x : V) : w a ⊓ k x = w a ⊓ f a x := by
    refine le_antisymm ?_ (le_inf inf_le_left (le_iSup (fun d => w d ⊓ f d x) a))
    change w a ⊓ (⨆ d, w d ⊓ f d x) ≤ _
    rw [inf_iSup_eq]
    apply iSup_le
    intro d
    by_cases h : w a ⊓ w d = ⊥
    · exact ((le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans_eq h).trans bot_le
    · exact le_inf inf_le_left ((inf_le_right.trans inf_le_right).trans_eq (agree a d h x).symm)
  have mono : Monotone k := fun x y h => iSup_mono fun a => inf_le_inf_left _ (OrderHomClass.mono (f a) h)
  have sup (T : Set V) : k (sSup T) = sSup (k '' T) := by
    refine le_antisymm ?_ ?_
    swap
    · apply sSup_le
      rintro _ ⟨z,hz,rfl⟩
      exact mono (le_sSup hz)
    apply iSup_le
    intro a
    rw [map_sSup,sSup_image',inf_iSup_eq]
    apply iSup_le
    intro z
    exact (le_iSup (fun d => w d ⊓ f d z.val) a).trans (le_sSup ⟨z.val,z.property,rfl⟩)
  have inf (T : Set V) : k (sInf T) = sInf (k '' T) := by
    refine le_antisymm ?_ ?_
    · apply le_sInf
      rintro _ ⟨z,hz,rfl⟩
      exact mono (sInf_le hz)
    apply le_of_cover w cover
    intro a
    apply (le_inf inf_le_left ?_).trans (le_iSup (fun d => w d ⊓ f d (sInf T)) a)
    rw [map_sInf]
    apply le_sInf
    rintro _ ⟨z,hz,rfl⟩
    exact ((inf_le_inf_left (w a) (sInf_le (show k z ∈ k '' T from ⟨z,hz,rfl⟩))).trans_eq (loc a z)).trans inf_le_right
  exact ⟨{ toFun := k, map_sSup' := sup, map_sInf' := inf },loc⟩

variable {J : Type u} [Preorder J] {B C : J → Type u}
  [∀ j, NontrivialCompleteBooleanAlgebra (B j)] [∀ j, NontrivialCompleteBooleanAlgebra (C j)]
  {b : ∀ {i j : J}, i ≤ j → CompleteLatticeHom (B i) (B j)}
  {c : ∀ {i j : J}, i ≤ j → CompleteLatticeHom (C i) (C j)}
  {E : Type u} [CompleteBooleanAlgebra E] (W : StageWeights B C b c E)
  (g : ∀ i, CompleteLatticeHom (B i) E)
  (gg : ∀ {i j} (h : i ≤ j) x, g j (b h x) = g i x)
  (cc : ∀ {i j k} (h : i ≤ j) (h' : j ≤ k) x, c (h.trans h') x = c h' (c h x))

abbrev Site (B C : J → Type u) [∀ j, NontrivialCompleteBooleanAlgebra (B j)]
    [∀ j, NontrivialCompleteBooleanAlgebra (C j)] (i : J) :=
  ℕ × {s : StageMatch B C // i ≤ s.1}

def localMap (i : J) (a : Site B C i) : CompleteLatticeHom (C i) E :=
  (g a.2.val.1).comp ((CompleteLatticeHom.OrderIso.toCompleteLatticeHom a.2.val.2.symm).comp (c a.2.property))

include gg cc in
private theorem localMap_agrees {i : J} (s t : Site B C i)
    (ext : ExtendsMatch B C b c s.2.val t.2.val) (x : C i) :
    localMap (c := c) g i s x = localMap (c := c) g i t x := by
  obtain ⟨h,he⟩ := ext
  let z := s.2.val.2.symm (c s.2.property x)
  have hz : t.2.val.2 (b h z) = c t.2.property x := by
    rw [he,OrderIso.apply_symm_apply,← cc s.2.property h]
  exact (gg h z).symm.trans (congrArg (g _) (t.2.val.2.symm_apply_eq.mpr hz.symm).symm)

private theorem site_cover (i : J) : (⊤ : E) ≤ ⨆ a : Site B C i, W.weight a.1 a.2.val :=
  (W.covers i).trans <| iSup_le fun n => iSup_le fun s => le_iSup (fun a : Site B C i => W.weight a.1 a.2.val) (n,s)

include gg cc in
/-- Each target stage maps completely into the joint outer forcing. Over the
weight of an actual match the map agrees, on the entire bounded algebra, with
the source interpretation of the inverse isomorphism. The resulting maps
commute with every target inclusion. -/
theorem exists_coherent_target_maps :
    ∃ k : ∀ i, CompleteLatticeHom (C i) E,
      (∀ {i} (n : ℕ) (s : StageMatch B C) (h : i ≤ s.1) (x : C i),
        W.weight n s ⊓ k i x = W.weight n s ⊓ g s.1 (s.2.symm (c h x))) ∧
      ∀ {i j} (h : i ≤ j) x, k j (c h x) = k i x := by
  classical
  have exists_i (i : J) := glue_homs (fun a : Site B C i => W.weight a.1 a.2.val)
    (localMap (c := c) g i) (site_cover W i) fun a d hn x => by
      rcases W.compatible a.1 d.1 a.2.val d.2.val hn with h | h | h
      · rcases a with ⟨n,⟨s,hs⟩⟩
        rcases d with ⟨m,⟨t,ht⟩⟩
        change s = t at h
        subst t
        rfl
      · exact localMap_agrees g gg cc a d h x
      · exact (localMap_agrees g gg cc d a h x).symm
  choose k hk using exists_i
  refine ⟨k,fun n s h x => hk _ (n,⟨s,h⟩) x,?_⟩
  intro i j h x
  have same (a : Site B C j) : W.weight a.1 a.2.val ⊓ k j (c h x) =
      W.weight a.1 a.2.val ⊓ k i x := by
    rw [hk j a (c h x),hk i (a.1,⟨a.2.val,h.trans a.2.property⟩) x]
    change _ = W.weight a.1 a.2.val ⊓ g a.2.val.1 (a.2.val.2.symm (c (h.trans a.2.property) x))
    rw [cc h a.2.property]
    rfl
  apply le_antisymm
  · exact le_of_cover _ (site_cover W j) fun a => (same a).le.trans inf_le_right
  · exact le_of_cover _ (site_cover W j) fun a => (same a).ge.trans inf_le_right

end Erdos1172LevyCollapse.Matching
