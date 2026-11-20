/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingStageRealNames

@[expose] public section

/-! # Matching target-stage generics over the source times the stage-index collapse -/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
universe u
open Erdos1172PosetCompletion Erdos1172PosetProjection Erdos1172PositiveBoolean Erdos1172Collapse
open bSet bSet.ErdosNameTransport Erdos1172CohenIteration
open scoped Flypitch
namespace Erdos1172LevyCollapse.Matching

variable {J R : Type u} [NontrivialCompleteBooleanAlgebra R]

/-- The outer extension adds a countable enumeration of the ground stages over the source. -/
abbrev JointForcing (R J : Type u) [NontrivialCompleteBooleanAlgebra R] :=
  Completion (Positive R × Condition J)

instance jointNontrivial : NontrivialCompleteBooleanAlgebra (JointForcing R J) where
  toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra
  bot_lt_top := by
    have : Nonempty (Positive R) := ⟨⟨⊤,top_ne_bot⟩⟩
    exact bot_lt_top

def jointSourceHom (J : Type u) : CompleteLatticeHom R (JointForcing R J) :=
  (Erdos1172PosetProjection.completionHom (⟨Prod.fst,fun _ _ h => h.1⟩ : Positive R × Condition J →o Positive R)
    (fun p q h => ⟨(q,p.2),⟨h,le_rfl⟩,rfl⟩)).comp Erdos1172PositiveBoolean.completionHom

def jointCollapseHom (R : Type u) [NontrivialCompleteBooleanAlgebra R] :
    CompleteLatticeHom (Algebra J) (JointForcing R J) :=
  Erdos1172PosetProjection.completionHom (⟨Prod.snd,fun _ _ h => h.2⟩ : Positive R × Condition J →o Condition J)
    (fun p q h => ⟨(p.1,q),⟨le_rfl,h⟩,rfl⟩)

/-- A positive condition in the independent collapse factor reflects equality
of arbitrary Boolean values from the source factor. -/
theorem joint_source_reflects {d : Algebra J} (hd : d ≠ ⊥) {x y : R}
    (he : jointCollapseHom R d ⊓ jointSourceHom J x = jointCollapseHom R d ⊓ jointSourceHom J y) : x = y := by
  obtain ⟨q,hq⟩ := exists_condition_le hd
  apply element_injective
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro p
  have piece (z : R) : condition (p,q) ≤ jointCollapseHom R d ⊓ jointSourceHom J z ↔ p.val ≤ z := by
    exact ⟨fun h => condition_le_iff.mp (h.trans inf_le_right),fun h =>
      le_inf (condition_le_iff.mpr (show q ∈ d.val from condition_le_iff.mp hq)) (condition_le_iff.mpr h)⟩
  exact ⟨fun h => (piece y).mp (((piece x).mpr h).trans_eq he),
    fun h => (piece x).mp (((piece y).mpr h).trans_eq he.symm)⟩

variable [Preorder J] {B C : J → Type u}
  [∀ j, NontrivialCompleteBooleanAlgebra (B j)] [∀ j, NontrivialCompleteBooleanAlgebra (C j)]
  (b : ∀ {i j : J}, i ≤ j → CompleteLatticeHom (B i) (B j))
  (c : ∀ {i j : J}, i ≤ j → CompleteLatticeHom (C i) (C j))

/-- Complete embeddings of all bounded target stages into the actual joint
product. They are coherent and match the reals from bounded source stages in both directions. -/
theorem exists_joint_stage_embeddings_from
    (hb : ∀ {i j} (h : i ≤ j), Function.Injective (b h))
    (hc : ∀ {i j} (h : i ≤ j), Function.Injective (c h))
    (bid : ∀ i (x : B i), b (le_refl i) x = x)
    (cid : ∀ i (x : C i), c (le_refl i) x = x)
    (bcomp : ∀ {i j k} (h : i ≤ j) (h' : j ≤ k) x, b (h.trans h') x = b h' (b h x))
    (ccomp : ∀ {i j k} (h : i ≤ j) (h' : j ≤ k) x, c (h.trans h') x = c h' (c h x))
    (pairing : ∀ i t, CollapsingPair B C i t) (start : StageMatch B C)
    (g : ∀ i, CompleteLatticeHom (B i) R) (hg : ∀ i, Function.Injective (g i))
    (gg : ∀ {i j} (h : i ≤ j) x, g j (b h x) = g i x) :
    ∃ (V : StageWeights B C b c (JointForcing R J)) (k : ∀ i, CompleteLatticeHom (C i) (JointForcing R J)),
      (⊤ : JointForcing R J) ≤ V.weight 0 start ∧ (∀ i, Function.Injective (k i)) ∧
      (∀ {i j} (h : i ≤ j) x, k j (c h x) = k i x) ∧
      ∀ {i} n (s : StageMatch B C) (h : i ≤ s.1) (x : C i),
        V.weight n s ⊓ k i x = V.weight n s ⊓ jointSourceHom J (g s.1 (s.2.symm (c h x))) := by
  classical
  obtain ⟨W,initial⟩ := exists_external_stageWeights_from b c hb hc bid cid bcomp ccomp pairing start
  let V := W.map b c (jointCollapseHom R)
  let src (i : J) := (jointSourceHom J).comp (g i)
  have hs {i j : J} (h : i ≤ j) (x : B i) : src j (b h x) = src i x := congrArg (jointSourceHom J) (gg h x)
  obtain ⟨k,loc,coh⟩ := exists_coherent_target_maps V src hs ccomp
  have init : (⊤ : JointForcing R J) ≤ V.weight 0 start := by
    exact (TopHomClass.map_top (jointCollapseHom R)).ge.trans (OrderHomClass.mono (jointCollapseHom R) initial)
  refine ⟨V,k,init,?_,coh,loc⟩
  intro i x y eq
  have pos : ∃ (n : ℕ) (s : {s : StageMatch B C // i ≤ s.1}), W.weight n s.val ≠ ⊥ := by
    by_contra! h
    exact top_ne_bot (bot_unique ((W.covers i).trans (iSup_le fun n => iSup_le fun s => (h n s).le)))
  obtain ⟨n,s,hn⟩ := pos
  have e := (loc n s.val s.property x).symm.trans ((congrArg (V.weight n s.val ⊓ ·) eq).trans (loc n s.val s.property y))
  exact hc s.property (s.val.2.symm.injective (hg _ (joint_source_reflects hn e)))

theorem exists_joint_stage_embeddings
    (hb : ∀ {i j} (h : i ≤ j), Function.Injective (b h))
    (hc : ∀ {i j} (h : i ≤ j), Function.Injective (c h))
    (bid : ∀ i (x : B i), b (le_refl i) x = x)
    (cid : ∀ i (x : C i), c (le_refl i) x = x)
    (bcomp : ∀ {i j k} (h : i ≤ j) (h' : j ≤ k) x, b (h.trans h') x = b h' (b h x))
    (ccomp : ∀ {i j k} (h : i ≤ j) (h' : j ≤ k) x, c (h.trans h') x = c h' (c h x))
    (pairing : ∀ i t, CollapsingPair B C i t) (start : StageMatch B C)
    (g : ∀ i, CompleteLatticeHom (B i) R) (hg : ∀ i, Function.Injective (g i))
    (gg : ∀ {i j} (h : i ≤ j) x, g j (b h x) = g i x) :
    ∃ k : ∀ i, CompleteLatticeHom (C i) (JointForcing R J),
      (∀ i, Function.Injective (k i)) ∧ (∀ {i j} (h : i ≤ j) x, k j (c h x) = k i x) ∧
      (∀ i (x : bSet (B i)), jointSourceHom J (g i (x ⊆ᴮ omega)) ≤ ⨆ j, ⨆ v : ℕ → C j,
        mapNames ((jointSourceHom J).comp (g i)) x =ᴮ mapNames (k j) (realName v)) ∧
      (∀ i (x : bSet (C i)), k i (x ⊆ᴮ omega) ≤ ⨆ j, ⨆ v : ℕ → B j,
        mapNames (k i) x =ᴮ mapNames ((jointSourceHom J).comp (g j)) (realName v)) := by
  obtain ⟨V,k,_,ki,coh,loc⟩ := exists_joint_stage_embeddings_from b c hb hc bid cid bcomp ccomp pairing start g hg gg
  let src (i : J) := (jointSourceHom J).comp (g i)
  have hs {i j : J} (h : i ≤ j) (x : B i) : src j (b h x) = src i x := congrArg (jointSourceHom J) (gg h x)
  exact ⟨k,ki,coh,bounded_real_names_match V src k hs cid loc⟩
end Erdos1172LevyCollapse.Matching
