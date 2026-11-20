/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingTargetMaps
public import Erdos1172.Part4CohenRealReading

@[expose] public section

/-! # Two-sided matching of arbitrary real names from bounded stages -/

set_option autoImplicit false
noncomputable section
universe u
open bSet bSet.ErdosNameTransport Erdos1172CohenIteration Lattice
open scoped Flypitch
namespace Erdos1172LevyCollapse.Matching

variable {J : Type u} [Preorder J] {B C : J → Type u}
  [∀ j, NontrivialCompleteBooleanAlgebra (B j)] [∀ j, NontrivialCompleteBooleanAlgebra (C j)]
  {b : ∀ {i j : J}, i ≤ j → CompleteLatticeHom (B i) (B j)}
  {c : ∀ {i j : J}, i ≤ j → CompleteLatticeHom (C i) (C j)}
  {E : Type u} [NontrivialCompleteBooleanAlgebra E]
  (W : StageWeights B C b c E) (g : ∀ i, CompleteLatticeHom (B i) E)
  (k : ∀ i, CompleteLatticeHom (C i) E)

private theorem names_agree {Γ : E} (a d : ℕ → E) (h : ∀ n, Γ ⊓ a n = Γ ⊓ d n) :
    Γ ≤ realName a =ᴮ realName d := by
  rw [realName_eq_indicator,realName_eq_indicator]
  exact ErdosPowersetPairCoding.indicator_eq_iff.mpr ⟨fun i => (h i.down).le.trans inf_le_right,
    fun i => (h i.down).ge.trans inf_le_right⟩

private theorem covered (i : J) {Γ y : E}
    (h : ∀ n (s : StageMatch B C), i ≤ s.1 → Γ ⊓ W.weight n s ≤ y) : Γ ≤ y := by
  apply (le_inf (le_refl Γ) (le_top.trans (W.covers i))).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro n
  rw [inf_iSup_eq]
  exact iSup_le fun s => h n s.val s.property

private theorem read_real {V : Type u} [NontrivialCompleteBooleanAlgebra V]
    (e : CompleteLatticeHom V E) (x : bSet V) :
    e (x ⊆ᴮ omega) ≤ mapNames e x =ᴮ realName (fun n => e (of_nat n ∈ᴮ x)) := by
  have rep : x ⊆ᴮ omega ≤ x =ᴮ realName (fun n => of_nat n ∈ᴮ x) :=
    eq_membership_indicator_of_subset le_rfl
  simpa only [map_bv_eq,map_realName] using OrderHomClass.mono e rep

/-- All reals from either bounded stage are covered by ground real names on
the opposite side. A single matching piece transports all bits of each real. -/
theorem bounded_real_names_match
    (gg : ∀ {i j} (h : i ≤ j) x, g j (b h x) = g i x)
    (cid : ∀ i (x : C i), c (le_refl i) x = x)
    (localMap : ∀ {i} (n : ℕ) (s : StageMatch B C) (h : i ≤ s.1) (x : C i),
      W.weight n s ⊓ k i x = W.weight n s ⊓ g s.1 (s.2.symm (c h x))) :
    (∀ i (x : bSet (B i)), g i (x ⊆ᴮ omega) ≤ ⨆ j, ⨆ v : ℕ → C j,
      mapNames (g i) x =ᴮ mapNames (k j) (realName v)) ∧
    (∀ i (x : bSet (C i)), k i (x ⊆ᴮ omega) ≤ ⨆ j, ⨆ v : ℕ → B j,
      mapNames (k i) x =ᴮ mapNames (g j) (realName v)) := by
  constructor
  · intro i x
    apply covered W i
    intro n s hi
    let v (l : ℕ) := s.2 (b hi (of_nat l ∈ᴮ x))
    apply le_iSup_of_le s.1
    apply le_iSup_of_le v
    rw [map_realName]
    apply bv_trans (inf_le_left.trans (read_real (g i) x))
    refine inf_le_right.trans (names_agree _ _ ?_)
    intro l
    rw [localMap n s le_rfl (v l),cid]
    change _ = W.weight n s ⊓ g s.1 (s.2.symm (s.2 (b hi (of_nat l ∈ᴮ x))))
    rw [OrderIso.symm_apply_apply,gg]
  · intro i x
    apply covered W i
    intro n s hi
    let v (l : ℕ) := s.2.symm (c hi (of_nat l ∈ᴮ x))
    apply le_iSup_of_le s.1
    apply le_iSup_of_le v
    rw [map_realName]
    exact bv_trans (inf_le_left.trans (read_real (k i) x))
      (inf_le_right.trans (names_agree _ _ (fun l => localMap n s hi (of_nat l ∈ᴮ x))))

end Erdos1172LevyCollapse.Matching
