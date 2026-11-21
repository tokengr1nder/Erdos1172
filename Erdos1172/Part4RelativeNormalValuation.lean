/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyAnonymousQuotientDistributivity
public import Erdos1172.Part4SeedQuotientOrder

@[expose] public section

/-! # Complete range of a Boolean valuation over a forcing extension -/

set_option autoImplicit false
noncomputable section
open Set Erdos1172SeedQuotient Erdos1172CompleteSubalgebra
universe u
namespace Erdos1172RelativeValuation
variable {W B C : Type u} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]
variable (e : CompleteLatticeHom B C) (μ : BoundedLatticeHom (W → B) C)
variable (scalar : ∀ b : B, μ (fun _ => b) = e b)

include scalar in
theorem localized (b : B) (a : W → B) : e b ⊓ μ a = μ (fun x => b ⊓ a x) := by
  rw [← scalar b]
  exact (map_inf μ (fun _ => b) a).symm

include scalar in
/-- A finitary valuation respecting ground Boolean scalars commutes with
arbitrary mixing on pairwise disjoint Boolean pieces. -/
theorem value_mix {J : Type u} (w : J → B) (sep : ∀ j k, j ≠ k → w j ⊓ w k = ⊥)
    (A : J → W → B) :
    μ (fun x => ⨆ j, w j ⊓ A j x) = ⨆ j, e (w j) ⊓ μ (A j) := by
  classical
  let X (x : W) := ⨆ j, w j ⊓ A j x
  have eq (j : J) : e (w j) ⊓ μ X = e (w j) ⊓ μ (A j) := by
    rw [localized e μ scalar,localized e μ scalar]
    congr 1
    funext x
    dsimp only [X]
    rw [inf_iSup_eq]
    apply le_antisymm
    · apply iSup_le
      intro k
      by_cases h : j = k
      · subst k
        exact inf_le_right
      · rw [← inf_assoc,sep j k h,bot_inf_eq]
        exact bot_le
    · apply le_iSup_of_le j
      exact le_inf inf_le_left le_rfl
  have small : μ X ≤ e (⨆ j, w j) := by
    rw [← scalar]
    exact OrderHomClass.mono μ (fun x => iSup_le (fun j => inf_le_left.trans (le_iSup w j)))
  calc
    μ X = e (⨆ j, w j) ⊓ μ X := (inf_eq_right.mpr small).symm
    _ = ⨆ j, e (w j) ⊓ μ (A j) := by rw [map_iSup,iSup_inf_eq]; exact iSup_congr eq

section Range
variable {I : Type u} (d : I → C) (dense : denseOver e d)
variable (normal : ∀ F : I → W → B, ∃ X, μ X = ⨆ i, μ (F i))

include scalar dense normal in
/-- Relative density uses the conditions of the quotient together with
arbitrary source Boolean conditions. Mixing on source antichains keeps
one representative per quotient condition. -/
theorem range_iSup {J : Type u} (A : J → W → B) : ∃ X, μ X = ⨆ j, μ (A j) := by
  classical
  let allow (i : I) (j : J) := sSup {b : B | d i ⊓ e b ≤ μ (A j)}
  have below (i : I) (j : J) : d i ⊓ e (allow i j) ≤ μ (A j) := by
    change d i ⊓ e (sSup _) ≤ _
    rw [map_sSup,sSup_image,inf_iSup_eq]
    exact iSup_le fun b => by rw [inf_iSup_eq]; exact iSup_le fun hb => hb
  choose w lew sep cover using fun i => Erdos1172LevyCohen.disjoint_cover_refinement (allow i)
  let F (i : I) (x : W) := ⨆ j, w i j ⊓ A j x
  have mix (i : I) : μ (F i) = ⨆ j, e (w i j) ⊓ μ (A j) := value_mix e μ scalar _ (sep i) A
  have absorbed (i : I) (j : J) : d i ⊓ e (allow i j) ≤ μ (F i) := by
    have leg : allow i j ≤ ⨆ k, w i k := (le_iSup (allow i) j).trans_eq (cover i).symm
    apply (inf_le_inf_left (d i) (OrderHomClass.mono e leg)).trans
    rw [map_iSup,inf_iSup_eq,mix]
    apply iSup_mono
    intro k
    exact le_inf inf_le_right ((inf_le_inf_left _ (OrderHomClass.mono e (lew i k))).trans (below i k))
  obtain ⟨X,hX⟩ := normal F
  refine ⟨X,hX.trans (le_antisymm ?_ ?_)⟩
  · apply iSup_le
    intro i
    rw [mix]
    exact iSup_mono fun _ => inf_le_right
  · apply iSup_le
    intro j
    let v := ⨆ i, μ (F i)
    by_contra hn
    have nz : μ (A j) \ v ≠ ⊥ := fun h => hn (sdiff_eq_bot_iff.mp h)
    obtain ⟨i,b,pos,hi⟩ := dense _ nz
    have ha : b ≤ allow i j := le_sSup (hi.trans sdiff_le)
    have hv : d i ⊓ e b ≤ v :=
      ((inf_le_inf_left _ (OrderHomClass.mono e ha)).trans (absorbed i j)).trans (le_iSup (fun k => μ (F k)) i)
    exact pos (bot_unique ((le_inf hv hi).trans (by simp [v])))

include scalar dense normal in
/-- The complete Boolean subalgebra consists exactly of values of subsets. -/
def completeRange : CompleteSubalgebra C where
  toCompleteSublattice := by
    have supClosed (S : Set C) (hs : S ⊆ Set.range μ) : sSup S ∈ Set.range μ := by
      choose A hA using fun t : S => hs t.prop
      obtain ⟨X,hX⟩ := range_iSup e μ scalar d dense normal A
      refine ⟨X,hX.trans ?_⟩
      simp only [hA,sSup_eq_iSup']
    refine CompleteSublattice.mk' (Set.range μ) supClosed ?_
    intro S hS
    let T := compl '' S
    have ht : T ⊆ Set.range μ := by
      rintro _ ⟨b,hb,rfl⟩
      obtain ⟨A,rfl⟩ := hS hb
      exact ⟨Aᶜ,map_compl' μ A⟩
    obtain ⟨Y,hY⟩ := supClosed T ht
    refine ⟨Yᶜ,?_⟩
    rw [map_compl',hY]
    change (sSup (compl '' S))ᶜ = sInf S
    rw [← compl_sInf',compl_compl]
  compl_mem' := by
    rintro b ⟨X,rfl⟩
    exact ⟨Xᶜ,map_compl' μ X⟩

end Range

open Erdos1172BooleanFactor

private theorem lowerProjection_projected (R : CompleteSubalgebra C) (inside : ∀ b : B, e b ∈ R)
    (c : C) : lowerProjection e (inclusion R (lowerProjection (inclusion R) c)) = lowerProjection e c := by
  apply le_antisymm
  · apply lowerProjection_le
    change lowerProjection (inclusion R) c ≤ (⟨e (lowerProjection e c),inside _⟩ : R)
    exact lowerProjection_le (inclusion R) (le_image_lowerProjection e c)
  · exact lowerProjection_mono e (le_image_lowerProjection (inclusion R) c)

include scalar in
/-- In the source Boolean model, one subset per condition of the residual
forcing suffices for the positive-basis and small-loss cover. The residual
conditions themselves can lie outside the range of the valuation. -/
theorem exists_quotient_basis {I : Type u} (d : I → C) (dense : denseOver e d)
    (normal : ∀ F : I → W → B, ∃ X, μ X = ⨆ i, μ (F i)) :
    ∃ X : I → W → B, ∀ A : W → B, lowerProjection e (μ A) ≤
      ⨆ i, lowerProjection e (μ (X i)) ⊓ (lowerProjection e (μ (X i) ⊓ (μ A)ᶜ))ᶜ := by
  classical
  let R := completeRange e μ scalar d dense normal
  let r (i : I) := lowerProjection (inclusion R) (d i)
  have inside (b : B) : e b ∈ R := ⟨fun _ => b, scalar b⟩
  choose X hX using fun i => (show (r i).val ∈ Set.range μ from (r i).property)
  refine ⟨X,fun A => ?_⟩
  apply ((denseOver_iff e d).mp dense (μ A)).trans
  apply iSup_mono
  intro i
  rw [hX i]
  have first := lowerProjection_projected e R inside (d i)
  have ha : (μ A)ᶜ ∈ R := ⟨Aᶜ,map_compl' μ A⟩
  let a : R := ⟨(μ A)ᶜ,ha⟩
  have second := lowerProjection_projected e R inside (d i ⊓ inclusion R a)
  rw [lowerProjection_inf_image] at second
  change lowerProjection e (d i) ⊓ (lowerProjection e (d i ⊓ (μ A)ᶜ))ᶜ ≤
    lowerProjection e (inclusion R (r i)) ⊓ (lowerProjection e (inclusion R (r i ⊓ a)))ᶜ
  rw [first,second]
  exact le_rfl

end Erdos1172RelativeValuation
