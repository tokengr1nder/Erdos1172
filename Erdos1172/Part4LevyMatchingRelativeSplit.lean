/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingPartitions
public import Erdos1172.Part4LevyAnonymousQuotientDistributivity

@[expose] public section

/-! # Splitting a collapse condition without reducing its projection -/

set_option autoImplicit false
noncomputable section
universe u
open Cardinal Erdos1172PositiveBoolean Erdos1172BooleanFactor
namespace Erdos1172LevyCollapse.Matching

variable {A B X K : Type u} [CompleteBooleanAlgebra A] [CompleteBooleanAlgebra B]
variable (e : CompleteLatticeHom A B)
local notation "π" => lowerProjection e

theorem lowerProjection_iSup {T : Type u} (b : T → B) : π (⨆ t, b t) = ⨆ t, π (b t) := by
  apply le_antisymm ((lowerProjection_le_iff e).mpr (iSup_le fun t =>
    (lowerProjection_le_iff e).mp (le_iSup (fun i => π (b i)) t)))
  exact iSup_le fun t => lowerProjection_mono e (le_iSup b t)

variable (M : CollapseMatrix X B) (hX : ℵ₀ < #X) (reg : (#X).IsRegular)
variable (g : K → Positive A) (small : #K < #X) (dense : ∀ a, ∃ k, g k ≤ a)

def Good (p : B) (a : A) : Prop :=
  a ≤ π p ∧ ∃ v : X → B, (∀ x, v x ≤ p) ∧ (∀ x, π (v x) = a) ∧
    ∀ x y, x ≠ y → v x ⊓ v y = ⊥

include M hX reg small dense in
private theorem good_dense (p : B) (a : Positive A) (ha : a.val ≤ π p) :
    ∃ z : Positive A, z ≤ a ∧ Good (X := X) e p z.val := by
  let c : Positive B := ⟨e a.val ⊓ p,inf_image_lowerProjection_ne_bot e a.property ha⟩
  obtain ⟨v,hv,_,sep⟩ := M.exists_partition hX reg c
  choose f hf using fun x => dense (⟨π (v x).val,lowerProjection_ne_bot e (v x).property⟩ : Positive A)
  obtain ⟨k,hk⟩ := Cardinal.infinite_pigeonhole f hX.le (by rwa [reg.cof_ord])
  let ℓ : X ≃ (f ⁻¹' {k}) := Classical.choice (Cardinal.eq.mp hk.symm)
  have below (x) : (g k).val ≤ π (v (ℓ x).val).val := by
    have h : f (ℓ x).val = k := (ℓ x).property
    have hle : (g (f (ℓ x).val)).val ≤ π (v (ℓ x).val).val := hf (ℓ x).val
    rwa [h] at hle
  obtain ⟨x₀⟩ : Nonempty X := Cardinal.mk_ne_zero_iff.mp (Cardinal.aleph0_pos.trans hX).ne'
  have hka : (g k).val ≤ a.val := (below x₀).trans (lowerProjection_le e
    ((show (v (ℓ x₀).val).val ≤ e a.val ⊓ p from hv _).trans inf_le_left))
  let w (x : X) := (v (ℓ x).val).val ⊓ e (g k).val
  refine ⟨g k,hka,hka.trans ha,w,fun x => inf_le_left.trans
    ((show (v (ℓ x).val).val ≤ e a.val ⊓ p from hv _).trans inf_le_right),?_,?_⟩
  · intro x
    exact (lowerProjection_inf_image e _ _).trans (inf_eq_right.mpr (below x))
  · intro x y hxy
    exact bot_unique ((inf_le_inf (show w x ≤ (v (ℓ x).val).val from inf_le_left)
      (show w y ≤ (v (ℓ y).val).val from inf_le_left)).trans_eq
      (sep _ _ (fun h => hxy (ℓ.injective (Subtype.ext h)))))

include M hX reg small dense in
/-- Every condition splits into |X| incompatible pieces, each with the
same support in the smaller algebra. This is a statement about the actual
lower projection of each piece, including mixed old-stage conditions. -/
theorem exists_full_support_antichain (p : B) :
    ∃ v : X → B, (∀ x, v x ≤ p) ∧ (∀ x, π (v x) = π p) ∧ ∀ x y, x ≠ y → v x ⊓ v y = ⊥ := by
  classical
  let S := {a : A // Good (X := X) e p a}
  have cover : (⨆ a : S, a.val) = π p := by
    apply le_antisymm (iSup_le fun a => a.property.1)
    apply disjoint_compl_right_iff.mp
    apply disjoint_iff.mpr
    by_contra hn
    let a : Positive A := ⟨π p ⊓ (⨆ s : S, s.val)ᶜ,hn⟩
    obtain ⟨b,hba,hb⟩ := good_dense e M hX reg g small dense p a inf_le_left
    have h₁ : b.val ≤ ⨆ s : S, s.val := le_iSup Subtype.val (⟨b.val,hb⟩ : S)
    have h₂ : b.val ≤ (⨆ s : S, s.val)ᶜ := (show b.val ≤ a.val from hba).trans inf_le_right
    exact b.property (bot_unique ((le_inf h₁ h₂).trans inf_compl_eq_bot.le))
  obtain ⟨w,sub,dis,total⟩ := Erdos1172LevyCohen.disjoint_cover_refinement (fun s : S => s.val)
  choose v hv proj sep using fun s : S => s.property.2
  let z (s : S) (x : X) := v s x ⊓ e (w s)
  refine ⟨fun x => ⨆ s, z s x,fun x => iSup_le fun s => inf_le_left.trans (hv s x),?_,?_⟩
  · intro x
    rw [lowerProjection_iSup]
    calc (⨆ s, π (z s x)) = ⨆ s, w s := iSup_congr fun s =>
          (lowerProjection_inf_image e _ _).trans (by rw [proj,inf_eq_right.mpr (sub s)])
         _ = π p := total.trans cover
  · intro x y hxy
    apply bot_unique
    rw [iSup_inf_eq]
    apply iSup_le
    intro a
    rw [inf_iSup_eq]
    apply iSup_le
    intro b
    by_cases hab : a = b
    · subst b
      exact (inf_le_inf (show z a x ≤ v a x from inf_le_left) (show z a y ≤ v a y from inf_le_left)).trans_eq
        (sep a x y hxy)
    · have h : e (w a) ⊓ e (w b) = ⊥ := by rw [← map_inf,dis a b hab,map_bot]
      exact (inf_le_inf (show z a x ≤ e (w a) from inf_le_right)
        (show z b y ≤ e (w b) from inf_le_right)).trans_eq h

end Erdos1172LevyCollapse.Matching
