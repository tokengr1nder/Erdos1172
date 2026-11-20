/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalProjection

@[expose] public section

/-! # Witnesses for mixed partial projections on every Boolean subcondition -/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
open Lattice
universe u
namespace bSet.ErdosShioyaInternal
open ErdosRelationGraph
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

theorem projection_function_bounds {D Q F x y : N} {Γ : B} (hf : Γ ≤ is_function D Q F)
    (xy : Γ ≤ edge F x y) : Γ ≤ x ∈ᴮ D ∧ Γ ≤ y ∈ᴮ Q :=
  mem_prod_iff.mp (mem_of_mem_subset (subset_prod_of_is_function hf) xy)

def projectionPullback (D F E : N) : N :=
  comprehend (fun x => ⨆ y : N, edge F x y ⊓ (y ∈ᴮ E)) D

theorem projectionPullback_mem {D F E x : N} {Γ : B} :
    Γ ≤ x ∈ᴮ projectionPullback D F E ↔ Γ ≤ x ∈ᴮ D ∧ ∃ y : N, Γ ≤ edge F x y ∧ Γ ≤ y ∈ᴮ E := by
  have ext : B_ext (fun x : N => ⨆ y : N, edge F x y ⊓ (y ∈ᴮ E)) :=
    B_ext_iSup (h := fun _ => B_ext_inf B_ext_pair_mem_left B_ext_const)
  rw [projectionPullback,mem_comprehend_and ext]
  constructor
  · rintro ⟨hx,h⟩
    obtain ⟨y,hy⟩ := exists_convert h (B_ext_inf B_ext_pair_mem_right B_ext_mem_left)
    exact ⟨hx,y,hy.trans inf_le_left,hy.trans inf_le_right⟩
  · rintro ⟨hx,y,hy,he⟩
    exact ⟨hx,le_iSup_of_le y (le_inf hy he)⟩

theorem projectionSequence_ext_out (F f : N) : B_ext (projectionSequence F f) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_imp (h₁ := B_ext_inf B_ext_const B_ext_mem_right) (h₂ := B_ext_const))))

theorem projectionSequence_apply {Γ : B} {F f g i x y : N} (h : Γ ≤ projectionSequence F f g)
    (hx : Γ ≤ edge f i x) (hy : Γ ≤ edge g i y) : Γ ≤ edge F x y :=
  projection_imp.mp (h.trans (iInf_le _ i) |>.trans (iInf_le _ x) |>.trans (iInf_le _ y)) Γ le_rfl (le_inf hx hy)

theorem projectionDense_iff {P R D : N} {Γ : B} :
    Γ ≤ projectionDense P R D ↔ ∀ {Δ : B}, Δ ≤ Γ → ∀ {p : N}, Δ ≤ p ∈ᴮ P →
      ∃ x : N, Δ ≤ x ∈ᴮ D ∧ Δ ≤ edge R x p := by
  simp only [projectionDense,le_iInf_iff,projection_imp]
  constructor
  · intro h Δ hd p hp
    obtain ⟨x,hx⟩ := exists_convert (h p Δ hd hp) (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    exact ⟨x,hx.trans inf_le_left,hx.trans inf_le_right⟩
  · intro h p Δ hd hp
    obtain ⟨x,hx,hs⟩ := h hd hp
    exact le_iSup_of_le x (le_inf hx hs)

structure ProjectionLaws (Γ : B) (K P R Q S D F : N) : Prop where
  sub : Γ ≤ D ⊆ᴮ P
  func : Γ ≤ is_function D Q F
  dense : ∀ {Δ : B}, Δ ≤ Γ → ∀ {p : N}, Δ ≤ p ∈ᴮ P → ∃ x : N, Δ ≤ x ∈ᴮ D ∧ Δ ≤ edge R x p
  mono : ∀ {Δ : B}, Δ ≤ Γ → ∀ {x y a b : N}, Δ ≤ edge F x a → Δ ≤ edge F y b →
    Δ ≤ edge R x y → Δ ≤ edge S a b
  reaches : ∀ {Δ : B}, Δ ≤ Γ → ∀ {q : N}, Δ ≤ q ∈ᴮ Q → ∃ x a : N, Δ ≤ edge F x a ∧ Δ ≤ edge S a q
  lifts : ∀ {Δ : B}, Δ ≤ Γ → ∀ {x a q : N}, Δ ≤ edge F x a → Δ ≤ q ∈ᴮ Q → Δ ≤ edge S q a →
    ∃ y b : N, Δ ≤ edge F y b ∧ Δ ≤ edge R y x ∧ Δ ≤ edge S b q
  closed : ∀ {Δ : B}, Δ ≤ Γ → ∀ {A f p : N}, Δ ≤ A ∈ᴮ K → Δ ≤ is_function A D f →
    Δ ≤ descendingValue A f R → Δ ≤ glbValue A f P R p → Δ ≤ p ∈ᴮ D
  continuous : ∀ {Δ : B}, Δ ≤ Γ → ∀ {A f p q : N}, Δ ≤ A ∈ᴮ K → Δ ≤ is_function A D f →
    Δ ≤ descendingValue A f R → Δ ≤ glbValue A f P R p → Δ ≤ edge F p q →
    ∃ g : N, Δ ≤ is_function A Q g ∧ Δ ≤ projectionSequence F f g ∧ Δ ≤ glbValue A g Q S q

theorem projectionLaws_iff {Γ : B} {K P R Q S D F : N} :
    Γ ≤ partialProjectionValue K P R Q S D F ↔ ProjectionLaws Γ K P R Q S D F := by
  constructor
  · intro H
    have base := H.trans inf_le_left
    have first := base.trans inf_le_left
    have basic := base.trans inf_le_right
    have dens := basic.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
    have mono := basic.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
    have reach := basic.trans (inf_le_left.trans inf_le_right)
    have lift := basic.trans inf_le_right
    have cls := H.trans (inf_le_right.trans inf_le_left)
    have cont := H.trans (inf_le_right.trans inf_le_right)
    refine ⟨first.trans inf_le_left,first.trans inf_le_right,projectionDense_iff.mp dens,fun h x y z => ?_,?_,?_,?_,?_⟩
    · intro a hx hy hr
      exact projection_imp.mp (mono.trans (iInf_le _ x) |>.trans (iInf_le _ y) |>.trans (iInf_le _ z) |>.trans (iInf_le _ a)) _ h (le_inf (le_inf hx hy) hr)
    · intro Δ h q hq
      obtain ⟨x,hx⟩ := exists_convert (projection_imp.mp (reach.trans (iInf_le _ q)) Δ h hq)
        (B_ext_iSup (h := fun _ => B_ext_inf B_ext_pair_mem_left B_ext_const))
      obtain ⟨a,ha⟩ := exists_convert hx (B_ext_inf B_ext_pair_mem_right B_ext_pair_mem_left)
      exact ⟨x,a,ha.trans inf_le_left,ha.trans inf_le_right⟩
    · intro Δ h x a q hF hq hs
      obtain ⟨y,hy⟩ := exists_convert (projection_imp.mp (lift.trans (iInf_le _ x) |>.trans (iInf_le _ a) |>.trans (iInf_le _ q)) Δ h (le_inf (le_inf hF hq) hs))
        (B_ext_iSup (h := fun _ => B_ext_inf (B_ext_inf B_ext_pair_mem_left B_ext_pair_mem_left) B_ext_const))
      obtain ⟨b,hb⟩ := exists_convert hy (B_ext_inf (B_ext_inf B_ext_pair_mem_right B_ext_const) B_ext_pair_mem_left)
      exact ⟨y,b,hb.trans (inf_le_left.trans inf_le_left),hb.trans (inf_le_left.trans inf_le_right),hb.trans inf_le_right⟩
    · intro Δ h A f p hA hf hd hglb
      exact projection_imp.mp (cls.trans (iInf_le _ A) |>.trans (iInf_le _ f) |>.trans (iInf_le _ p)) Δ h (le_inf (le_inf (le_inf hA hf) hd) hglb)
    · intro Δ h A f p q hA hf hd hglb hF
      obtain ⟨g,hg⟩ := exists_convert (projection_imp.mp (cont.trans (iInf_le _ A) |>.trans (iInf_le _ f) |>.trans (iInf_le _ p) |>.trans (iInf_le _ q)) Δ h (le_inf (le_inf (le_inf (le_inf hA hf) hd) hglb) hF))
        (B_ext_inf (B_ext_inf B_ext_is_function_right (projectionSequence_ext_out F f)) (glbValue_ext_graph A Q S q))
      exact ⟨g,hg.trans (inf_le_left.trans inf_le_left),hg.trans (inf_le_left.trans inf_le_right),hg.trans inf_le_right⟩
  · intro H
    refine le_inf (le_inf (le_inf H.sub H.func) (le_inf (le_inf (le_inf (projectionDense_iff.mpr H.dense) ?_) ?_) ?_))
      (le_inf ?_ ?_)
    · refine le_iInf fun x => le_iInf fun y => le_iInf fun a => le_iInf fun b => projection_imp.mpr ?_
      intro Δ h ha
      exact H.mono h (ha.trans (inf_le_left.trans inf_le_left)) (ha.trans (inf_le_left.trans inf_le_right)) (ha.trans inf_le_right)
    · refine le_iInf fun q => projection_imp.mpr ?_
      intro Δ h hq
      obtain ⟨x,a,hF,hs⟩ := H.reaches h hq
      exact le_iSup_of_le x (le_iSup_of_le a (le_inf hF hs))
    · refine le_iInf fun x => le_iInf fun a => le_iInf fun q => projection_imp.mpr ?_
      intro Δ h ha
      obtain ⟨y,b,hF,hr,hs⟩ := H.lifts h (ha.trans (inf_le_left.trans inf_le_left))
        (ha.trans (inf_le_left.trans inf_le_right)) (ha.trans inf_le_right)
      exact le_iSup_of_le y (le_iSup_of_le b (le_inf (le_inf hF hr) hs))
    · refine le_iInf fun A => le_iInf fun f => le_iInf fun p => projection_imp.mpr ?_
      intro Δ h ha
      rcases le_inf_iff.mp ha with ⟨hz,hg⟩
      exact H.closed h (hz.trans (inf_le_left.trans inf_le_left)) (hz.trans (inf_le_left.trans inf_le_right))
        (hz.trans inf_le_right) hg
    · refine le_iInf fun A => le_iInf fun f => le_iInf fun p => le_iInf fun q => projection_imp.mpr ?_
      intro Δ h ha
      rcases le_inf_iff.mp ha with ⟨ht,hF⟩
      rcases le_inf_iff.mp ht with ⟨hz,hg⟩
      obtain ⟨g,h₁,h₂,h₃⟩ := H.continuous h (hz.trans (inf_le_left.trans inf_le_left))
        (hz.trans (inf_le_left.trans inf_le_right)) (hz.trans inf_le_right) hg hF
      exact le_iSup_of_le g (le_inf (le_inf h₁ h₂) h₃)

end bSet.ErdosShioyaInternal
