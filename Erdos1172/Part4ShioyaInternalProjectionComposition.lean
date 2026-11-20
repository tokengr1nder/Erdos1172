/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalProjectionCompositionGraph
public import Erdos1172.Part4ShioyaInternalProjectionDensity

@[expose] public section

/-! # Composition of continuous partial projections in the Boolean-valued extension -/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
open Lattice
universe u
namespace bSet.ErdosShioyaInternal
open ErdosBoundedFunctionValue
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

private theorem middleMeet {Γ : B} {K P R Q S T V D F E G A f p : N}
    (π : ProjectionLaws Γ K P R Q S D F) (σ : ProjectionLaws Γ K Q S T V E G)
    (hA : Γ ≤ A ∈ᴮ K) (hf : Γ ≤ is_function A (projectionPullback D F E) f)
    (hd : Γ ≤ descendingValue A f R) (hm : Γ ≤ glbValue A f P R p) :
    ∃ y g : N, Γ ≤ edge F p y ∧ Γ ≤ y ∈ᴮ E ∧ Γ ≤ is_function A E g ∧
      Γ ≤ projectionSequence F f g ∧ Γ ≤ descendingValue A g S ∧ Γ ≤ glbValue A g Q S y := by
  have fD : Γ ≤ is_function A D f := by
    apply function_recodomain hf
    intro Δ h i x hix
    exact (projectionPullback_mem.mp (projection_function_bounds (h.trans hf) hix).2).1
  have pD := π.closed le_rfl hA fD hd hm
  have py := graphValue_pair_mem π.func pD
  obtain ⟨g,hg,mapped,hgy⟩ := π.continuous le_rfl hA fD hd hm py
  have gE : Γ ≤ is_function A E g := by
    apply function_recodomain hg
    intro Δ h i a hia
    have ix := graphValue_pair_mem (h.trans hf) (projection_function_bounds (h.trans hg) hia).1
    obtain ⟨_,b,hxb,hb⟩ := projectionPullback_mem.mp (projection_function_bounds (h.trans hf) ix).2
    exact mem_congr (eq_of_is_function_of_eq (h.trans π.func) bv_refl hxb
      (projectionSequence_apply (h.trans mapped) ix hia)) bv_refl hb
  have gdesc := projectionSequence_descending π fD hd mapped
  exact ⟨_,g,py,σ.closed le_rfl hA gE gdesc hgy,gE,mapped,gdesc,hgy⟩

private theorem sequenceCompose {Γ : B} {D F E G Q T A f g k : N}
    (hf : Γ ≤ is_function D Q F) (hg : Γ ≤ is_function E T G)
    (fs : Γ ≤ is_function A (projectionPullback D F E) f) (gs : Γ ≤ is_function A E g)
    (one : Γ ≤ projectionSequence F f g) (two : Γ ≤ projectionSequence G g k) :
    Γ ≤ projectionSequence (projectionComposite D F E G T) f k := by
  refine le_iInf fun i => le_iInf fun x => le_iInf fun z => projection_imp.mpr ?_
  intro Δ h rows
  have ix := rows.trans inf_le_left
  have iy := graphValue_pair_mem (h.trans gs) (projection_function_bounds (h.trans fs) ix).1
  exact (projectionComposite_pair (h.trans hf) (h.trans hg)).mpr ⟨_,
    projectionSequence_apply (h.trans one) ix iy,projectionSequence_apply (h.trans two) iy (rows.trans inf_le_right)⟩

theorem partialProjectionValue_comp {Γ : B} {K P R Q S T V D F E G : N}
    (hk : Γ ≤ omega ∈ᴮ K) (hP : Γ ≤ partialOrderValue P R) (hQ : Γ ≤ partialOrderValue Q S)
    (hT : Γ ≤ partialOrderValue T V) (hC : Γ ≤ shortInfimaValue K P R)
    (hπ : Γ ≤ partialProjectionValue K P R Q S D F) (hσ : Γ ≤ partialProjectionValue K Q S T V E G) :
    Γ ≤ partialProjectionValue K P R T V (projectionPullback D F E) (projectionComposite D F E G T) := by
  let π := projectionLaws_iff.mp hπ
  let σ := projectionLaws_iff.mp hσ
  let H := projectionComposite D F E G T
  have denseValue := projection_pullback_dense hk hP hQ hC hπ hσ
  have below {Δ : B} (h : Δ ≤ Γ) {x a b c : N}
      (hx : Δ ≤ edge F x a) (hb : Δ ≤ edge G b c) (ab : Δ ≤ edge S a b) :
      ∃ r d : N, Δ ≤ edge H r d ∧ Δ ≤ edge R r x ∧ Δ ≤ edge V d c := by
    obtain ⟨r,hr,hrx⟩ := projectionDense_iff.mp denseValue h
      (mem_of_mem_subset (h.trans π.sub) (projection_function_bounds (h.trans π.func) hx).1)
    obtain ⟨_,z,hrz,hz⟩ := projectionPullback_mem.mp hr
    have hzd := graphValue_pair_mem (h.trans σ.func) hz
    refine ⟨r,_,(projectionComposite_pair (h.trans π.func) (h.trans σ.func)).mpr ⟨z,hrz,hzd⟩,hrx,?_⟩
    exact σ.mono h hzd hb (internalOrder_trans (h.trans hQ) (π.mono h hrz hx hrx) ab)
  apply projectionLaws_iff.mpr
  refine ⟨subset_trans' (comprehend_subset (ϕ := fun x => ⨆ y : N, edge F x y ⊓ (y ∈ᴮ E)) D) π.sub,
    projectionComposite_function π.func σ.func,projectionDense_iff.mp denseValue,?_,?_,?_,?_,?_⟩
  · intro Δ h x y a b hxa hyb hxy
    obtain ⟨s,hxs,hsa⟩ := (projectionComposite_pair (h.trans π.func) (h.trans σ.func)).mp hxa
    obtain ⟨t,hyt,htb⟩ := (projectionComposite_pair (h.trans π.func) (h.trans σ.func)).mp hyb
    exact σ.mono h hsa htb (π.mono h hxs hyt hxy)
  · intro Δ h t ht
    obtain ⟨b,c,hbc,hct⟩ := σ.reaches h ht
    obtain ⟨x,a,hxa,hab⟩ := π.reaches h (mem_of_mem_subset (h.trans σ.sub) (projection_function_bounds (h.trans σ.func) hbc).1)
    obtain ⟨r,d,hrd,_,hdc⟩ := below h hxa hbc hab
    exact ⟨r,d,hrd,internalOrder_trans (h.trans hT) hdc hct⟩
  · intro Δ h x a q hxa hq hqa
    obtain ⟨y,hxy,hya⟩ := (projectionComposite_pair (h.trans π.func) (h.trans σ.func)).mp hxa
    obtain ⟨b,c,hbc,hby,hcq⟩ := σ.lifts h hya hq hqa
    obtain ⟨s,t,hst,hsx,htb⟩ := π.lifts h hxy
      (mem_of_mem_subset (h.trans σ.sub) (projection_function_bounds (h.trans σ.func) hbc).1) hby
    obtain ⟨r,d,hrd,hrs,hdc⟩ := below h hst hbc htb
    exact ⟨r,d,hrd,internalOrder_trans (h.trans hP) hrs hsx,internalOrder_trans (h.trans hT) hdc hcq⟩
  · intro Δ h A f p hA hf hd hm
    obtain ⟨y,_,hpy,hy,_,_,_,_⟩ := middleMeet (projectionLaws_iff.mp (h.trans hπ))
      (projectionLaws_iff.mp (h.trans hσ)) hA hf hd hm
    exact projectionPullback_mem.mpr ⟨(projection_function_bounds (h.trans π.func) hpy).1,y,hpy,hy⟩
  · intro Δ h A f p q hA hf hd hm hpq
    obtain ⟨y,g,hpy,_,hg,hmap,hdesc,hglb⟩ := middleMeet (projectionLaws_iff.mp (h.trans hπ))
      (projectionLaws_iff.mp (h.trans hσ)) hA hf hd hm
    obtain ⟨b,hpb,hbq⟩ := (projectionComposite_pair (h.trans π.func) (h.trans σ.func)).mp hpq
    have hyq : Δ ≤ edge G y q := bv_rw'' (eq_of_is_function_of_eq (h.trans π.func) bv_refl hpb hpy) hbq B_ext_pair_mem_left
    obtain ⟨k,hkT,hkmap,hkglb⟩ := σ.continuous h hA hg hdesc hglb hyq
    exact ⟨k,hkT,sequenceCompose (h.trans π.func) (h.trans σ.func) hf hg hmap hkmap,hkglb⟩

end bSet.ErdosShioyaInternal
