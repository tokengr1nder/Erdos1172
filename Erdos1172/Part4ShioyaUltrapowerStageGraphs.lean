/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaUltrapowerProjection

@[expose] public section

/-! # Set-theoretic interpretation of bounded ultrapower point and edge codes

The target carrier is the image of the ground carrier under the elementary
embedding into the transitive bounded hull. Images of binary graphs can be
read at arbitrary bounded target points.
-/

set_option autoImplicit false
noncomputable section
open Filter Erdos1172GroundUltrapower
universe u
namespace Erdos1172Shioya.UltrapowerStage

variable {I V W : Type u} (U : Ultrafilter I) {θ : Cardinal.{u}} (a : I → Set θ.ord.ToType)

def codedHull (f : V → ZFSet.{u}) (p : Point U a V) : BoundedHull U θ a := by
  refine ⟨Germ.map f p.val,?_⟩
  obtain ⟨η,g,hg⟩ := p.property
  exact ⟨η,f ∘ g,congrArg (Germ.map f) hg⟩

variable [CountableInterFilter (U : Filter I)]

def pointCode (f : V → ZFSet.{u}) (p : Point U a V) : ZFSet.{u} :=
  boundedCollapse U θ a (codedHull U a f p)

theorem pointCode_map (f : V → W) (g : W → ZFSet.{u}) (p : Point U a V) :
    pointCode U a g (map U a f p) = pointCode U a (g ∘ f) p := by
  apply congrArg (boundedCollapse U θ a)
  exact Subtype.ext (Germ.map_map g f p.val)

theorem pointCode_injective [Nonempty θ.ord.ToType] {f : V → ZFSet.{u}} (hf : Function.Injective f) :
    Function.Injective (pointCode U a f) := by
  intro p q h
  have he := congrArg Subtype.val (boundedCollapse_injective U θ a h)
  change Germ.map f p.val = Germ.map f q.val at he
  obtain ⟨η,g,hg⟩ := p.property
  obtain ⟨ν,k,hk⟩ := q.property
  apply Subtype.ext
  rw [← hg,← hk] at he ⊢
  exact Germ.coe_eq.mpr ((Germ.coe_eq.mp he).mono fun _ hi => hf hi)

private theorem code_doubleton [Nonempty θ.ord.ToType] (p : Point U a V) (f g : V → ZFSet.{u}) :
    pointCode U a (fun t => ({f t,g t} : ZFSet)) p = ({pointCode U a f p,pointCode U a g p} : ZFSet) := by
  obtain ⟨η,r,hr⟩ := p.property
  let v i := r (boundedFiber θ a η i)
  ext z
  rw [pointCode,mem_boundedCollapse_iff,ZFSet.mem_pair]
  constructor
  · rintro ⟨t,ht,rfl⟩
    obtain ⟨ν,s,hs⟩ := t.property
    let w i := s (boundedFiber θ a ν i)
    change memRel U t.val (Germ.map (fun k => ({f k,g k} : ZFSet.{u})) p.val) at ht
    rw [← hr,← hs] at ht
    have hm : ∀ᶠ i in U, w i ∈ ({f (v i),g (v i)} : ZFSet) := ht
    rcases U.eventually_or.mp (hm.mono fun _ hi => ZFSet.mem_pair.mp hi) with h | h
    · left
      apply congrArg (boundedCollapse U θ a)
      apply Subtype.ext
      change t.val = Germ.map f p.val
      rw [← hr,← hs]
      exact Germ.coe_eq.mpr h
    · right
      apply congrArg (boundedCollapse U θ a)
      apply Subtype.ext
      change t.val = Germ.map g p.val
      rw [← hr,← hs]
      exact Germ.coe_eq.mpr h
  · rintro (rfl | rfl)
    · refine ⟨codedHull U a f p,?_,rfl⟩
      change memRel U (Germ.map f p.val) (Germ.map _ p.val)
      rw [← hr]
      exact Eventually.of_forall fun _ => ZFSet.mem_pair.mpr (Or.inl rfl)
    · refine ⟨codedHull U a g p,?_,rfl⟩
      change memRel U (Germ.map g p.val) (Germ.map _ p.val)
      rw [← hr]
      exact Eventually.of_forall fun _ => ZFSet.mem_pair.mpr (Or.inr rfl)

variable [Nonempty θ.ord.ToType]

theorem pointCode_pair (p : Point U a V) (f g : V → ZFSet.{u}) :
    pointCode U a (fun t => ZFSet.pair (f t) (g t)) p =
      ZFSet.pair (pointCode U a f p) (pointCode U a g p) := by
  have hs : pointCode U a (fun t => ({f t} : ZFSet)) p = ({pointCode U a f p} : ZFSet) := by
    simpa only [ZFSet.pair_eq_singleton] using code_doubleton U a p f f
  unfold ZFSet.pair
  rw [code_doubleton U a p,hs,code_doubleton U a p]

theorem pointCode_diagonal [PartialOrder V] (f : V → ZFSet.{u}) (p : V) :
    pointCode U a f (diagonal U a p) = (boundedGroundEmbedding U θ a (f p)).val := rfl

theorem mem_image_carrier_iff (f : V → ZFSet.{u}) (x : ZFSet.{u}) :
    x ∈ (boundedGroundEmbedding U θ a (ZFSet.range f)).val ↔ ∃ p : Point U a V, pointCode U a f p = x := by
  classical
  rw [boundedGroundEmbedding_val,mem_boundedCollapse_iff]
  constructor
  · rintro ⟨z,hz,rfl⟩
    obtain ⟨η,g,hg⟩ := z.property
    let s i := boundedFiber θ a η i
    change memRel U z.val (Germ.const (ZFSet.range f)) at hz
    rw [← hg] at hz
    have h := hz.mono fun i (hi : g (s i) ∈ ZFSet.range f) => ZFSet.mem_range.mp hi
    obtain ⟨_,v₀,_⟩ := h.exists
    let read (t : Set θ.ord.ToType) := if he : ∃ p, f p = g t then he.choose else v₀
    refine ⟨represent U a η read,congrArg (boundedCollapse U θ a) (Subtype.ext ?_)⟩
    change Germ.ofFun (fun i => f (read (s i))) = z.val
    rw [← hg]
    exact Germ.coe_eq.mpr (h.mono fun i hi => by simpa only [read,dif_pos hi] using hi.choose_spec)
  · rintro ⟨p,rfl⟩
    refine ⟨codedHull U a f p,?_,rfl⟩
    obtain ⟨η,g,hg⟩ := p.property
    change memRel U (Germ.map f p.val) (Germ.const (ZFSet.range f))
    rw [← hg]
    exact Eventually.of_forall fun _ => ZFSet.mem_range.mpr ⟨_,rfl⟩

theorem mem_image_graph_iff (f g : V → ZFSet.{u}) (x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ (boundedGroundEmbedding U θ a (ZFSet.range fun t => ZFSet.pair (f t) (g t))).val ↔
      ∃ p : Point U a V, pointCode U a f p = x ∧ pointCode U a g p = y := by
  rw [mem_image_carrier_iff]
  simp only [pointCode_pair,ZFSet.pair_inj]

theorem mem_image_order_iff [PartialOrder V] (f : V → ZFSet.{u}) (hf : Function.Injective f)
    (p q : Point U a V) :
    ZFSet.pair (pointCode U a f p) (pointCode U a f q) ∈
        (boundedGroundEmbedding U θ a (ZFSet.range fun t : {z : V × V // z.1 ≤ z.2} =>
          ZFSet.pair (f t.val.1) (f t.val.2))).val ↔ p ≤ q := by
  rw [mem_image_graph_iff]
  change _ ↔ Germ.LiftRel (· ≤ ·) p.val q.val
  rw [relation_iff]
  apply exists_congr
  intro z
  constructor
  · rintro ⟨h₁,h₂⟩
    exact ⟨pointCode_injective U a hf ((pointCode_map U a _ f z).trans h₁),
      pointCode_injective U a hf ((pointCode_map U a _ f z).trans h₂)⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨(pointCode_map U a _ f z).symm,(pointCode_map U a _ f z).symm⟩

/-- At every bounded target point, membership in the elementary image of
the original projection graph agrees exactly with the constructed projection. -/
theorem mem_image_projection_iff {κ : Cardinal.{u}} [PartialOrder V] [PartialOrder W]
    (π : PartialProjection κ V W) (f : V → ZFSet.{u}) (g : W → ZFSet.{u})
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hθ : θ.IsRegular) (fine : FineOn U a) (normal : NormalOn U a) (ht : FiberOrderType U κ θ a)
    (hV : ShortInfima κ V) (p : Point U a V) (q : Point U a W) :
    ZFSet.pair (pointCode U a f p) (pointCode U a g q) ∈
        (boundedGroundEmbedding U θ a (ZFSet.range fun t : π.dom => ZFSet.pair (f t.val) (g (π.proj t)))).val ↔
      ∃ hd : p ∈ (projection U a π hθ fine normal ht hV).dom,
        (projection U a π hθ fine normal ht hV).proj ⟨p,hd⟩ = q := by
  rw [mem_image_graph_iff,projection_graph]
  apply exists_congr
  intro z
  constructor
  · rintro ⟨h₁,h₂⟩
    exact ⟨pointCode_injective U a hf ((pointCode_map U a _ f z).trans h₁),
      pointCode_injective U a hg ((pointCode_map U a _ g z).trans h₂)⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨(pointCode_map U a _ f z).symm,(pointCode_map U a _ g z).symm⟩

end Erdos1172Shioya.UltrapowerStage
