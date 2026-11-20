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

variable [Nonempty θ.ord.ToType]

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

end Erdos1172Shioya.UltrapowerStage
