/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaCollapseTree

@[expose] public section

/-! # Closed dense domains in a product with the collapse tree -/

set_option autoImplicit false
noncomputable section
universe u

namespace Erdos1172Shioya

variable {κ : Cardinal.{u}} {R Q X : Type u} [PartialOrder R] [PartialOrder Q]

namespace Collapse

/-- The base coordinate is carried identically into the larger product. -/
def productTree (κ : Cardinal.{u}) (R X : Type u) [PartialOrder R] :
    (R × Sequence κ X) ↪o (R × Condition κ X) where
  toFun a := (a.1, a.2.toCondition)
  inj' _ _ h := Prod.ext (congrArg (Prod.fst : R × Condition κ X → R) h)
    (Sequence.toCondition_injective (congrArg Prod.snd h))
  map_rel_iff' := Iff.rfl

theorem product_isGLB_iff {L T : Type u} [PartialOrder T] (f : L → R × T) (p : R × T) :
    IsGLB (Set.range f) p ↔ IsGLB (Set.range (fun i => (f i).1)) p.1 ∧
      IsGLB (Set.range (fun i => (f i).2)) p.2 := by
  constructor
  · intro hp
    have h (i : L) := hp.1 (Set.mem_range_self i)
    constructor
    · refine ⟨Set.forall_mem_range.mpr (fun i => (h i).1), ?_⟩
      intro t ht
      have hl : (t,p.2) ∈ lowerBounds (Set.range f) := Set.forall_mem_range.mpr
        (fun i => ⟨ht (Set.mem_range_self i), (h i).2⟩)
      exact (hp.2 hl).1
    · refine ⟨Set.forall_mem_range.mpr (fun i => (h i).2), ?_⟩
      intro t ht
      have hl : (p.1,t) ∈ lowerBounds (Set.range f) := Set.forall_mem_range.mpr
        (fun i => ⟨(h i).1, ht (Set.mem_range_self i)⟩)
      exact (hp.2 hl).2
  · rintro ⟨h₁,h₂⟩
    refine ⟨Set.forall_mem_range.mpr (fun i => ⟨h₁.1 (Set.mem_range_self i), h₂.1 (Set.mem_range_self i)⟩), ?_⟩
    intro t ht
    exact ⟨h₁.2 (Set.forall_mem_range.mpr (fun i => (ht (Set.mem_range_self i)).1)),
      h₂.2 (Set.forall_mem_range.mpr (fun i => (ht (Set.mem_range_self i)).2))⟩

theorem productTree_isGLB_iff {L : Type u} (f : L → R × Sequence κ X) (p : R × Sequence κ X) :
    IsGLB (Set.range (fun i => productTree κ R X (f i))) (productTree κ R X p) ↔
      IsGLB (Set.range f) p := by
  rw [product_isGLB_iff, product_isGLB_iff]
  exact and_congr_right (fun _ => Sequence.toCondition_isGLB_iff _ _)

theorem productTree_glb_mem_range {L : Type u} (f : L → R × Sequence κ X) (p : R × Condition κ X)
    (hp : IsGLB (Set.range (fun i => productTree κ R X (f i))) p) :
    p ∈ Set.range (productTree κ R X) := by
  have h := ((product_isGLB_iff _ _).mp hp).2
  let g (i : L) : ordinalDomain κ X := ⟨(f i).2.toCondition, (f i).2.length, (f i).2.dom_toCondition⟩
  obtain ⟨s,hs⟩ := Sequence.exists_toCondition ⟨p.2, ordinalDomain_closed g p.2 h⟩
  exact ⟨(p.1,s), Prod.ext rfl hs⟩

theorem productTree_glb_coordinates {L : Type u} (f : L → R × Sequence κ X) (p : R × Condition κ X)
    (hp : IsGLB (Set.range (fun i => productTree κ R X (f i))) p) :
    IsGLB (Set.range (fun i => (f i).1)) p.1 ∧ ∃ s : Sequence κ X,
      s.toCondition = p.2 ∧ IsGLB (Set.range (fun i => (f i).2)) s := by
  obtain ⟨a, rfl⟩ := productTree_glb_mem_range f p hp
  obtain ⟨h₁,h₂⟩ := (product_isGLB_iff f a).mp ((productTree_isGLB_iff f a).mp hp)
  exact ⟨h₁,a.2,rfl,h₂⟩

def productTreeDomainIso (D : Set (R × Sequence κ X)) : D ≃o (productTree κ R X '' D) where
  toEquiv := Equiv.ofBijective (fun a => ⟨productTree κ R X a.val, Set.mem_image_of_mem _ a.property⟩)
    ⟨fun _ _ h => Subtype.ext ((productTree κ R X).injective (congrArg Subtype.val h)), by
      rintro ⟨_, a, ha, rfl⟩
      exact ⟨⟨a,ha⟩,rfl⟩⟩
  map_rel_iff' := Iff.rfl

theorem productTree_decode (D : Set (R × Sequence κ X)) (p : productTree κ R X '' D) :
    productTree κ R X ((productTreeDomainIso D).symm p).val = p.val :=
  congrArg Subtype.val ((productTreeDomainIso D).apply_symm_apply p)

end Collapse

namespace PartialProjection

open Collapse

/-- Extend the closed dense presentation from sequences to all collapse conditions. -/
def fromProductTree [Nonempty X] (π : PartialProjection κ (R × Sequence κ X) Q) (hκ : κ.IsRegular) :
    PartialProjection κ (R × Collapse.Condition κ X) Q where
  dom := productTree κ R X '' π.dom
  dense p := by
    obtain ⟨q,hq,hqp⟩ := ordinalDomain_dense hκ p.2
    obtain ⟨s,hs⟩ := Sequence.exists_toCondition ⟨q,hq⟩
    obtain ⟨z,hz⟩ := π.dense (p.1,s)
    exact ⟨productTreeDomainIso π.dom z, (productTree κ R X).monotone hz |>.trans
      (show productTree κ R X (p.1,s) ≤ p from ⟨le_rfl, (show s.toCondition ≤ p.2 by
        rw [hs]
        exact hqp)⟩)⟩
  proj := ⟨fun p => π.proj ((productTreeDomainIso π.dom).symm p),
    fun _ _ h => π.proj.monotone ((productTreeDomainIso π.dom).symm.monotone h)⟩
  reaches q := by
    obtain ⟨z,hz⟩ := π.reaches q
    refine ⟨productTreeDomainIso π.dom z, ?_⟩
    change π.proj ((productTreeDomainIso π.dom).symm (productTreeDomainIso π.dom z)) ≤ q
    simpa only [OrderIso.symm_apply_apply] using hz
  lifts a q h := by
    let e := productTreeDomainIso π.dom
    obtain ⟨z,hz,hq⟩ := π.lifts (e.symm a) q h
    refine ⟨e z, e.le_symm_apply.mp hz, ?_⟩
    change π.proj (e.symm (e z)) ≤ q
    simpa only [e.symm_apply_apply] using hq
  closed L _ _ hL f hf p hp := by
    let e := productTreeDomainIso π.dom
    let g (i : L) := e.symm (f i)
    have hh : IsGLB (Set.range (fun i => productTree κ R X (g i).val)) p := by
      simpa only [g, e, productTree_decode] using hp
    obtain ⟨t,rfl⟩ := productTree_glb_mem_range (fun i => (g i).val) p hh
    exact Set.mem_image_of_mem _ (π.closed L hL g (e.symm.monotone.comp_antitone hf) t
      ((productTree_isGLB_iff _ _).mp hh))
  continuous L _ _ hL f hf p hp := by
    let e := productTreeDomainIso π.dom
    let g (i : L) := e.symm (f i)
    apply π.continuous L hL g (e.symm.monotone.comp_antitone hf) (e.symm p)
    apply (productTree_isGLB_iff _ _).mp
    simpa only [g, e, productTree_decode] using hp

theorem fromProductTree_dom [Nonempty X] (π : PartialProjection κ (R × Sequence κ X) Q) (hκ : κ.IsRegular) :
    (π.fromProductTree hκ).dom = productTree κ R X '' π.dom := rfl

theorem fromProductTree_apply [Nonempty X] (π : PartialProjection κ (R × Sequence κ X) Q)
    (hκ : κ.IsRegular) (a : π.dom) :
    (π.fromProductTree hκ).proj (productTreeDomainIso π.dom a) = π.proj a := by
  change π.proj ((productTreeDomainIso π.dom).symm ((productTreeDomainIso π.dom) a)) = π.proj a
  rw [OrderIso.symm_apply_apply]

theorem fromProductTree_graph [Nonempty X] (π : PartialProjection κ (R × Sequence κ X) Q)
    (hκ : κ.IsRegular) (p : (π.fromProductTree hκ).dom) :
    ∃ a : π.dom, p.val = (a.val.1,a.val.2.toCondition) ∧ (π.fromProductTree hκ).proj p = π.proj a :=
  ⟨(productTreeDomainIso π.dom).symm p, (productTree_decode π.dom p).symm, rfl⟩

theorem fromProductTree_over_base [Nonempty X] (π : PartialProjection κ (R × Sequence κ X) Q)
    (hκ : κ.IsRegular) (base : Q → R) (h : ∀ a : π.dom, base (π.proj a) = a.val.1)
    (p : (π.fromProductTree hκ).dom) : base ((π.fromProductTree hκ).proj p) = p.val.1 := by
  obtain ⟨a,ha,hq⟩ := π.fromProductTree_graph hκ p
  rw [hq, h a, ha]

end PartialProjection

end Erdos1172Shioya
