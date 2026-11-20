/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInverseSystemDomains
public import Erdos1172.Part4ShioyaFreezing
public import Erdos1172.Part4ShioyaGenericString

@[expose] public section

/-! # Ground presentations for the uniformization forcing

Definition 38 of Eskew and Hayut, *Dense ideals*, imposes local lifting
into a restricted inverse limit whenever a point is in the common domain
of all finite projection paths and satisfies the source-point bounds.
The predicate on coding strings and the set of Shioya conditions are
explicit parameters. The resulting type describes ground presentations.
-/

set_option autoImplicit false
noncomputable section
universe u
open Erdos1172PosetCompletion
namespace Erdos1172Shioya.Uniformization

variable {κ θ : Cardinal.{u}}

structure Edge (p q : Condition κ θ) where
  source : q.Poset
  projection : PartialProjection κ q.Poset p.Poset
  point_le : condition source ≤ projection.booleanHom (condition p.point)
  string_le : condition source ≤ extensionValue projection.booleanHom p.name q.name

theorem Edge.refines {p q : Condition κ θ} (E : Edge p q) :
    (q.withPoint E.source).Refines p := ⟨E.projection,E.point_le,E.string_le⟩

def Edge.reindex {p q p' q' : Condition κ θ} (hp : p = p') (hq : q = q')
    (E : Edge p' q') : Edge p q := hp.symm ▸ hq.symm ▸ E

private theorem Edge.reindex_source {p q p' q' : Condition κ θ} (hp : p = p') (hq : q = q')
    (E : Edge p' q') : q.withPoint (E.reindex hp hq).source = q'.withPoint E.source := by
  subst p'
  subst q'
  rfl

structure Diagram (κ θ : Cardinal.{u}) (I : Type u) [Preorder I] where
  stage : I → Condition κ θ
  edge : ∀ {i j : I}, i < j → Edge (stage i) (stage j)

namespace Diagram

variable {I : Type u} [Preorder I] (D : Diagram κ θ I)
abbrev poset (i : I) := (D.stage i).Poset
abbrev projection {i j : I} (h : i < j) := (D.edge h).projection

def requirements : Set (Condition κ θ) :=
  {p | (∃ i, D.stage i = p) ∨
    ∃ i j : I, ∃ h : i < j, (D.stage j).withPoint (D.edge h).source = p}

theorem requirements_subset_iff (G : Set (Condition κ θ)) :
    D.requirements ⊆ G ↔
    (∀ i, D.stage i ∈ G) ∧ (∀ (i j : I) (h : i < j), (D.stage j).withPoint (D.edge h).source ∈ G) := by
  constructor
  · exact fun H => ⟨fun i => H (Or.inl ⟨i,rfl⟩),fun i j h => H (Or.inr ⟨i,j,h,rfl⟩)⟩
  · rintro ⟨hs,he⟩ _ (⟨i,rfl⟩ | ⟨i,j,h,rfl⟩)
    · exact hs i
    · exact he i j h

variable [hκ : Fact (Cardinal.aleph0 < κ)]

abbrev jointDomain (x : Set I) (γ : x) : Set (D.poset γ.val) :=
  InverseSystem.jointDomain D.poset D.projection hκ.out (fun i => (D.stage i).complete) x γ

abbrev lowerThread (x : Set I) (γ : x) :=
  InverseSystem.Thread D.poset D.projection (x ∩ Set.Iio γ.val)

/-- The diagonal projection at the top acts as the identity. The second
conjunct treats all strictly lower intermediate stages. -/
def guard (x : Set I) (γ : x) (q : D.poset γ.val) : Prop :=
  (∀ (i : x) (h : i < γ), q ≤ (D.edge h).source) ∧
  ∀ (i j : x) (hij : i < j) (hj : j < γ), ∀ hd : q ∈ (D.projection hj).dom,
    (D.projection hj).proj ⟨q,hd⟩ ≤ (D.edge hij).source

/-- Each component is the direct projection of the guarded point. The
freezing property of the coding string identifies it with each composite
through an intermediate stage. -/
def projectedThread (coding : ∀ i, (D.stage i).CodesDense)
    {x : Set I} {γ : x} (q : D.poset γ.val) (hq : q ∈ D.jointDomain x γ)
    (hg : D.guard x γ q) : D.lowerThread x γ := by
  let hd (i : (x ∩ Set.Iio γ.val : Set I)) : q ∈ (D.projection i.property.2).dom :=
    InverseSystem.jointDomain_direct D.poset D.projection hκ.out (fun k => (D.stage k).complete)
      (i := ⟨i.val,i.property.1⟩) i.property.2 hq
  refine ⟨fun i => (D.projection i.property.2).proj ⟨q,hd i⟩,?_⟩
  intro i j hij
  let π := D.projection j.property.2
  let σ := D.projection hij
  let τ := D.projection i.property.2
  let υ := π.comp σ hκ.out (D.stage γ.val).complete
  have hj : π.proj ⟨q,hd j⟩ ∈ D.jointDomain x ⟨j.val,j.property.1⟩ :=
    InverseSystem.jointDomain_project D.poset D.projection hκ.out (fun k => (D.stage k).complete)
      j.property.2 hq
  have hi : π.proj ⟨q,hd j⟩ ∈ σ.dom :=
    InverseSystem.jointDomain_direct D.poset D.projection hκ.out (fun k => (D.stage k).complete)
      (i := ⟨i.val,i.property.1⟩) hij hj
  have hpoint : condition q ≤ π.booleanHom (condition (D.edge hij).source) :=
    (π.dom_condition ⟨q,hd j⟩ _).mpr (condition_mono
      (hg.2 ⟨i.val,i.property.1⟩ ⟨j.val,j.property.1⟩ hij j.property.2 (hd j)))
  have he (k : (x ∩ Set.Iio γ.val : Set I)) : condition q ≤ extensionValue
      (D.projection k.property.2).booleanHom (D.stage k.val).name (D.stage γ.val).name :=
    (condition_mono (hg.1 ⟨k.val,k.property.1⟩ k.property.2)).trans (D.edge k.property.2).string_le
  have hυ : condition q ≤ extensionValue υ.booleanHom (D.stage i.val).name (D.stage γ.val).name := by
    rw [show υ.booleanHom = π.booleanHom.comp σ.booleanHom from π.booleanHom_comp σ hκ.out _]
    exact extensionValue_trans σ.booleanHom π.booleanHom _ _ _ hpoint (D.edge hij).string_le (he j)
  refine ⟨hi,?_⟩
  exact (coding i.val).freeze_proj (w := (D.stage γ.val).withPoint q) υ τ hυ (he i)
    q le_rfl ⟨hd j,hi⟩ (hd i)

def localLifts : Prop :=
  ∀ (x : Set I), Cardinal.mk x < κ → ∀ (γ : x), (∀ i : x, i ≤ γ) →
  ∀ q ∈ D.jointDomain x γ, D.guard x γ q →
    ∀ r : D.lowerThread x γ,
      (∀ i, ∃ hd, r.val i ≤ (D.projection i.property.2).proj ⟨q,hd⟩) →
      ∃ q' ≤ q, q' ∈ D.jointDomain x γ ∧
        ∀ i, ∃ hd, (D.projection i.property.2).proj ⟨q',hd⟩ ≤ r.val i

theorem guard_mono {x : Set I} {γ : x} {q' q : D.poset γ.val} (hle : q' ≤ q)
    (hq : q ∈ D.jointDomain x γ) (hg : D.guard x γ q) : D.guard x γ q' := by
  refine ⟨fun i hi => hle.trans (hg.1 i hi),?_⟩
  intro i j hij hj hd
  let π := D.projection hj
  have hqj : q ∈ π.dom := InverseSystem.jointDomain_direct D.poset D.projection hκ.out
    (fun k => (D.stage k).complete) hj hq
  exact (π.proj.monotone (show (⟨q',hd⟩ : π.dom) ≤ ⟨q,hqj⟩ from hle)).trans (hg.2 i j hij hj hqj)

theorem projectedThread_lifts (hl : D.localLifts) (coding : ∀ i, (D.stage i).CodesDense)
    {x : Set I} (hx : Cardinal.mk x < κ) (γ : x) (ht : ∀ i : x, i ≤ γ)
    (q : D.poset γ.val) (hq : q ∈ D.jointDomain x γ) (hg : D.guard x γ q)
    (r : D.lowerThread x γ) (hr : r ≤ D.projectedThread coding q hq hg) :
    ∃ q' ≤ q, ∃ hd : q' ∈ D.jointDomain x γ, ∃ hb : D.guard x γ q',
      D.projectedThread coding q' hd hb ≤ r := by
  obtain ⟨q',hle,hd,hs⟩ := hl x hx γ ht q hq hg r (fun i =>
    ⟨InverseSystem.jointDomain_direct D.poset D.projection hκ.out (fun k => (D.stage k).complete)
      (i := ⟨i.val,i.property.1⟩) i.property.2 hq,hr i⟩)
  exact ⟨q',hle,hd,D.guard_mono hle hq hg,fun i => (hs i).choose_spec⟩

/-- When a stage has at most one predecessor, lifting a thread reduces
to lifting through its sole projection and meeting the joint domain. -/
theorem localLifts_of_unique_predecessor
    (hthin : ∀ (γ i j : I), i < γ → j < γ → i = j) : D.localLifts := by
  intro x hx γ _ q hq _ r hr
  classical
  by_cases h : Nonempty (x ∩ Set.Iio γ.val : Set I)
  · let i := h.some
    let π := D.projection i.property.2
    obtain ⟨hd,hrd⟩ := hr i
    obtain ⟨t,htq,htr⟩ := π.lifts ⟨q,hd⟩ (r.val i) hrd
    obtain ⟨z,hzt,hz⟩ := InverseSystem.jointDomain_dense D.poset D.projection hκ.out
      (fun n => (D.stage n).complete) x hx γ t.val
    refine ⟨z,hzt.trans htq,hz,?_⟩
    intro j
    have hji : j = i := Subtype.ext (hthin γ.val j.val i.val j.property.2 i.property.2)
    subst j
    have hm : z ∈ π.dom := InverseSystem.jointDomain_direct D.poset D.projection hκ.out
      (fun n => (D.stage n).complete) (i := ⟨i.val,i.property.1⟩) i.property.2 hz
    exact ⟨hm,(π.proj.monotone (show (⟨z,hm⟩ : π.dom) ≤ t from hzt)).trans htr⟩
  · exact ⟨q,le_rfl,hq,fun i => (h ⟨i⟩).elim⟩

def Valid (G : Set (Condition κ θ)) (Coding : Condition κ θ → Prop) : Prop :=
  (∀ i, (∀ q : (D.stage i).Poset, q ≤ (D.stage i).point) ∧ Coding (D.stage i)) ∧
    D.requirements ⊆ G ∧ D.localLifts

end Diagram

structure Presentation (κ θ : Cardinal.{u}) where
  last : θ.ord.ToType
  diagram : Diagram κ θ (Set.Iic last)

namespace Presentation

def restrict {a b : θ.ord.ToType} (D : Diagram κ θ (Set.Iic b)) (h : a ≤ b) :
    Diagram κ θ (Set.Iic a) where
  stage i := D.stage ⟨i.val,i.property.trans h⟩
  edge {_ _} hij := D.edge hij

def EndExtends (v u : Presentation κ θ) : Prop :=
  ∃ h : u.last ≤ v.last, restrict v.diagram h = u.diagram

instance : Preorder (Presentation κ θ) where
  le := EndExtends
  le_refl u := ⟨le_rfl,rfl⟩
  le_trans u v w huv hvw := by
    obtain ⟨h₁,e₁⟩ := huv
    obtain ⟨h₂,e₂⟩ := hvw
    exact ⟨h₂.trans h₁,(congrArg (fun d => restrict d h₂) e₁).trans e₂⟩

theorem requirements_mono {v u : Presentation κ θ} (h : v ≤ u) :
    u.diagram.requirements ⊆ v.diagram.requirements := by
  obtain ⟨hvu,he⟩ := h
  rw [← he]
  apply (Diagram.requirements_subset_iff _ _).mpr
  constructor
  · intro i
    exact Or.inl ⟨⟨i.val,i.property.trans hvu⟩,rfl⟩
  · intro i j hij
    exact Or.inr ⟨⟨i.val,i.property.trans hvu⟩,⟨j.val,j.property.trans hvu⟩,hij,rfl⟩

variable [Fact (Cardinal.aleph0 < κ)]

abbrev Valid (u : Presentation κ θ) (G : Set (Condition κ θ)) (Coding : Condition κ θ → Prop) :=
  u.diagram.Valid G Coding

end Presentation

abbrev GroundCondition (κ θ : Cardinal.{u}) [Fact (Cardinal.aleph0 < κ)]
    (G : Set (Condition κ θ)) (Coding : Condition κ θ → Prop) :=
  {u : Presentation κ θ // u.Valid G Coding}

namespace Presentation

theorem exists_initial_pair (hθ : 1 < θ.ord) :
    ∃ z b : θ.ord.ToType, IsBot z ∧ z < b ∧ ∀ i ≤ b, i = z ∨ i = b := by
  let a₀ : Set.Iio θ.ord := ⟨0,zero_lt_one.trans hθ⟩
  let a₁ : Set.Iio θ.ord := ⟨1,hθ⟩
  let z := Ordinal.ToType.mk a₀
  let b := Ordinal.ToType.mk a₁
  have hab : a₀ < a₁ := (zero_lt_one : (0 : Ordinal.{u}) < 1)
  refine ⟨z,b,?_,Ordinal.ToType.mk.strictMono hab,?_⟩
  · intro i
    apply Ordinal.ToType.mk.symm.le_iff_le.mp
    rw [show Ordinal.ToType.mk.symm z = a₀ from OrderIso.symm_apply_apply _ _]
    exact (zero_le : (0 : Ordinal.{u}) ≤ i.toOrd.val)
  · intro i hi
    have h : Ordinal.ToType.mk.symm i ≤ a₁ := (Ordinal.ToType.mk.symm.monotone hi).trans_eq
      (OrderIso.symm_apply_apply _ _)
    rcases Order.le_one_iff.mp (show i.toOrd.val ≤ 1 from h) with h₀ | h₁
    · left
      exact (Ordinal.ToType.mk.apply_symm_apply i).symm.trans
        (congrArg Ordinal.ToType.mk.toFun (Subtype.ext h₀ : i.toOrd = a₀))
    · right
      exact (Ordinal.ToType.mk.apply_symm_apply i).symm.trans
        (congrArg Ordinal.ToType.mk.toFun (Subtype.ext h₁ : i.toOrd = a₁))

variable (z : θ.ord.ToType) (hz : IsBot z)

include hz in
theorem atFirst (i : Set.Iic z) : i.val = z := le_antisymm i.property (hz i.val)

include hz in
def singleton (p : Condition κ θ) : Presentation κ θ where
  last := z
  diagram.stage _ := p
  diagram.edge {i j} h := False.elim (lt_irrefl i ((Subtype.ext
    ((atFirst z hz j).trans (atFirst z hz i).symm) : j = i) ▸ h))

variable [Fact (Cardinal.aleph0 < κ)]

theorem singleton_valid (G : Set (Condition κ θ)) (Coding : Condition κ θ → Prop)
    (p : Condition κ θ) (hp : ∀ t : p.Poset, t ≤ p.point) (hc : Coding p) (hg : p ∈ G) :
    (singleton z hz p).Valid G Coding := by
  refine ⟨fun _ => ⟨hp,hc⟩,?_,?_⟩
  · apply (Diagram.requirements_subset_iff _ G).mpr
    refine ⟨fun _ => hg,?_⟩
    intro i j hij
    exact ((ne_of_lt hij) (Subtype.ext ((atFirst z hz i).trans (atFirst z hz j).symm))).elim
  · apply Diagram.localLifts_of_unique_predecessor
    exact fun _ i j _ _ => Subtype.ext ((atFirst z hz i).trans (atFirst z hz j).symm)

omit [Fact (Cardinal.aleph0 < κ)] in
private theorem diagram_eq_of_no_edges {I : Type u} [Preorder I] (D F : Diagram κ θ I)
    (hs : D.stage = F.stage) (hn : ∀ i j : I, ¬ i < j) : D = F := by
  cases D with | mk s e =>
  cases F with | mk t f =>
  cases hs
  congr 1
  funext i j hij
  exact (hn i j hij).elim

/-- Given two consecutive stages above the least index, one witnessed
refinement gives an end extension. Each row of the lower inverse limit
has at most one coordinate, so its lifting property follows from the
original partial projection. -/
theorem exists_two_stage_extension (b : θ.ord.ToType) (hzb : z < b)
    (hpair : ∀ i ≤ b, i = z ∨ i = b) (G : Set (Condition κ θ)) (Coding : Condition κ θ → Prop)
    (p q : Condition κ θ) (E : Edge p q)
    (hp : (∀ r : p.Poset, r ≤ p.point) ∧ Coding p ∧ p ∈ G)
    (hq : (∀ r : q.Poset, r ≤ q.point) ∧ Coding q ∧ q ∈ G)
    (hE : q.withPoint E.source ∈ G) :
    ∃ D : Diagram κ θ (Set.Iic b), D.Valid G Coding ∧
      (⟨b,D⟩ : Presentation κ θ) ≤ singleton z hz p ∧
      D.stage ⟨z,hzb.le⟩ = p ∧ D.stage ⟨b,show b ≤ b from le_rfl⟩ = q := by
  classical
  let lo : Set.Iic b := ⟨z,hzb.le⟩
  let hi : Set.Iic b := ⟨b,show b ≤ b from le_rfl⟩
  have shape (i : Set.Iic b) : i = lo ∨ i = hi :=
    (hpair i.val i.property).imp Subtype.ext Subtype.ext
  have strictly (i j : Set.Iic b) (h : i < j) : i = lo ∧ j = hi := by
    rcases shape i with rfl | rfl <;> rcases shape j with rfl | rfl
    · exact (lt_irrefl _ h).elim
    · exact ⟨rfl,rfl⟩
    · exact (not_lt_of_ge hzb.le h).elim
    · exact (lt_irrefl _ h).elim
  let Q (i : Set.Iic b) := if i = lo then p else q
  have hne : hi ≠ lo := fun h => hzb.ne (congrArg Subtype.val h).symm
  have h0 : Q lo = p := if_pos rfl
  have h1 : Q hi = q := if_neg hne
  let e : Edge (Q lo) (Q hi) := E.reindex h0 h1
  have he : (Q hi).withPoint e.source ∈ G := (E.reindex_source h0 h1) ▸ hE
  let edge {i j : Set.Iic b} (h : i < j) : Edge (Q i) (Q j) :=
    (strictly i j h).1.symm ▸ (strictly i j h).2.symm ▸ e
  let D : Diagram κ θ (Set.Iic b) := ⟨Q,edge⟩
  refine ⟨D,⟨?_,?_,?_⟩,⟨hzb.le,?_⟩,h0,h1⟩
  · intro i
    change (∀ r : (Q i).Poset, r ≤ (Q i).point) ∧ Coding (Q i)
    rcases shape i with rfl | rfl
    · rw [h0]
      exact ⟨hp.1,hp.2.1⟩
    · rw [h1]
      exact ⟨hq.1,hq.2.1⟩
  · apply (Diagram.requirements_subset_iff D G).mpr
    constructor
    · intro i
      change Q i ∈ G
      rcases shape i with rfl | rfl
      · rw [h0]
        exact hp.2.2
      · rw [h1]
        exact hq.2.2
    · intro i j hij
      obtain ⟨rfl,rfl⟩ := strictly i j hij
      exact he
  · apply Diagram.localLifts_of_unique_predecessor
    intro t i j hit hjt
    exact (strictly i t hit).1.trans (strictly j t hjt).1.symm
  · apply diagram_eq_of_no_edges
    · funext i
      change Q ⟨i.val,i.property.trans hzb.le⟩ = p
      have hi' : (⟨i.val,i.property.trans hzb.le⟩ : Set.Iic b) = lo := Subtype.ext (atFirst z hz i)
      rw [hi']
      exact h0
    · intro i j hij
      exact (ne_of_lt hij) (Subtype.ext ((atFirst z hz i).trans (atFirst z hz j).symm))

end Presentation
end Erdos1172Shioya.Uniformization
