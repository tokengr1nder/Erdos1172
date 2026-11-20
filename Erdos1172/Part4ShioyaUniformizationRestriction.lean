/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaUniformizationMixedDiagrams

@[expose] public section

/-! # Local characterization of valid ground uniformization diagrams

Restricting first to a set of stages and then to one of its subsets
preserves the entire finite-path domain and the restricted lower threads.
Thus validity of every short restriction tests Definition 38 on the
original diagram, including its designated edge sources.
-/

set_option autoImplicit false
noncomputable section
universe u
open bSet Erdos1172PosetCompletion
open scoped Flypitch
namespace Erdos1172Shioya.Uniformization.MixedDiagram

open InverseSystem
variable {κ θ : Cardinal.{u}} {I : Type u} [Preorder I]

structure Nested (x : Set I) (y : Set x) (z : Set I) : Prop where
  inside : z ⊆ x
  mem : ∀ i : x, i ∈ y ↔ i.val ∈ z

namespace Nested

variable {x : Set I} {y : Set x} {z : Set I} (a : Nested x y z)

def up (i : y) : z := ⟨i.val.val,(a.mem i.val).mp i.property⟩
def down (i : z) : y := ⟨⟨i.val,a.inside i.property⟩,(a.mem _).mpr i.property⟩

def upLower {γ : y} (i : (y ∩ Set.Iio γ.val : Set x)) :
    (z ∩ Set.Iio (a.up γ).val : Set I) :=
  ⟨i.val.val,(a.mem i.val).mp i.property.1,i.property.2⟩

def downLower {γ : y} (i : (z ∩ Set.Iio (a.up γ).val : Set I)) :
    (y ∩ Set.Iio γ.val : Set x) :=
  ⟨⟨i.val,a.inside i.property.1⟩,(a.mem _).mpr i.property.1,i.property.2⟩

variable [hκ : Fact (Cardinal.aleph0 < κ)] (D : Diagram κ θ I)
local notation "R" => restrict D x

private theorem down_path (j : z) (q : D.poset j.val)
    (hq : q ∈ (R).jointDomain y (a.down j)) (l : List z) (hl : Descending j l) :
    q ∈ (pathMap D.poset D.projection hκ.out (fun i => (D.stage i).complete) z j ⟨l,hl⟩).dom := by
  induction l generalizing j with
  | nil => exact Set.mem_univ _
  | cons i l ih =>
    have hij : a.down i < a.down j := hl.1
    have hd := jointDomain_direct (R).poset (R).projection hκ.out (fun k => ((R).stage k).complete) hij hq
    have hp := jointDomain_project (R).poset (R).projection hκ.out (fun k => ((R).stage k).complete) hij hq
    exact ⟨hd,ih i _ hp hl.2⟩

private theorem up_path (j : y) (q : D.poset j.val.val) (hq : q ∈ D.jointDomain z (a.up j))
    (l : List y) (hl : Descending j l) :
    q ∈ (pathMap (R).poset (R).projection hκ.out (fun i => ((R).stage i).complete) y j ⟨l,hl⟩).dom := by
  induction l generalizing j with
  | nil => exact Set.mem_univ _
  | cons i l ih =>
    have hij : a.up i < a.up j := hl.1
    have hd := jointDomain_direct D.poset D.projection hκ.out (fun k => (D.stage k).complete) hij hq
    have hp := jointDomain_project D.poset D.projection hκ.out (fun k => (D.stage k).complete) hij hq
    exact ⟨hd,ih i _ hp hl.2⟩

private theorem joint_iff (γ : y) (q : D.poset γ.val.val) :
    q ∈ (R).jointDomain y γ ↔ q ∈ D.jointDomain z (a.up γ) :=
  ⟨fun h l => a.down_path D (a.up γ) q h l.val l.property,
   fun h l => a.up_path D γ q h l.val l.property⟩

omit hκ in
private theorem guard_iff (γ : y) (q : D.poset γ.val.val) :
    (R).guard y γ q ↔ D.guard z (a.up γ) q :=
  ⟨fun h => ⟨fun i hi => h.1 (a.down i) hi,fun i j hij hj hd => h.2 (a.down i) (a.down j) hij hj hd⟩,
   fun h => ⟨fun i hi => h.1 (a.up i) hi,fun i j hij hj hd => h.2 (a.up i) (a.up j) hij hj hd⟩⟩

def upThread (γ : y) (t : (R).lowerThread y γ) : D.lowerThread z (a.up γ) :=
  ⟨fun i => t.val (a.downLower i),fun i j h => t.property (a.downLower i) (a.downLower j) h⟩

def downThread (γ : y) (t : D.lowerThread z (a.up γ)) : (R).lowerThread y γ :=
  ⟨fun i => t.val (a.upLower i),fun i j h => t.property (a.upLower i) (a.upLower j) h⟩

end Nested

variable [hκ : Fact (Cardinal.aleph0 < κ)]

def liftsOn (D : Diagram κ θ I) (z : Set I) : Prop :=
  ∀ (γ : z), (∀ i : z, i ≤ γ) → ∀ q ∈ D.jointDomain z γ, D.guard z γ q →
    ∀ r : D.lowerThread z γ, (∀ i, ∃ hd, r.val i ≤ (D.projection i.property.2).proj ⟨q,hd⟩) →
      ∃ q' ≤ q, q' ∈ D.jointDomain z γ ∧
        ∀ i, ∃ hd, (D.projection i.property.2).proj ⟨q',hd⟩ ≤ r.val i

private theorem nested_lifts_iff {x : Set I} {y : Set x} {z : Set I} (a : Nested x y z)
    (D : Diagram κ θ I) : liftsOn (restrict D x) y ↔ liftsOn D z := by
  constructor
  · intro h j hm q hd hg t ht
    let γ := a.down j
    let r := a.downThread D γ t
    obtain ⟨q',hle,hd',hs⟩ := h γ (fun i => hm (a.up i)) q ((a.joint_iff D γ q).mpr hd)
      ((a.guard_iff D γ q).mpr hg) r (fun i => ht (a.upLower i))
    exact ⟨q',hle,(a.joint_iff D γ q').mp hd',fun i => hs (a.downLower i)⟩
  · intro h γ hm q hd hg t ht
    let r := a.upThread D γ t
    obtain ⟨q',hle,hd',hs⟩ := h (a.up γ) (fun i => hm (a.down i)) q ((a.joint_iff D γ q).mp hd)
      ((a.guard_iff D γ q).mp hg) r (fun i => ht (a.downLower i))
    exact ⟨q',hle,(a.joint_iff D γ q').mpr hd',fun i => hs (a.upLower i)⟩

theorem restrict_localLifts (D : Diagram κ θ I) (h : D.localLifts) (x : Set I) :
    (restrict D x).localLifts := by
  intro y hy
  let z := {i : I | ∃ hi : i ∈ x, (⟨i,hi⟩ : x) ∈ y}
  have a : Nested x y z := ⟨fun _ hi => hi.choose,fun i =>
    ⟨fun hi => ⟨i.property,hi⟩,fun hi => hi.choose_spec⟩⟩
  have hsmall : Cardinal.mk z < κ :=
    (Cardinal.mk_le_of_injective (f := a.down)
      (fun _ _ he => Subtype.ext (congrArg (fun i : y => i.val.val) he))).trans_lt hy
  exact (nested_lifts_iff a D).mpr (h z hsmall)

theorem restrict_valid (D : Diagram κ θ I) {G : Set (Condition κ θ)} {Coding : Condition κ θ → Prop}
    (h : D.Valid G Coding) (x : Set I) : (restrict D x).Valid G Coding := by
  obtain ⟨ht,hr,hl⟩ := h
  refine ⟨fun i => ht i.val,?_,restrict_localLifts D hl x⟩
  have hg := (D.requirements_subset_iff G).mp hr
  exact ((restrict D x).requirements_subset_iff G).mpr
    ⟨fun i => hg.1 i.val,fun i j hij => hg.2 i.val j.val hij⟩

theorem valid_iff_short_restrictions (D : Diagram κ θ I) (G : Set (Condition κ θ))
    (Coding : Condition κ θ → Prop) :
    D.Valid G Coding ↔ ∀ x : Set I, Cardinal.mk x < κ → (restrict D x).Valid G Coding := by
  refine ⟨fun h x _ => restrict_valid D h x,?_⟩
  intro h
  have single (i : I) := h {i} ((Set.finite_singleton i).lt_aleph0.trans hκ.out)
  refine ⟨fun i => (single i).1 ⟨i,Set.mem_singleton i⟩,?_,?_⟩
  · apply (D.requirements_subset_iff G).mpr
    constructor
    · intro i
      exact (((restrict D {i}).requirements_subset_iff G).mp (single i).2.1).1 ⟨i,Set.mem_singleton i⟩
    · intro i j hij
      let x : Set I := {i,j}
      have hv := h x (((Set.finite_singleton j).insert i).lt_aleph0.trans hκ.out)
      exact (((restrict D x).requirements_subset_iff G).mp hv.2.1).2
        ⟨i,Set.mem_insert i _⟩ ⟨j,Set.mem_insert_of_mem _ (Set.mem_singleton j)⟩ hij
  · intro x hx
    have a : Nested x Set.univ x := ⟨fun _ hi => hi,fun i => ⟨fun _ => i.property,fun _ => Set.mem_univ i⟩⟩
    have huniv : Cardinal.mk (Set.univ : Set x) < κ := by rwa [Cardinal.mk_univ]
    exact (nested_lifts_iff a D).mp ((h x hx).2.2 Set.univ huniv)

theorem ground_mem_family_iff_valid [Nonempty (Condition κ θ)] (Coding : Condition κ θ → Prop)
    (D : Diagram κ θ I) {Γ : Algebra κ θ} (hn : Γ ≠ ⊥) :
    Γ ≤ check (code D) ∈ᴮ family I Coding ↔ D.Valid {s | Γ ≤ condition s} Coding :=
  (ground_mem_family_iff Coding D hn).trans (valid_iff_short_restrictions D _ Coding).symm

/-- Validity is local on a cover by initial segments. Every lifting test
has a specified greatest stage, even if its predecessors are cofinal below it. -/
theorem valid_iff_initial_cover (D : Diagram κ θ I) (G : Set (Condition κ θ))
    (Coding : Condition κ θ → Prop) {J : Type u} (bound : J → I)
    (cofinal : ∀ i : I, ∃ j, i ≤ bound j) :
    D.Valid G Coding ↔ ∀ j, (restrict D (Set.Iic (bound j))).Valid G Coding := by
  refine ⟨fun h j => restrict_valid D h _,?_⟩
  intro h
  constructor
  · intro i
    obtain ⟨j,hj⟩ := cofinal i
    exact (h j).1 ⟨i,hj⟩
  constructor
  · apply (D.requirements_subset_iff G).mpr
    constructor
    · intro i
      obtain ⟨j,hj⟩ := cofinal i
      exact (((restrict D (Set.Iic (bound j))).requirements_subset_iff G).mp (h j).2.1).1 ⟨i,hj⟩
    · intro i k hik
      obtain ⟨j,hj⟩ := cofinal k
      exact (((restrict D (Set.Iic (bound j))).requirements_subset_iff G).mp (h j).2.1).2
        ⟨i,hik.le.trans hj⟩ ⟨k,hj⟩ hik
  · intro x hx γ hm
    obtain ⟨j,hj⟩ := cofinal γ.val
    let s := Set.Iic (bound j)
    let y : Set s := {i | i.val ∈ x}
    have a : Nested s y x :=
      ⟨fun i hi => (show i ≤ γ.val from hm ⟨i,hi⟩).trans hj,fun _ => Iff.rfl⟩
    have hy : Cardinal.mk y < κ := (Cardinal.mk_le_of_injective (f := a.up)
      (fun _ _ he => Subtype.ext (Subtype.ext (congrArg (fun k : x => k.val) he)))).trans_lt hx
    exact (nested_lifts_iff a D).mp ((h j).2.2 y hy) γ hm

private theorem joint_restrict_path (D : Diagram κ θ I) {x y : Set I} (hsub : y ⊆ x)
    (j : y) (p : D.poset j.val) (hp : p ∈ D.jointDomain x ⟨j.val,hsub j.property⟩)
    (l : List y) (hl : Descending j l) :
    p ∈ (pathMap D.poset D.projection hκ.out (fun k => (D.stage k).complete) y j ⟨l,hl⟩).dom := by
  induction l generalizing j with
  | nil => exact Set.mem_univ _
  | cons i l ih =>
    have hij : (⟨i.val,hsub i.property⟩ : x) < ⟨j.val,hsub j.property⟩ := hl.1
    have hd := jointDomain_direct D.poset D.projection hκ.out (fun k => (D.stage k).complete) hij hp
    have ht := jointDomain_project D.poset D.projection hκ.out (fun k => (D.stage k).complete) hij hp
    exact ⟨hd,ih i _ ht hl.2⟩

/-- For each lifting test it suffices to lift on a restriction containing its
greatest stage and cofinal among its strict predecessors. A common refinement
in the full joint domain restores all remaining coordinates by thread coherence. -/
theorem localLifts_of_cofinal_restrictions {K : Type u} [PartialOrder K] (D : Diagram κ θ K)
    (coding : ∀ i, (D.stage i).CodesDense)
    (cover : ∀ (x : Set K), Cardinal.mk x < κ → ∀ (γ : x), (∀ i : x, i ≤ γ) →
      ∃ y : Set K, y ⊆ x ∧ γ.val ∈ y ∧
        (∀ i : (x ∩ Set.Iio γ.val : Set K), ∃ j : (y ∩ Set.Iio γ.val : Set K), i.val ≤ j.val) ∧
        (restrict D y).localLifts) : D.localLifts := by
  intro x hx γ hm q hq hg r hr
  obtain ⟨y,hsub,hγ,cof,lifts⟩ := cover x hx γ hm
  let γ' : y := ⟨γ.val,hγ⟩
  let inc (i : y) : x := ⟨i.val,hsub i.property⟩
  let lower (i : (y ∩ Set.Iio γ.val : Set K)) : (x ∩ Set.Iio γ.val : Set K) :=
    ⟨i.val,hsub i.property.1,i.property.2⟩
  have hy : Cardinal.mk (Set.univ : Set y) < κ := by
    rw [Cardinal.mk_univ]
    exact (Cardinal.mk_le_mk_of_subset hsub).trans_lt hx
  have all : Nested y Set.univ y :=
    ⟨fun _ h => h,fun i => ⟨fun _ => i.property,fun _ => Set.mem_univ i⟩⟩
  have hL := (nested_lifts_iff all D).mp (lifts Set.univ hy)
  have hd : q ∈ D.jointDomain y γ' := fun l => joint_restrict_path D hsub γ' q hq l.val l.property
  have hb : D.guard y γ' q :=
    ⟨fun i h => hg.1 (inc i) h,fun i j hij hj => hg.2 (inc i) (inc j) hij hj⟩
  let t : D.lowerThread y γ' :=
    ⟨fun i => r.val (lower i),fun i j h => r.property (lower i) (lower j) h⟩
  obtain ⟨p,hp,_,hit⟩ := hL γ' (fun i => hm (inc i)) q hd hb t (fun i => hr (lower i))
  obtain ⟨z,hzp,hz⟩ := jointDomain_dense D.poset D.projection hκ.out (fun k => (D.stage k).complete) x hx γ p
  have hzq := hzp.trans hp
  let v := D.projectedThread coding z hz (D.guard_mono hzq hq hg)
  refine ⟨z,hzq,hz,?_⟩
  intro i
  obtain ⟨j,hij⟩ := cof i
  obtain ⟨hdp,hp'⟩ := hit j
  have direct (i : (x ∩ Set.Iio γ.val : Set K)) : z ∈ (D.projection i.property.2).dom :=
    jointDomain_direct D.poset D.projection hκ.out (fun k => (D.stage k).complete)
      (i := ⟨i.val,i.property.1⟩) i.property.2 hz
  have hv : v.val (lower j) ≤ r.val (lower j) := ((D.projection j.property.2).proj.monotone
    (show (⟨z,direct (lower j)⟩ : (D.projection j.property.2).dom) ≤ ⟨p,hdp⟩ from hzp)).trans hp'
  refine ⟨direct i,show v.val i ≤ r.val i from ?_⟩
  rcases (show i ≤ lower j from hij).lt_or_eq with h | h
  · obtain ⟨hvdom,hvi⟩ := v.property i (lower j) h
    obtain ⟨hrdom,hri⟩ := r.property i (lower j) h
    exact hvi.ge.trans (((D.projection h).proj.monotone
      (show (⟨v.val (lower j),hvdom⟩ : (D.projection h).dom) ≤ ⟨r.val (lower j),hrdom⟩ from hv)).trans hri.le)
  · exact h ▸ hv

end Erdos1172Shioya.Uniformization.MixedDiagram
