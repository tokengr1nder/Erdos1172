/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaRecoveredProjection
public import Mathlib.Order.PFilter

@[expose] public section

/-! # Master points for countable recovered filters

In the auxiliary extension of Theorem 47 of Eskew and Hayut, the recovered
stage filters are countable. The images of those filters therefore have
infima in the target stages. Closed domains and continuous projections
identify the images of the infima along each diagram edge.
-/

set_option autoImplicit false
noncomputable section
universe u
open Erdos1172PosetCompletion
namespace Erdos1172Shioya.RecoveredMaster

private theorem countable_chain (A : Type u) [Preorder A] [Nonempty A] [Countable A]
    (dir : ∀ a b : A, ∃ c, c ≤ a ∧ c ≤ b) :
    ∃ f : ULift.{u} ℕ → A, Antitone f ∧ ∀ a, ∃ n, f n ≤ a := by
  classical
  obtain ⟨g,hg⟩ := exists_surjective_nat A
  choose lower h₁ h₂ using dir
  let f : ℕ → A := Nat.rec (g 0) (fun n x => lower x (g (n+1)))
  have anti : Antitone f := antitone_nat_of_succ_le (fun n => h₁ (f n) (g (n+1)))
  refine ⟨fun n => f n.down,fun _ _ h => anti h,?_⟩
  intro a
  obtain ⟨n,rfl⟩ := hg a
  cases n with
  | zero => exact ⟨⟨0⟩,le_rfl⟩
  | succ n => exact ⟨⟨n+1⟩,h₂ (f n) (g (n+1))⟩

private theorem glb_coinitial {P : Type u} [PartialOrder P] {s t : Set P}
    (sub : s ⊆ t) (coi : ∀ y ∈ t, ∃ z ∈ s, z ≤ y) (p : P) : IsGLB s p ↔ IsGLB t p := by
  have he : lowerBounds s = lowerBounds t := by
    ext z
    constructor
    · intro h y hy
      obtain ⟨w,hw,hwy⟩ := coi y hy
      exact (h hw).trans hwy
    · intro h y hy
      exact h (sub hy)
  change IsGreatest (lowerBounds s) p ↔ IsGreatest (lowerBounds t) p
  rw [he]

variable {Λ : Cardinal.{u}} {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- Countability is needed only for the directed family. The target need
only admit infima of descending sequences of length less than Λ. -/
theorem exists_image_master (unc : Cardinal.aleph0 < Λ) (complete : ShortInfima Λ P)
    {A : Type u} [Preorder A] [Nonempty A] [Countable A] (dir : ∀ a b : A, ∃ c, c ≤ a ∧ c ≤ b)
    (image : A →o P) : ∃ p, IsGLB (Set.range image) p := by
  obtain ⟨f,hf,coi⟩ := countable_chain A dir
  have hL : Cardinal.mk (ULift.{u} ℕ) < Λ := by simpa using unc
  obtain ⟨p,hp⟩ := complete _ hL (fun n => image (f n)) (fun _ _ h => image.monotone (hf h))
  refine ⟨p,(glb_coinitial (Set.range_comp_subset_range _ _) ?_ p).mp hp⟩
  rintro _ ⟨a,rfl⟩
  obtain ⟨n,hn⟩ := coi a
  exact ⟨_,Set.mem_range_self n,image.monotone hn⟩

/-- A directed countable family of legal edge witnesses that is coinitial
at both ends determines the projection of the source master point. -/
theorem projection_master (unc : Cardinal.aleph0 < Λ) (π : PartialProjection Λ P Q)
    {A : Type u} [Preorder A] [Nonempty A] [Countable A] (dir : ∀ a b : A, ∃ c, c ≤ a ∧ c ≤ b)
    (lift : A →o π.dom) {s : Set P} {t : Set Q}
    (hs : ∀ a, (lift a).val ∈ s) (ht : ∀ a, π.proj (lift a) ∈ t)
    (cs : ∀ p ∈ s, ∃ a, (lift a).val ≤ p) (ct : ∀ q ∈ t, ∃ a, π.proj (lift a) ≤ q)
    {p : P} {q : Q} (hp : IsGLB s p) (hq : IsGLB t q) :
    ∃ hd : p ∈ π.dom, π.proj ⟨p,hd⟩ = q := by
  obtain ⟨f,hf,coi⟩ := countable_chain A dir
  let g (n : ULift.{u} ℕ) := lift (f n)
  have hg : Antitone g := fun _ _ h => lift.monotone (hf h)
  have hL : Cardinal.mk (ULift.{u} ℕ) < Λ := by simpa using unc
  have source : IsGLB (Set.range (fun n => (g n).val)) p := by
    apply (glb_coinitial (Set.range_subset_iff.mpr fun n => hs (f n)) ?_ p).mpr hp
    intro z hz
    obtain ⟨a,ha⟩ := cs z hz
    obtain ⟨n,hn⟩ := coi a
    exact ⟨_,Set.mem_range_self n,le_trans (lift.monotone hn) ha⟩
  have hd := π.closed _ hL g hg p source
  have target := π.continuous _ hL g hg ⟨p,hd⟩ source
  refine ⟨hd,IsGLB.unique ((glb_coinitial (Set.range_subset_iff.mpr fun n => ht (f n)) ?_ _).mp target) hq⟩
  intro z hz
  obtain ⟨a,ha⟩ := ct z hz
  obtain ⟨n,hn⟩ := coi a
  exact ⟨_,Set.mem_range_self n,(π.proj.monotone (lift.monotone hn)).trans ha⟩

open Uniformization
variable {κ θ : Cardinal.{u}} [Fact (Cardinal.aleph0 < κ)] {I : Type u} [Preorder I]
variable (D : Diagram κ θ I) (F : Order.PFilter (Algebra κ θ))

/-- Truth for the repointing cones that define the recovered filter. -/
def realized (i : I) : Set (D.poset i) := {p | condition ((D.stage i).withPoint p) ∈ F}

def readsJoin {B : Type u} [CompleteLattice B] (G : Order.PFilter B) {A : Type u} (v : A → B) : Prop :=
  (⨆ a, v a) ∈ G → ∃ a, v a ∈ G

/-- Only the three indicated families of joins have to be read by the
realizing filter. They concern pairs in one stage, the dense source domain
below a point, and preimages of a recovered target point. -/
structure ReadsEdges : Prop where
  pairs : ∀ i (a b : D.poset i), readsJoin F
    (fun c : {c : D.poset i // c ≤ a ∧ c ≤ b} => condition ((D.stage i).withPoint c.val))
  domains : ∀ (i j : I) (h : i < j) (b : D.poset j), readsJoin F
    (fun c : {c : D.poset j // c ∈ (D.projection h).dom ∧ c ≤ b} => condition ((D.stage j).withPoint c.val))
  preimages : ∀ (i j : I) (h : i < j) (a : D.poset i), readsJoin F
    (fun c : (D.edge h).liftsOf a => condition ((D.stage j).withPoint c.val.val))

/-- A dense set deciding a single ground join. -/
def decisionSet {B : Type u} [CompleteBooleanAlgebra B] {A : Type u} (v : A → B) : Set B :=
  {p | p ≠ ⊥ ∧ (p ⊓ (⨆ a, v a) = ⊥ ∨ ∃ a, p ≤ v a)}

theorem decisionSet_dense {B : Type u} [CompleteBooleanAlgebra B] {A : Type u} (v : A → B)
    (b : B) (hb : b ≠ ⊥) : ∃ c ∈ decisionSet v, c ≤ b := by
  classical
  by_cases h : ∃ a, b ⊓ v a ≠ ⊥
  · obtain ⟨a,ha⟩ := h
    exact ⟨_,⟨ha,Or.inr ⟨a,inf_le_right⟩⟩,inf_le_left⟩
  · refine ⟨b,⟨hb,Or.inl ?_⟩,le_rfl⟩
    rw [inf_iSup_eq]
    exact iSup_eq_bot.mpr (fun a => by_contra fun ha => h ⟨a,ha⟩)

theorem readsJoin_of_decisionSet {B : Type u} [CompleteBooleanAlgebra B] (G : Order.PFilter B)
    (proper : ⊥ ∉ G) {A : Type u} (v : A → B) (hit : ∃ b ∈ decisionSet v, b ∈ G) : readsJoin G v := by
  intro hv
  obtain ⟨b,⟨_,hz | ⟨a,ha⟩⟩,hb⟩ := hit
  · exact (proper (hz ▸ G.inf_mem hb hv)).elim
  · exact ⟨a,Order.PFilter.mem_of_le ha hb⟩

/-- The list of dense sets is determined by the ground stage data. -/
inductive edgeTests : Set (Set (Algebra κ θ))
  | pairs (i : I) (a b : D.poset i) : edgeTests
      (decisionSet (fun c : {c : D.poset i // c ≤ a ∧ c ≤ b} => condition ((D.stage i).withPoint c.val)))
  | domains (i j : I) (h : i < j) (b : D.poset j) : edgeTests
      (decisionSet (fun c : {c : D.poset j // c ∈ (D.projection h).dom ∧ c ≤ b} =>
        condition ((D.stage j).withPoint c.val)))
  | preimages (i j : I) (h : i < j) (a : D.poset i) : edgeTests
      (decisionSet (fun c : (D.edge h).liftsOf a => condition ((D.stage j).withPoint c.val.val)))

theorem edgeTests_dense {S : Set (Algebra κ θ)} (hS : edgeTests D S) (b : Algebra κ θ) (hb : b ≠ ⊥) :
    ∃ c ∈ S, c ≤ b := by cases hS <;> exact decisionSet_dense _ b hb

theorem readsEdges_of_meets (proper : ⊥ ∉ F) (meets : ∀ S, edgeTests D S → ∃ b ∈ S, b ∈ F) :
    ReadsEdges D F where
  pairs i a b := readsJoin_of_decisionSet F proper _ (meets _ (.pairs i a b))
  domains i j h b := readsJoin_of_decisionSet F proper _ (meets _ (.domains i j h b))
  preimages i j h a := readsJoin_of_decisionSet F proper _ (meets _ (.preimages i j h a))

variable {D F}
variable (hc : ∀ i, (D.stage i).CodesDense) (read : ReadsEdges D F)

include hc read in
private theorem realized_directed (i : I) : DirectedOn (· ≥ ·) (realized D F i) := by
  intro a ha b hb
  have hit : condition ((D.stage i).withPoint a) ⊓ condition ((D.stage i).withPoint b) ∈ F := F.inf_mem ha hb
  rw [(hc i).cones_directed] at hit
  obtain ⟨c,hc'⟩ := read.pairs i a b hit
  exact ⟨c.val,hc',c.property⟩

include read in
private theorem realized_domain {i j : I} (h : i < j) (b : D.poset j) (hb : b ∈ realized D F j) :
    ∃ c ∈ realized D F j, c ∈ (D.projection h).dom ∧ c ≤ b := by
  let Z : Set (D.poset j) := {c | c ∈ (D.projection h).dom ∧ c ≤ b}
  have hd : ∀ a ≤ b, ∃ c ∈ Z, c ≤ a := by
    intro a ha
    obtain ⟨c,hca⟩ := (D.projection h).dense a
    exact ⟨c.val,⟨c.property,hca.trans ha⟩,hca⟩
  have cover := ((D.stage j).withPoint b).withPoint_predense Z hd
  obtain ⟨c,hc'⟩ := read.domains i j h b (Order.PFilter.mem_of_le cover hb)
  exact ⟨c.val,hc',c.property⟩

abbrev edgePoints {i j : I} (h : i < j) :=
  {c : D.poset j // c ∈ realized D F j ∧ c ∈ (D.projection h).dom ∧ c ≤ (D.edge h).source}

variable (req : ∀ p ∈ D.requirements, condition p ∈ F)

include hc read req in
private theorem edge_coinitial {i j : I} (h : i < j) (b : D.poset j) (hb : b ∈ realized D F j) :
    ∃ c : edgePoints (D := D) (F := F) h, c.val ≤ b := by
  have hs : (D.edge h).source ∈ realized D F j := req _ (Or.inr ⟨i,j,h,rfl⟩)
  obtain ⟨a,ha,hab,has⟩ := realized_directed hc read j b hb (D.edge h).source hs
  obtain ⟨c,hw,hd,hca⟩ := realized_domain read h a ha
  exact ⟨⟨c,hw,hd,hca.trans has⟩,hca.trans hab⟩

include hc read req in
private theorem edge_project_coinitial {i j : I} (h : i < j) (a : D.poset i) (ha : a ∈ realized D F i) :
    ∃ c : edgePoints (D := D) (F := F) h, (D.projection h).proj ⟨c.val,c.property.2.1⟩ ≤ a := by
  have hs : condition ((D.stage j).withPoint (D.edge h).source) ∈ F := req _ (Or.inr ⟨i,j,h,rfl⟩)
  have hit : condition ((D.stage j).withPoint (D.edge h).source) ⊓ condition ((D.stage i).withPoint a) ∈ F :=
    F.inf_mem hs ha
  rw [(D.edge h).recovered_projection (hc i) a] at hit
  obtain ⟨c,hc'⟩ := read.preimages i j h a hit
  exact ⟨⟨c.val.val,hc',c.val.property,c.property.1⟩,c.property.2⟩

set_option maxHeartbeats 1000000 in
include hc read req in
/-- The external point maps may take values in larger, closed stages. They
need only preserve order and commute with the specified projection on
old domain points. The master points are calculated, including the
inequality below every designated edge source. -/
theorem exists_lifted_thread {Λ : Cardinal.{u}} (unc : Cardinal.aleph0 < Λ)
    (T : I → Type u) [∀ i, PartialOrder (T i)] (complete : ∀ i, ShortInfima Λ (T i))
    (π : ∀ {i j : I}, i < j → PartialProjection Λ (T j) (T i))
    (J : ∀ i, D.poset i →o T i)
    (square : ∀ {i j : I} (h : i < j) (a : (D.projection h).dom),
      ∃ hd : J j a.val ∈ (π h).dom, (π h).proj ⟨J j a.val,hd⟩ = J i ((D.projection h).proj a))
    (count : ∀ i, (realized D F i).Countable) (x : Set I) :
    ∃ m : InverseSystem.Thread T π x,
      (∀ i, IsGLB (J i.val '' realized D F i.val) (m.val i)) ∧
      ∀ (i j : x) (h : i < j), m.val j ≤ J j.val (D.edge h).source := by
  classical
  let H := realized D F
  have (i : I) : Nonempty (H i) := ⟨⟨(D.stage i).point,req _ (Or.inl ⟨i,rfl⟩)⟩⟩
  have (i : I) : Countable (H i) := count i
  have directed (i : I) (a b : H i) : ∃ c : H i, c ≤ a ∧ c ≤ b := by
    obtain ⟨c,ch,ca,cb⟩ := realized_directed hc read i a.val a.property b.val b.property
    exact ⟨⟨c,ch⟩,ca,cb⟩
  have glb (i : I) : ∃ m, IsGLB (J i '' H i) m := by
    let im : H i →o T i := ⟨fun a => J i a.val,fun _ _ h => (J i).monotone h⟩
    have eq : Set.range im = J i '' H i := Set.ext (fun _ => ⟨fun ⟨a,ha⟩ => ⟨a.val,a.property,ha⟩,
      fun ⟨a,ha,he⟩ => ⟨⟨a,ha⟩,he⟩⟩)
    exact eq ▸ exists_image_master unc (complete i) (directed i) im
  choose m hm using glb
  have edges {i j : I} (h : i < j) : ∃ hd : m j ∈ (π h).dom, (π h).proj ⟨m j,hd⟩ = m i := by
    let A := edgePoints (D := D) (F := F) h
    have : Nonempty A := by
      obtain ⟨c,_⟩ := edge_coinitial hc read req h (D.stage j).point (req _ (Or.inl ⟨j,rfl⟩))
      exact ⟨c⟩
    have : Countable A := Function.Injective.countable (f := fun c : A => (⟨c.val,c.property.1⟩ : H j))
      (fun _ _ he => Subtype.ext (congrArg (fun b : H j => b.val) he))
    have da (a b : A) : ∃ c : A, c ≤ a ∧ c ≤ b := by
      obtain ⟨z,hz,hza,hzb⟩ := realized_directed hc read j a.val a.property.1 b.val b.property.1
      obtain ⟨c,hcz⟩ := edge_coinitial hc read req h z hz
      exact ⟨c,hcz.trans hza,hcz.trans hzb⟩
    let old (c : A) : (D.projection h).dom := ⟨c.val,c.property.2.1⟩
    let lift : A →o (π h).dom := ⟨fun c => ⟨J j c.val,(square h (old c)).choose⟩,
      fun _ _ hle => (J j).monotone hle⟩
    have sq (c : A) : (π h).proj (lift c) = J i ((D.projection h).proj (old c)) := (square h (old c)).choose_spec
    apply projection_master unc (π h) da lift _ _ _ _ (hm j) (hm i)
    · exact fun c => ⟨c.val,c.property.1,rfl⟩
    · intro c
      exact ⟨_,Order.PFilter.mem_of_le (condition_mono ((D.edge h).repoint_le (old c) c.property.2.2 le_rfl))
        c.property.1,(sq c).symm⟩
    · rintro _ ⟨b,hb,rfl⟩
      obtain ⟨c,hc'⟩ := edge_coinitial hc read req h b hb
      exact ⟨c,(J j).monotone hc'⟩
    · rintro _ ⟨a,ha,rfl⟩
      obtain ⟨c,hc'⟩ := edge_project_coinitial hc read req h a ha
      exact ⟨c,(sq c).le.trans ((J i).monotone hc')⟩
  refine ⟨⟨fun i => m i.val,fun _ _ h => edges h⟩,fun i => hm i.val,?_⟩
  exact fun i j h => (hm j.val).1 ⟨(D.edge h).source,req _ (Or.inr ⟨i.val,j.val,h,rfl⟩),rfl⟩

/-- For a lifted diagram with the indicated point maps, the master is
in every joint domain and below all the designated sources in its
projected thread. These conclusions hold on arbitrary subsystems. -/
theorem exists_guarded_master {Λ Θ : Cardinal.{u}} [fΛ : Fact (Cardinal.aleph0 < Λ)]
    (target : Diagram Λ Θ I) (J : ∀ i, D.poset i →o target.poset i)
    (square : ∀ {i j : I} (h : i < j) (a : (D.projection h).dom),
      ∃ hd : J j a.val ∈ (target.projection h).dom,
        (target.projection h).proj ⟨J j a.val,hd⟩ = J i ((D.projection h).proj a))
    (sources : ∀ {i j : I} (h : i < j), (target.edge h).source = J j (D.edge h).source)
    (proper : ⊥ ∉ F) (meets : ∀ S, edgeTests D S → ∃ b ∈ S, b ∈ F)
    (coding : ∀ i, (D.stage i).CodesDense) (requirements : ∀ p ∈ D.requirements, condition p ∈ F)
    (count : ∀ i, (realized D F i).Countable) (x : Set I) :
    ∃ m : InverseSystem.Thread target.poset target.projection x,
      (∀ i, IsGLB (J i.val '' realized D F i.val) (m.val i)) ∧
      ∀ γ, m.val γ ∈ target.jointDomain x γ ∧ target.guard x γ (m.val γ) := by
  obtain ⟨m,hm,hs⟩ := exists_lifted_thread coding (readsEdges_of_meets D F proper meets) requirements
    fΛ.out target.poset (fun i => (target.stage i).complete) target.projection J square count x
  refine ⟨m,hm,fun γ => ⟨InverseSystem.thread_mem_jointDomain target.poset target.projection fΛ.out
    (fun i => (target.stage i).complete) m γ,?_,?_⟩⟩
  · exact fun i h => (hs i γ h).trans_eq (sources h).symm
  · intro i j hij hj hd
    obtain ⟨_,he⟩ := m.property j γ hj
    exact he.le.trans ((hs i j hij).trans_eq (sources hij).symm)

end Erdos1172Shioya.RecoveredMaster
