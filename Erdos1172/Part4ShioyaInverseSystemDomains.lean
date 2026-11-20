/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaSimultaneousDecision
public import Mathlib.SetTheory.Cardinal.Arithmetic

@[expose] public section

/-! # The joint domains and threads of systems of partial projections -/

set_option autoImplicit false
noncomputable section
universe u

namespace Erdos1172Shioya.InverseSystem

variable {κ : Cardinal.{u}} {P : Type u} [PartialOrder P]

def ShortClosed (κ : Cardinal.{u}) (D : Set P) : Prop :=
  ∀ (L : Type u) [LinearOrder L] [WellFoundedLT L], Cardinal.mk L < κ →
    ∀ f : L → D, Antitone f → ∀ t, IsGLB (Set.range (fun i => (f i).val)) t → t ∈ D

private theorem lowerBound {L : Type u} [LinearOrder L] [WellFoundedLT L] (hP : ShortInfima κ P)
    (hL : Cardinal.mk L < κ) (p : P) (q : L → P) (hq : Antitone q) (hp : ∀ i, q i ≤ p) :
    ∃ b ≤ p, ∀ i, b ≤ q i := by
  classical
  by_cases hn : Nonempty L
  · obtain ⟨b,hb⟩ := hP L hL q hq
    exact ⟨b,(hb.1 (Set.mem_range_self hn.some)).trans (hp _),fun i => hb.1 (Set.mem_range_self i)⟩
  · exact ⟨p,le_rfl,fun i => (hn ⟨i⟩).elim⟩

/-- One pass through all dense requirements. Each point met in the pass
lies between its starting point and its common lower bound. -/
private theorem dense_sweep {L : Type u} (hP : ShortInfima κ P) (hL : Cardinal.mk L < κ)
    (D : L → Set P) (hd : ∀ i p, ∃ q ≤ p, q ∈ D i) (p : P) :
    ∃ b ≤ p, ∀ i, ∃ z ∈ D i, b ≤ z ∧ z ≤ p := by
  classical
  obtain ⟨_lo, _wf⟩ := exists_wellFoundedLT L
  letI := _lo
  haveI : WellFoundedLT (L) := _wf
  let stage (i : L) (prior : ∀ j < i, P) (z : P) := z ≤ p ∧ (∀ j hj, z ≤ prior j hj) ∧ z ∈ D i
  let _ : Nonempty P := ⟨p⟩
  let step (i : L) (prior : ∀ j < i, P) := Classical.epsilon (stage i prior)
  let q := wellFounded_lt.fix step
  have eqn (i : L) : q i = step i (fun j _ => q j) := WellFounded.fix_eq _ _ _
  have hstage (i : L) : stage i (fun j _ => q j) (q i) := by
    induction i using (wellFounded_lt : WellFounded ((· < ·) : L → L → Prop)).induction with
    | h i ih =>
      let g (j : Set.Iio i) := q j.val
      have hg : Antitone g := by
        intro j k hjk
        rcases hjk.lt_or_eq with hlt | rfl
        · exact (ih k.val k.property).2.1 j.val hlt
        · exact le_rfl
      obtain ⟨b,hbp,hb⟩ := lowerBound hP ((Cardinal.mk_set_le (Set.Iio i)).trans_lt hL) p g hg
        (fun j => (ih j.val j.property).1)
      obtain ⟨z,hzb,hz⟩ := hd i b
      exact (eqn i).symm ▸ Classical.epsilon_spec (p := stage i (fun j _ => q j))
        ⟨z,hzb.trans hbp,fun j hj => hzb.trans (hb ⟨j,hj⟩),hz⟩
  have hq : Antitone q := by
    intro i j hij
    rcases hij.lt_or_eq with hlt | rfl
    · exact (hstage j).2.1 i hlt
    · exact le_rfl
  obtain ⟨b,hbp,hb⟩ := lowerBound hP hL p q hq (fun i => (hstage i).1)
  exact ⟨b,hbp,fun i => ⟨q i,(hstage i).2.2,hb i,(hstage i).1⟩⟩

/-- A short intersection of downward closed dense sets is dense. -/
theorem short_dense_lower_intersection {K : Type u} (hP : ShortInfima κ P) (hK : Cardinal.mk K < κ)
    (D : K → Set P) (down : ∀ k, IsLowerSet (D k)) (hd : ∀ k p, ∃ q ≤ p, q ∈ D k) (p : P) :
    ∃ b ≤ p, ∀ k, b ∈ D k := by
  obtain ⟨b,hb,hw⟩ := dense_sweep hP hK D hd p
  refine ⟨b,hb,fun k => ?_⟩
  obtain ⟨z,hz,hbz,_⟩ := hw k
  exact down k hbz hz

/-- A short intersection of closed dense sets is dense. The sets need
only be closed under short infima, and can omit stronger conditions. -/
theorem short_closed_dense_intersection {K : Type u} (hκ : Cardinal.aleph0 < κ) (hP : ShortInfima κ P)
    (hK : Cardinal.mk K < κ) (D : K → Set P) (hc : ∀ k, ShortClosed κ (D k))
    (hd : ∀ k p, ∃ q ≤ p, q ∈ D k) (p : P) : ∃ r ≤ p, ∀ k, r ∈ D k := by
  classical
  choose next hn hw using fun z : P => dense_sweep hP hK D hd z
  let a (n : ℕ) := next^[n] p
  have ha (n : ℕ) : a (n+1) = next (a n) := Function.iterate_succ_apply' _ _ _
  have ham : Antitone a := antitone_nat_of_succ_le (fun n => (ha n) ▸ hn (a n))
  let L := ULift.{u} ℕ
  have hL : Cardinal.mk L < κ := by simpa [L] using hκ
  let f (n : L) := a n.down
  obtain ⟨r,hr⟩ := hP L hL f (fun _ _ h => ham h)
  refine ⟨r,hr.1 (Set.mem_range_self (ULift.up 0)),?_⟩
  intro k
  choose w hmem hbelow habove using fun n => hw (a n) k
  have hlo (n : ℕ) : a (n+1) ≤ w n := (ha n) ▸ hbelow n
  have hwm : Antitone w := antitone_nat_of_succ_le (fun n => (habove (n+1)).trans (hlo n))
  let g (n : L) : D k := ⟨w n.down,hmem _⟩
  apply hc k L hL g (fun _ _ h => hwm h) r
  refine ⟨Set.forall_mem_range.mpr (fun n => (hr.1 (Set.mem_range_self (ULift.up (n.down+1)))).trans (hlo n.down)),?_⟩
  intro z hz
  exact hr.2 (Set.forall_mem_range.mpr (fun n => (hz (Set.mem_range_self n)).trans (habove n.down)))

section Paths

variable {I : Type u} [Preorder I] (Q : I → Type u) [∀ i, PartialOrder (Q i)]
variable (π : ∀ {i j : I}, i < j → PartialProjection κ (Q j) (Q i))

def Descending (i : I) : List I → Prop
  | [] => True
  | j :: l => j < i ∧ Descending j l

def endpoint (i : I) : List I → I
  | [] => i
  | j :: l => endpoint j l

def pathProjection (hκ : Cardinal.aleph0 < κ) (hQ : ∀ i, ShortInfima κ (Q i)) (i : I) :
    (l : List I) → Descending i l → PartialProjection κ (Q i) (Q (endpoint i l))
  | [], _ => PartialProjection.identity
  | j :: l,h => (π h.1).comp (pathProjection hκ hQ j l h.2) hκ (hQ i)

variable (hκ : Cardinal.aleph0 < κ) (hQ : ∀ i, ShortInfima κ (Q i))

abbrev Path (x : Set I) (γ : x) := {l : List x // Descending γ l}

def pathMap (x : Set I) (γ : x) (l : Path x γ) : PartialProjection κ (Q γ.val) (Q (endpoint γ l.val).val) :=
  pathProjection (fun i : x => Q i.val) (fun h => π h) hκ (fun i => hQ i.val) γ l.val l.property

/-- A condition is in the joint domain when every finite path inside x
starting at γ is defined there, including paths with intermediate stages. -/
def jointDomain (x : Set I) (γ : x) : Set (Q γ.val) :=
  {q | ∀ l : Path x γ, q ∈ (pathMap Q π hκ hQ x γ l).dom}

theorem jointDomain_closed (x : Set I) (γ : x) :
    ShortClosed κ (jointDomain Q π hκ hQ x γ) := by
  intro L _ _ hL f hf r hr l
  let ρ := pathMap Q π hκ hQ x γ l
  let g (i : L) : ρ.dom := ⟨(f i).val,(f i).property l⟩
  exact ρ.closed L hL g (fun _ _ h => hf h) r hr

theorem jointDomain_dense (x : Set I) (hx : Cardinal.mk x < κ) (γ : x) (p : Q γ.val) :
    ∃ r ≤ p, r ∈ jointDomain Q π hκ hQ x γ := by
  have hpaths : Cardinal.mk (Path x γ) < κ := (Cardinal.mk_set_le {l : List x | Descending γ l}).trans_lt
    ((Cardinal.mk_list_le_max x).trans_lt (max_lt hκ hx))
  apply short_closed_dense_intersection hκ (hQ γ.val) hpaths (fun l => (pathMap Q π hκ hQ x γ l).dom)
    (fun l => (pathMap Q π hκ hQ x γ l).closed)
  intro l q
  obtain ⟨r,hr⟩ := (pathMap Q π hκ hQ x γ l).dense q
  exact ⟨r.val,hr,r.property⟩

theorem jointDomain_direct {x : Set I} {γ i : x} (hi : i < γ) {p : Q γ.val}
    (hp : p ∈ jointDomain Q π hκ hQ x γ) : p ∈ (π hi).dom :=
  (hp ⟨[i],hi,True.intro⟩).choose

theorem jointDomain_project {x : Set I} {γ i : x} (hi : i < γ) {p : Q γ.val}
    (hp : p ∈ jointDomain Q π hκ hQ x γ) :
    (π hi).proj ⟨p,jointDomain_direct Q π hκ hQ hi hp⟩ ∈ jointDomain Q π hκ hQ x i :=
  fun l => (hp ⟨i :: l.val,hi,l.property⟩).choose_spec

def Thread (x : Set I) := {t : ∀ i : x, Q i.val // ∀ (i j : x) (h : i < j),
  ∃ hd : t j ∈ (π h).dom, (π h).proj ⟨t j,hd⟩ = t i}

instance (x : Set I) : PartialOrder (Thread Q π x) := inferInstanceAs (PartialOrder (Subtype _))

/-- Along every finite descending path, projecting a thread coordinate gives
the coordinate at its endpoint. -/
theorem thread_path {x : Set I} (t : Thread Q π x) (γ : x) (l : Path x γ) :
    ∃ hd : t.val γ ∈ (pathMap Q π hκ hQ x γ l).dom,
      (pathMap Q π hκ hQ x γ l).proj ⟨t.val γ, hd⟩ = t.val (endpoint γ l.val) := by
  rcases l with ⟨l, hl⟩
  induction l generalizing γ with
  | nil => exact ⟨Set.mem_univ _, rfl⟩
  | cons i l ih =>
    obtain ⟨hd, he⟩ := t.property i γ hl.1
    obtain ⟨ht, het⟩ := ih i hl.2
    let σ := pathMap Q π hκ hQ x i ⟨l, hl.2⟩
    have hm : (π hl.1).proj ⟨t.val γ, hd⟩ ∈ σ.dom := he ▸ ht
    refine ⟨⟨hd, hm⟩, ?_⟩
    change σ.proj ⟨(π hl.1).proj ⟨t.val γ, hd⟩, hm⟩ = _
    exact (congrArg σ.proj (Subtype.ext he)).trans het

theorem thread_mem_jointDomain {x : Set I} (t : Thread Q π x) (γ : x) :
    t.val γ ∈ jointDomain Q π hκ hQ x γ :=
  fun l => (thread_path Q π hκ hQ t γ l).choose

theorem thread_glb_of_coordinates {x : Set I} {L : Type u} (f : L → Thread Q π x)
    (t : Thread Q π x) (ht : ∀ i, IsGLB (Set.range (fun k => (f k).val i)) (t.val i)) :
    IsGLB (Set.range f) t := by
  refine ⟨Set.forall_mem_range.mpr (fun k i => (ht i).1 (Set.mem_range_self k)), ?_⟩
  intro s hs i
  exact (ht i).2 (Set.forall_mem_range.mpr (fun k => hs (Set.mem_range_self k) i))

include hQ

/-- The infima in the individual stages form a compatible thread. -/
theorem exists_coordinate_glb {x : Set I} (L : Type u) [LinearOrder L] [WellFoundedLT L]
    (hL : Cardinal.mk L < κ) (f : L → Thread Q π x) (hf : Antitone f) :
    ∃ t : Thread Q π x, ∀ i, IsGLB (Set.range (fun k => (f k).val i)) (t.val i) := by
  classical
  choose q hq using fun i : x => hQ i.val L hL (fun k => (f k).val i) (fun _ _ h => hf h i)
  refine ⟨⟨q, ?_⟩, hq⟩
  intro i j hij
  choose hd he using fun k : L => (f k).property i j hij
  let σ := π hij
  let g (k : L) : σ.dom := ⟨(f k).val j, hd k⟩
  have hg : Antitone g := fun _ _ h => hf h j
  have hj := σ.closed L hL g hg (q j) (hq j)
  refine ⟨hj, ?_⟩
  have h := σ.continuous L hL g hg ⟨q j, hj⟩ (hq j)
  have heq : (fun k => σ.proj (g k)) = (fun k => (f k).val i) := funext he
  rw [heq] at h
  exact h.unique (hq i)

theorem thread_shortInfima (x : Set I) : ShortInfima κ (Thread Q π x) := by
  intro L _ _ hL f hf
  obtain ⟨t, ht⟩ := exists_coordinate_glb Q π hQ L hL f hf
  exact ⟨t, thread_glb_of_coordinates Q π f t ht⟩

theorem thread_glb_coordinates {x : Set I} (L : Type u) [LinearOrder L] [WellFoundedLT L]
    (hL : Cardinal.mk L < κ) (f : L → Thread Q π x) (hf : Antitone f)
    (t : Thread Q π x) (ht : IsGLB (Set.range f) t) (i : x) :
    IsGLB (Set.range (fun k => (f k).val i)) (t.val i) := by
  obtain ⟨s, hs⟩ := exists_coordinate_glb Q π hQ L hL f hf
  rw [ht.unique (thread_glb_of_coordinates Q π f s hs)]
  exact hs i

omit hQ

def restrictThread {x y : Set I} (hyx : y ⊆ x) : Thread Q π x →o Thread Q π y where
  toFun t := ⟨fun i => t.val ⟨i.val,hyx i.property⟩,fun i j h =>
    t.property ⟨i.val,hyx i.property⟩ ⟨j.val,hyx j.property⟩ h⟩
  monotone' _ _ h i := h ⟨i.val,hyx i.property⟩

theorem restrictThread_apply {x y : Set I} (hyx : y ⊆ x) (t : Thread Q π x) (i : y) :
    (restrictThread Q π hyx t).val i = t.val ⟨i.val,hyx i.property⟩ := rfl

theorem restrictThread_comp {x y z : Set I} (hzy : z ⊆ y) (hyx : y ⊆ x) (t : Thread Q π x) :
    restrictThread Q π hzy (restrictThread Q π hyx t) = restrictThread Q π (hzy.trans hyx) t := rfl

include hQ in
theorem restrictThread_continuous {x y : Set I} (hyx : y ⊆ x) (L : Type u)
    [LinearOrder L] [WellFoundedLT L] (hL : Cardinal.mk L < κ)
    (f : L → Thread Q π x) (hf : Antitone f) (t : Thread Q π x) (ht : IsGLB (Set.range f) t) :
    IsGLB (Set.range (fun k => restrictThread Q π hyx (f k))) (restrictThread Q π hyx t) :=
  thread_glb_of_coordinates Q π _ _ (fun i =>
    thread_glb_coordinates Q π hQ L hL f hf t ht ⟨i.val, hyx i.property⟩)

end Paths
end Erdos1172Shioya.InverseSystem
