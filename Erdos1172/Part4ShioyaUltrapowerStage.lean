/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BoundedUltrapowerSequenceClosure
public import Erdos1172.Part4ClosedPartialProjection

@[expose] public section

/-! # Bounded ultrapowers of stage posets

On every bounded interval of the fine seed, the fibers have size below the
critical cardinal. Normality transfers the comparisons of an external short
chain to simultaneous comparisons on these fibers. Thus their pointwise
infima form a bounded target point.
-/

set_option autoImplicit false
noncomputable section
open Filter Erdos1172GroundUltrapower
universe u
namespace Erdos1172Shioya.UltrapowerStage

variable {I : Type u} (U : Ultrafilter I) {κ θ : Cardinal.{u}} (a : I → Set θ.ord.ToType)

abbrev Point (P : Type u) := {x : Germ (U : Filter I) P //
  ∃ η : θ.ord.ToType, ∃ f : Set θ.ord.ToType → P,
    Germ.ofFun (fun i => f (boundedFiber θ a η i)) = x}

def represent {P : Type u} (η : θ.ord.ToType) (f : Set θ.ord.ToType → P) : Point U a P :=
  ⟨_,η,f,rfl⟩

def diagonal [Nonempty θ.ord.ToType] {P : Type u} [PartialOrder P] : P ↪o Point U a P where
  toFun x := represent U a (Classical.choice inferInstance) (fun _ => x)
  inj' _ _ h := Germ.const_inj.mp (congrArg Subtype.val h)
  map_rel_iff' := Germ.const_le_iff

def map {P Q : Type u} (f : P → Q) (p : Point U a P) : Point U a Q := by
  refine ⟨Germ.map f p.val, ?_⟩
  obtain ⟨η,g,hg⟩ := p.property
  exact ⟨η,f ∘ g,congrArg (Germ.map f) hg⟩

@[simp] theorem map_id {P : Type u} (p : Point U a P) : map U a id p = p := by
  apply Subtype.ext
  exact congrFun Germ.map_id p.val

theorem map_mono {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q} (h : Monotone f) :
    Monotone (map U a f) := by
  intro p q hpq
  obtain ⟨η,g,hg⟩ := p.property
  obtain ⟨ν,k,hk⟩ := q.property
  change Germ.map f p.val ≤ Germ.map f q.val
  change p.val ≤ q.val at hpq
  rw [← hg, ← hk] at hpq ⊢
  exact (Germ.coe_le.mp hpq).mono fun _ hi => h hi

private theorem normal_all {J : Type u} (s : I → Set J) (hn : NormalOn U s)
    (R : I → J → Prop) (h : ∀ j, ∀ᶠ i in U, R i j) :
    ∀ᶠ i in U, ∀ j ∈ s i, R i j := by
  classical
  by_contra hbad
  have bad := U.eventually_not.mpr hbad
  simp only [not_forall] at bad
  obtain ⟨i₀,j₀,_⟩ := bad.exists
  let f i := if hi : ∃ j, j ∈ s i ∧ ¬R i j then hi.choose else j₀
  have hb : ∀ᶠ i in U, f i ∈ s i ∧ ¬R i (f i) := bad.mono fun i hi => by
    have h' : ∃ j, j ∈ s i ∧ ¬R i j := by simpa using hi
    simpa only [f,dif_pos h'] using h'.choose_spec
  obtain ⟨j,hj⟩ := hn f (hb.mono fun _ hi => hi.1)
  exact (U.eventually_not.mp ((hj.and hb).mono fun _ hi => hi.1 ▸ hi.2.2)) (h j)

private theorem small_fiber (hf : FineOn U a) (ht : FiberOrderType U κ θ a) (ν : θ.ord.ToType) :
    ∀ᶠ i in U, Cardinal.mk (boundedFiber θ a ν i) < κ := by
  filter_upwards [hf ν,ht] with i hi he
  let e := Classical.choice he
  let t := e.symm ⟨ν,hi⟩
  let f (x : boundedFiber θ a ν i) : Set.Iio t :=
    ⟨e.symm ⟨x.val,x.property.1⟩,e.symm.strictMono x.property.2⟩
  have inj : Function.Injective f := fun x y h =>
    Subtype.ext (congrArg (fun p : a i => p.val) (e.symm.injective (congrArg Subtype.val h)))
  have hlt := Cardinal.mk_Iio_lt t (show Cardinal.ord (Cardinal.mk κ.ord.ToType) =
    Ordinal.type (α := κ.ord.ToType) (· < ·) by simp)
  exact (Cardinal.mk_le_of_injective inj).trans_lt (by simpa using hlt)

structure Chart {L P : Type u} (f : L → Point U a P) where
  bound : θ.ord.ToType
  slice : Set θ.ord.ToType → Set L
  val : Set θ.ord.ToType → L → P
  rep : ∀ j, Germ.ofFun (fun i => val (boundedFiber θ a bound i) j) = (f j).val
  fine : FineOn U (fun i => slice (boundedFiber θ a bound i))
  normal : NormalOn U (fun i => slice (boundedFiber θ a bound i))
  small : ∀ᶠ i in U, Cardinal.mk (slice (boundedFiber θ a bound i)) < κ

private theorem exists_chart (hθ : θ.IsRegular) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) {L P : Type u} (hL : Cardinal.mk L < θ) (f : L → Point U a P) :
    Nonempty (Chart U (κ := κ) a f) := by
  classical
  choose η g hg using fun j => (f j).property
  obtain ⟨e⟩ : Nonempty (L ↪ θ.ord.ToType) :=
    (Cardinal.le_def _ _).mp (by simpa using hL.le)
  let b (j : L) := max (η j) (e j)
  let β := ⨆ j, (b j).toOrd.val + 1
  have hβ : β < θ.ord := Ordinal.iSup_add_one_lt_of_lt_cof (by rwa [hθ.cof_ord])
    (fun j => (b j).toOrd.property)
  let ν := Ordinal.ToType.mk (⟨β,hβ⟩ : Set.Iio θ.ord)
  have hv (j : L) : b j < ν := by
    apply Ordinal.ToType.mk.symm.lt_iff_lt.mp
    change (b j).toOrd.val < ν.toOrd.val
    rw [show ν.toOrd.val = β from congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply ⟨β,hβ⟩)]
    exact Ordinal.lt_iSup_add_one _ j
  refine ⟨⟨ν,fun S => e ⁻¹' S,fun S j => g j (S ∩ Set.Iio (η j)),?_,?_,?_,?_⟩⟩
  · intro j
    simpa only [boundedFiber_restrict θ a ((le_max_left (η j) (e j)).trans (hv j).le)] using hg j
  · exact fun j => (hf (e j)).mono fun _ hi => ⟨hi,(le_max_right (η j) (e j)).trans_lt (hv j)⟩
  · intro w hw
    obtain ⟨ξ,hξ⟩ := hn (fun i => e (w i)) (hw.mono fun _ hi => hi.1)
    obtain ⟨i,hi⟩ := hξ.exists
    exact ⟨w i,hξ.mono fun _ he => e.injective (he.trans hi.symm)⟩
  · exact (small_fiber U a hf ht ν).mono fun i hi => (Cardinal.mk_le_of_injective
      (f := fun j : e ⁻¹' boundedFiber θ a ν i => (⟨e j.val,j.property⟩ : boundedFiber θ a ν i))
      (fun j k h => Subtype.ext (e.injective (congrArg Subtype.val h)))).trans_lt hi

/-- Any external family of fewer than θ bounded points is exactly the membership
trace of a bounded point represented by sets of size below κ. -/
theorem exists_short_set (hκ : 0 < κ) (hθ : θ.IsRegular) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) {L V : Type u} (hL : Cardinal.mk L < θ) (f : L → Point U a V) :
    ∃ s : Point U a {S : Set V // Cardinal.mk S < κ}, ∀ w : Point U a V,
      Germ.LiftRel (fun x (S : {S : Set V // Cardinal.mk S < κ}) => x ∈ S.val) w.val s.val ↔
        ∃ j, f j = w := by
  classical
  let c := Classical.choice (exists_chart U a hθ hf hn ht hL f)
  let S t := c.val t '' c.slice t
  let collect (t : Set θ.ord.ToType) : {s : Set V // Cardinal.mk s < κ} :=
    if h : Cardinal.mk (S t) < κ then ⟨S t,h⟩ else ⟨∅,by simpa using hκ⟩
  let t i := boundedFiber θ a c.bound i
  have exactSlice : ∀ᶠ i in U, (collect (t i)).val = S (t i) :=
    c.small.mono fun i hi => by
      have hs : Cardinal.mk (S (t i)) < κ := Cardinal.mk_image_le.trans_lt hi
      simp only [collect,dif_pos hs]
  refine ⟨represent U a c.bound collect,fun w => ?_⟩
  obtain ⟨ν,g,hg⟩ := w.property
  let v i := g (boundedFiber θ a ν i)
  rw [← hg]
  change (∀ᶠ i in U, v i ∈ (collect (t i)).val) ↔ _
  constructor
  · intro hw
    have H : ∀ᶠ i in U, ∃ j ∈ c.slice (t i), c.val (t i) j = v i :=
      (hw.and exactSlice).mono fun i hi => by
        have hm := hi.1
        rw [hi.2] at hm
        exact hm
    obtain ⟨_,j₀,_⟩ := H.exists
    let pick i := if h : ∃ j ∈ c.slice (t i), c.val (t i) j = v i then h.choose else j₀
    have hp : ∀ᶠ i in U, pick i ∈ c.slice (t i) ∧ c.val (t i) (pick i) = v i :=
      H.mono fun i hi => by simpa only [pick,dif_pos hi] using hi.choose_spec
    obtain ⟨j,hj⟩ := c.normal pick (hp.mono fun _ => And.left)
    refine ⟨j,Subtype.ext ((c.rep j).symm.trans ((Germ.coe_eq.mpr ?_).trans hg))⟩
    exact (hp.and hj).mono fun _ hi => hi.2 ▸ hi.1.2
  · rintro ⟨j,hj⟩
    have eqv : (fun i => c.val (t i) j) =ᶠ[U] v := Germ.coe_eq.mp
      ((c.rep j).trans ((congrArg Subtype.val hj).trans hg.symm))
    filter_upwards [eqv,c.fine j,exactSlice] with i he hj hs
    exact hs ▸ ⟨j,hj,he⟩

variable {L P Q : Type u} [PartialOrder P] [PartialOrder Q]

private theorem Chart.antitone [LinearOrder L] {f : L → Point U a P}
    (c : Chart U (κ := κ) a f) (h : Antitone f) :
    ∀ᶠ i in U, Antitone (fun j : c.slice (boundedFiber θ a c.bound i) =>
      c.val (boundedFiber θ a c.bound i) j.val) := by
  let s i := boundedFiber θ a c.bound i
  have pairs (j k : L) : ∀ᶠ i in U, j ≤ k → c.val (s i) k ≤ c.val (s i) j := by
    by_cases hjk : j ≤ k
    · have he : (f k).val ≤ (f j).val := h hjk
      rw [← c.rep, ← c.rep] at he
      exact (Germ.coe_le.mp he).mono fun _ hi _ => hi
    · exact Eventually.of_forall fun _ hi => (hjk hi).elim
  have h₁ j := normal_all U _ c.normal _ (pairs j)
  have h₂ := normal_all U _ c.normal _ h₁
  exact h₂.mono fun _ hi j k hjk => hi j.val j.property k.val k.property hjk

omit [PartialOrder P] in
private theorem Chart.glb {f : L → Point U a P} (c : Chart U (κ := κ) a f)
    (m : P → Q) (g : Set θ.ord.ToType → Q)
    (hg : ∀ᶠ i in U, IsGLB (Set.range (fun j : c.slice (boundedFiber θ a c.bound i) =>
      m (c.val (boundedFiber θ a c.bound i) j.val))) (g (boundedFiber θ a c.bound i))) :
    IsGLB (Set.range (fun j => map U a m (f j))) (represent U a c.bound g) := by
  let s i := boundedFiber θ a c.bound i
  constructor
  · rintro _ ⟨j,rfl⟩
    change Germ.ofFun (fun i => g (s i)) ≤ Germ.map m (f j).val
    rw [← c.rep]
    exact ((c.fine j).and hg).mono fun i hi => hi.2.1
      (Set.mem_range_self (⟨j,hi.1⟩ : c.slice (s i)))
  · intro z hz
    obtain ⟨ν,w,hw⟩ := z.property
    let v i := w (boundedFiber θ a ν i)
    have hb (j : L) : ∀ᶠ i in U, v i ≤ m (c.val (s i) j) := by
      have he : z.val ≤ Germ.map m (f j).val := hz (Set.mem_range_self j)
      rw [← hw, ← c.rep] at he
      exact he
    change z.val ≤ Germ.ofFun (fun i => g (s i))
    rw [← hw]
    exact ((normal_all U _ c.normal _ hb).and hg).mono fun _ hi =>
      hi.2.2 (Set.forall_mem_range.mpr fun j => hi.1 j.val j.property)

private theorem chart_infima [LinearOrder L] [WellFoundedLT L] (hP : ShortInfima κ P)
    {f : L → Point U a P} (c : Chart U (κ := κ) a f) (h : Antitone f) :
    ∃ g : Set θ.ord.ToType → P, ∀ᶠ i in U,
      IsGLB (Set.range (fun j : c.slice (boundedFiber θ a c.bound i) =>
        c.val (boundedFiber θ a c.bound i) j.val)) (g (boundedFiber θ a c.bound i)) := by
  classical
  let s i := boundedFiber θ a c.bound i
  let good (S : Set θ.ord.ToType) (p : P) := IsGLB (Set.range (fun j : c.slice S => c.val S j.val)) p
  have he : ∀ᶠ i in U, ∃ p, good (s i) p := (c.small.and (c.antitone U a h)).mono fun i hi =>
    hP _ hi.1 _ hi.2
  obtain ⟨_,p,_⟩ := he.exists
  let g S := if hg : ∃ x, good S x then hg.choose else p
  refine ⟨g,he.mono fun i hi => ?_⟩
  change good (s i) (g (s i))
  simpa only [g,dif_pos hi] using hi.choose_spec

/-- Bounded-support target stages admit infima of externally indexed
descending sequences of every cardinality below the target cardinal. -/
theorem shortInfima (hθ : θ.IsRegular) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hP : ShortInfima κ P) : ShortInfima θ (Point U a P) := by
  intro L _ _ hL f h
  let c := Classical.choice (exists_chart U a hθ hf hn ht hL f)
  obtain ⟨g,hg⟩ := chart_infima U a hP c h
  exact ⟨represent U a c.bound g,by simpa only [map_id] using c.glb U a id g hg⟩

/-- Pointwise transport preserves the newly obtained target infima provided
the original point map preserves infima of short chains. -/
theorem map_preserves_shortInfima (hθ : θ.IsRegular) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hP : ShortInfima κ P) (m : P → Q)
    (hm : ∀ (L : Type u) [LinearOrder L] [WellFoundedLT L], Cardinal.mk L < κ →
      ∀ (f : L → P), Antitone f → ∀ p, IsGLB (Set.range f) p → IsGLB (Set.range (m ∘ f)) (m p))
    (L : Type u) [LinearOrder L] [WellFoundedLT L] (hL : Cardinal.mk L < θ)
    (f : L → Point U a P) (h : Antitone f) (p : Point U a P) (hp : IsGLB (Set.range f) p) :
    IsGLB (Set.range (fun j => map U a m (f j))) (map U a m p) := by
  let c := Classical.choice (exists_chart U a hθ hf hn ht hL f)
  obtain ⟨g,hg⟩ := chart_infima U a hP c h
  have he : p = represent U a c.bound g := hp.unique (by simpa only [map_id] using c.glb U a id g hg)
  rw [he]
  exact c.glb U a m (m ∘ g) ((c.small.and ((c.antitone U a h).and hg)).mono
    fun _ hi => hm _ hi.1 _ hi.2.1 _ hi.2.2)

end Erdos1172Shioya.UltrapowerStage
