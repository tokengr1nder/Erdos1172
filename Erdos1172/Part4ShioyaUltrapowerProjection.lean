/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaUltrapowerStage
public import Erdos1172.Part4ShioyaProjectedPath
public import Erdos1172.Part4ShioyaRecoveredMasterThread

@[expose] public section

/-! # Lifting stage projections through the bounded ultrapower -/

set_option autoImplicit false
noncomputable section
open Filter Erdos1172GroundUltrapower
universe u
namespace Erdos1172Shioya.UltrapowerStage

variable {I : Type u} (U : Ultrafilter I) {κ θ : Cardinal.{u}} (a : I → Set θ.ord.ToType)
variable {P Q R : Type u} [PartialOrder P] [PartialOrder Q]

def repr {V : Type u} (z : Point U a V) : I → V := fun i =>
  z.property.choose_spec.choose (boundedFiber θ a z.property.choose i)

theorem repr_eq {V : Type u} (z : Point U a V) :
    Germ.ofFun (repr U a z) = z.val := z.property.choose_spec.choose_spec

theorem le_iff (p q : Point U a P) : p ≤ q ↔ ∀ᶠ i in U, repr U a p i ≤ repr U a q i := by
  change p.val ≤ q.val ↔ _
  rw [← repr_eq U a p,← repr_eq U a q]
  rfl

theorem map_repr {V W : Type u} (f : V → W) (p : Point U a V) :
    repr U a (map U a f p) =ᶠ[U] fun i => f (repr U a p i) := by
  apply Germ.coe_eq.mp
  exact (repr_eq U a _).trans (congrArg (Germ.map f) (repr_eq U a p)).symm

theorem choose_pair {V W Y : Type u} (p : Point U a V) (q : Point U a W)
    (T : V → W → Y → Prop) (h : ∀ᶠ i in U, ∃ y, T (repr U a p i) (repr U a q i) y) :
    ∃ z : Point U a Y, ∀ᶠ i in U, T (repr U a p i) (repr U a q i) (repr U a z i) := by
  classical
  obtain ⟨_,y₀,_⟩ := h.exists
  let pick (v : V) (w : W) := if hi : ∃ y, T v w y then hi.choose else y₀
  let η := p.property.choose
  let ν := q.property.choose
  let f := p.property.choose_spec.choose
  let g := q.property.choose_spec.choose
  let z := represent U a (max η ν) (fun S => pick (f (S ∩ Set.Iio η)) (g (S ∩ Set.Iio ν)))
  have he : repr U a z =ᶠ[U] fun i => pick (repr U a p i) (repr U a q i) := by
    apply Germ.coe_eq.mp
    refine (repr_eq U a z).trans ?_
    change Germ.ofFun (fun i => pick (f _) (g _)) = _
    simp only [boundedFiber_restrict θ a (le_max_left η ν),boundedFiber_restrict θ a (le_max_right η ν)]
    rfl
  exact ⟨z,(he.and h).mono fun i hi => by rw [hi.1]; simpa only [pick,dif_pos hi.2] using hi.2.choose_spec⟩

variable (π : PartialProjection κ P Q)

theorem separative (hs : Separative P) : Separative (Point U a P) := by
  intro p q hpq
  have h := U.eventually_not.mpr (fun h => hpq ((le_iff U a _ _).mpr h))
  obtain ⟨r,hr⟩ := choose_pair U a p q (fun v w y => y ≤ v ∧ ¬ ∃ t, t ≤ y ∧ t ≤ w)
    (h.mono fun _ hi => hs _ _ hi)
  refine ⟨r,(le_iff U a _ _).mpr (hr.mono fun _ hi => hi.1),?_⟩
  rintro ⟨t,hl,hm⟩
  obtain ⟨i,hi,h₁,h₂⟩ := (hr.and (((le_iff U a _ _).mp hl).and ((le_iff U a _ _).mp hm))).exists
  exact hi.2 ⟨repr U a t i,h₁,h₂⟩

private theorem eq_iff_repr {V : Type u} (p q : Point U a V) :
    p = q ↔ repr U a p =ᶠ[U] repr U a q := by
  rw [← Germ.coe_eq, repr_eq, repr_eq, Subtype.ext_iff]

theorem relation_iff {V W : Type u} (R : V → W → Prop) (p : Point U a V) (q : Point U a W) :
    Germ.LiftRel R p.val q.val ↔ ∃ z : Point U a {t : V × W // R t.1 t.2},
      map U a (fun t => t.val.1) z = p ∧ map U a (fun t => t.val.2) z = q := by
  rw [← repr_eq U a p,← repr_eq U a q,Germ.liftRel_coe]
  constructor
  · intro h
    let A := {t : V × W // R t.1 t.2}
    obtain ⟨z,hz⟩ := choose_pair U a p q (fun v w (t : A) => t.val.1 = v ∧ t.val.2 = w)
      (h.mono fun i hi => ⟨⟨(repr U a p i,repr U a q i),hi⟩,rfl,rfl⟩)
    exact ⟨z,(eq_iff_repr U a _ _).mpr ((map_repr U a _ z).trans (hz.mono fun _ hi => hi.1)),
      (eq_iff_repr U a _ _).mpr ((map_repr U a _ z).trans (hz.mono fun _ hi => hi.2))⟩
  · rintro ⟨z,rfl,rfl⟩
    filter_upwards [map_repr U a (fun t : {t : V × W // R t.1 t.2} => t.val.1) z,
      map_repr U a (fun t : {t : V × W // R t.1 t.2} => t.val.2) z] with i hi hj
    exact hi.symm ▸ hj.symm ▸ (repr U a z i).property

def incl : Point U a π.dom ↪o Point U a P where
  toFun := map U a Subtype.val
  inj' := by
    intro p q he
    apply Subtype.ext
    rw [← repr_eq U a p,← repr_eq U a q]
    apply Germ.coe_eq.mpr
    have he' := congrArg (repr U a) he
    have ha := map_repr U a (fun z : π.dom => z.val) p
    have hb := map_repr U a (fun z : π.dom => z.val) q
    rw [he'] at ha
    exact (ha.symm.trans hb).mono fun _ hi => Subtype.ext hi
  map_rel_iff' := by
    intro p q
    rw [le_iff,le_iff]
    apply eventually_congr
    filter_upwards [map_repr U a (fun z : π.dom => z.val) p,map_repr U a (fun z : π.dom => z.val) q]
      with i hi hj
    change repr U a (map U a Subtype.val p) i ≤ repr U a (map U a Subtype.val q) i ↔ _
    exact congrArg₂ (· ≤ ·) hi hj |> Iff.of_eq

def domainIso : Point U a π.dom ≃o Set.range (incl U a π) := (incl U a π).orderIso

theorem embed_dense (p : Point U a P) : ∃ z : Point U a π.dom, incl U a π z ≤ p := by
  let f x := (π.dense x).choose
  refine ⟨map U a f p,(le_iff U a _ _).mpr ?_⟩
  exact ((map_repr U a (fun z : π.dom => z.val) (map U a f p)).and
    (map_repr U a f p)).mono fun i hi => by
      change repr U a (map U a Subtype.val (map U a f p)) i ≤ _
      exact (hi.1.trans (congrArg Subtype.val hi.2)).trans_le (π.dense _).choose_spec

theorem embed_reaches (q : Point U a Q) : ∃ z : Point U a π.dom, map U a π.proj z ≤ q := by
  let f x := (π.reaches x).choose
  refine ⟨map U a f q,(le_iff U a _ _).mpr ?_⟩
  exact ((map_repr U a π.proj (map U a f q)).and (map_repr U a f q)).mono fun i hi => by
    exact (hi.1.trans (congrArg π.proj hi.2)).trans_le (π.reaches _).choose_spec

theorem embed_lifts (p : Point U a π.dom) (q : Point U a Q) (h : q ≤ map U a π.proj p) :
    ∃ z : Point U a π.dom, z ≤ p ∧ map U a π.proj z ≤ q := by
  have hw := ((le_iff U a _ _).mp h).and (map_repr U a π.proj p)
  obtain ⟨z,hz⟩ := choose_pair U a p q (fun x y t => t ≤ x ∧ π.proj t ≤ y)
    (hw.mono fun _ hi => π.lifts _ _ (hi.1.trans_eq hi.2))
  refine ⟨z,(le_iff U a _ _).mpr (hz.mono fun _ hi => hi.1),(le_iff U a _ _).mpr ?_⟩
  exact ((map_repr U a π.proj z).and hz).mono fun _ hi => hi.1.trans_le hi.2.2

def projection (hθ : θ.IsRegular) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hP : ShortInfima κ P) :
    PartialProjection θ (Point U a P) (Point U a Q) := by
  let e := domainIso U a π
  let project : Point U a π.dom →o Point U a Q := ⟨map U a π.proj,map_mono U a π.proj.monotone⟩
  let closedDom := π.domShortInfima hP
  have keep := map_preserves_shortInfima U a hθ hf hn ht closedDom (fun z : π.dom => z.val)
    (fun _ _ _ hL f h x hx => π.val_isGLB hP hL f h x hx)
  have send := map_preserves_shortInfima U a hθ hf hn ht closedDom π.proj
    (fun _ _ _ hL f h x hx => π.proj_isGLB hP hL f h x hx)
  refine ⟨Set.range (incl U a π),?_,⟨fun z => project (e.symm z),project.monotone.comp e.symm.monotone⟩,
    ?_,?_,?_,?_⟩
  · intro p
    obtain ⟨z,hz⟩ := embed_dense U a π p
    exact ⟨e z,hz⟩
  · intro q
    obtain ⟨z,hz⟩ := embed_reaches U a π q
    exact ⟨e z,by change project (e.symm (e z)) ≤ q; rwa [e.symm_apply_apply]⟩
  · intro p q h
    obtain ⟨t,ht₁,ht₂⟩ := embed_lifts U a π (e.symm p) q h
    exact ⟨e t,(e.monotone ht₁).trans_eq (e.apply_symm_apply p),
      by change project (e.symm (e t)) ≤ q; rwa [e.symm_apply_apply]⟩
  · intro L _ _ hL f h p hp
    let w j := e.symm (f j)
    have hw : Antitone w := e.symm.monotone.comp_antitone h
    obtain ⟨z,hz⟩ := shortInfima U a hθ hf hn ht closedDom L hL w hw
    have hi := keep L hL w hw z hz
    have eq (j : L) : map U a Subtype.val (w j) = (f j).val := congrArg Subtype.val (e.apply_symm_apply (f j))
    simp only [eq] at hi
    exact ⟨z,hi.unique hp⟩
  · intro L _ _ hL f h p hp
    let w j := e.symm (f j)
    have hw : Antitone w := e.symm.monotone.comp_antitone h
    obtain ⟨z,hz⟩ := shortInfima U a hθ hf hn ht closedDom L hL w hw
    have hi := keep L hL w hw z hz
    have eq (j : L) : map U a Subtype.val (w j) = (f j).val := congrArg Subtype.val (e.apply_symm_apply (f j))
    simp only [eq] at hi
    have he : e z = p := Subtype.ext (hi.unique hp)
    have hz' : z = e.symm p := by rw [← he,e.symm_apply_apply]
    exact send L hL w hw _ (hz' ▸ hz)

theorem projection_diagonal [Nonempty θ.ord.ToType] (hθ : θ.IsRegular) (hf : FineOn U a)
    (hn : NormalOn U a) (ht : FiberOrderType U κ θ a) (hP : ShortInfima κ P) (x : π.dom) :
    ∃ hd : diagonal U a x.val ∈ (projection U a π hθ hf hn ht hP).dom,
      (projection U a π hθ hf hn ht hP).proj ⟨diagonal U a x.val,hd⟩ = diagonal U a (π.proj x) := by
  let z := diagonal U a x
  let e := domainIso U a π
  have hv : incl U a π z = diagonal U a x.val := rfl
  refine ⟨⟨z,hv⟩,?_⟩
  change map U a π.proj (e.symm (e z)) = _
  rw [e.symm_apply_apply]
  rfl

theorem projection_graph (hθ : θ.IsRegular) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hP : ShortInfima κ P) (p : Point U a P) (q : Point U a Q) :
    (∃ hd : p ∈ (projection U a π hθ hf hn ht hP).dom, (projection U a π hθ hf hn ht hP).proj ⟨p,hd⟩ = q) ↔
      ∃ z : Point U a π.dom, map U a Subtype.val z = p ∧ map U a π.proj z = q := by
  let e := domainIso U a π
  constructor
  · rintro ⟨hd,hq⟩
    let v : Set.range (incl U a π) := ⟨p,hd⟩
    exact ⟨e.symm v,congrArg Subtype.val (e.apply_symm_apply v),hq⟩
  · rintro ⟨z,rfl,rfl⟩
    refine ⟨⟨z,rfl⟩,?_⟩
    change map U a π.proj (e.symm (e z)) = _
    rw [e.symm_apply_apply]

/-- The master thread for a recovered diagram has concrete bounded
ultrapower stages, projections and point maps. -/
theorem recovered_thread [Nonempty θ.ord.ToType] [Fact (Cardinal.aleph0 < κ)]
    {J : Type u} [Preorder J] (D : Uniformization.Diagram κ θ J)
    (F : Order.PFilter (Algebra κ θ)) (hθ : θ.IsRegular) (hunc : Cardinal.aleph0 < θ)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    (proper : ⊥ ∉ F) (meets : ∀ S, RecoveredMaster.edgeTests D S → ∃ b ∈ S, b ∈ F)
    (coding : ∀ i, (D.stage i).CodesDense)
    (req : ∀ p ∈ D.requirements, Erdos1172PosetCompletion.condition p ∈ F)
    (count : ∀ i, (RecoveredMaster.realized D F i).Countable) (s : Set J) :
    ∃ m : InverseSystem.Thread (fun i => Point U a (D.poset i))
        (fun {i j} (h : i < j) => projection U a (D.projection h) hθ hf hn ht (D.stage j).complete) s,
      (∀ i, IsGLB (diagonal U a '' RecoveredMaster.realized D F i.val) (m.val i)) ∧
      ∀ (i j : s) (h : i < j), m.val j ≤ diagonal U a (D.edge h).source :=
  RecoveredMaster.exists_lifted_thread coding (RecoveredMaster.readsEdges_of_meets D F proper meets)
    req hunc _ (fun i => shortInfima U a hθ hf hn ht (D.stage i).complete) _
    (fun i => (diagonal U a (P := D.poset i)).toOrderHom)
    (fun h x => projection_diagonal U a (D.projection h) hθ hf hn ht _ x) count s

end Erdos1172Shioya.UltrapowerStage
