/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaUltrapowerMasterDecisions
public import Erdos1172.Part4ShioyaUniformizationRestriction

@[expose] public section

/-! # Simultaneous lifting on externally short marked systems in a bounded ultrapower -/

set_option autoImplicit false
noncomputable section
open Filter Erdos1172GroundUltrapower
universe u
namespace Erdos1172Shioya.UltrapowerStage
variable {I : Type u} (U : Ultrafilter I) {κ θ : Cardinal.{u}} (a : I → Set θ.ord.ToType)

/-- A single bounded point evaluates at every entry of an externally short
dependent sequence of bounded ultrapower points. -/
theorem collect_dependent (hθ : θ.IsRegular) {J : Type u} (hJ : Cardinal.mk J < θ)
    {V : J → Type u} (f : ∀ j, Point U a (V j)) :
    ∃ p : Point U a ((j : J) → V j), ∀ j, map U a (fun v => v j) p = f j := by
  classical
  choose η g hg using fun j => (f j).property
  let β := ⨆ j, (η j).toOrd.val + 1
  have hβ : β < θ.ord := Ordinal.iSup_add_one_lt_of_lt_cof (by rwa [hθ.cof_ord])
    (fun j => (η j).toOrd.property)
  let ν := Ordinal.ToType.mk (⟨β,hβ⟩ : Set.Iio θ.ord)
  have bound (j : J) : η j < ν := by
    apply Ordinal.ToType.mk.symm.lt_iff_lt.mp
    change (η j).toOrd.val < ν.toOrd.val
    rw [show ν.toOrd.val = β from congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply ⟨β,hβ⟩)]
    exact Ordinal.lt_iSup_add_one _ j
  refine ⟨represent U a ν (fun S j => g j (S ∩ Set.Iio (η j))),?_⟩
  intro j
  apply Subtype.ext
  change Germ.ofFun (fun i => g j (boundedFiber θ a ν i ∩ Set.Iio (η j))) = _
  simpa only [boundedFiber_restrict θ a (bound j).le] using hg j

private theorem repr_inj {V : Type u} {p q : Point U a V}
    (h : repr U a p =ᶠ[U] repr U a q) : p = q :=
  Subtype.ext (((repr_eq U a p).symm.trans (Germ.coe_eq.mpr h)).trans (repr_eq U a q))

variable [Nonempty θ.ord.ToType]

/-- The external initial segment has an internally short set whose bounded
members are exactly the marked ordinals through γ. -/
theorem initial_segment_marked (hκ : 0 < κ) (hθ : θ.IsRegular)
    (fine : FineOn U a) (normal : NormalOn U a) (ht : FiberOrderType U κ θ a)
    (γ : θ.ord.ToType) :
    ∃ s : Point U a {S : Set θ.ord.ToType // Cardinal.mk S < κ}, ∀ w : Point U a θ.ord.ToType,
      Germ.LiftRel (fun x (S : {S : Set θ.ord.ToType // Cardinal.mk S < κ}) => x ∈ S.val) w.val s.val ↔
        ∃ j ≤ γ, diagonal U a j = w := by
  have hseg : Cardinal.mk (Set.Iic γ) < θ := by
    simpa using Cardinal.mk_Iic_lt γ (by simp) (by simpa using hθ.aleph0_le)
  obtain ⟨s,hs⟩ := exists_short_set U a hκ hθ fine normal ht hseg (fun j : Set.Iic γ => diagonal U a j.val)
  exact ⟨s,fun w => (hs w).trans ⟨fun ⟨j,hj⟩ => ⟨j.val,j.property,hj⟩,fun ⟨j,hj,he⟩ => ⟨⟨j,hj⟩,he⟩⟩⟩

/-- The marked set is represented by sets of size below κ. Every bounded
member is a diagonal element, so bounded parameters satisfy uniform two-index
tests throughout the marked fibers. -/
theorem marked_test (hκ : 0 < κ) (hθ : θ.IsRegular) (fine : FineOn U a) (normal : NormalOn U a)
    (ht : FiberOrderType U κ θ a) {J : Type u} [PartialOrder J] (hJ : Cardinal.mk J < θ) :
    ∃ s : Point U a {S : Set J // Cardinal.mk S < κ},
      (∀ j, ∀ᶠ i in U, j ∈ (repr U a s i).val) ∧
      (∀ w : Point U a J, (∀ᶠ i in U, repr U a w i ∈ (repr U a s i).val) ↔
        ∃ j, diagonal U a j = w) ∧
      ∀ {V : Type u} (p : Point U a V) (R : V → J → J → Prop),
        (∀ j k, ∀ᶠ i in U, R (repr U a p i) j k) →
        ∀ᶠ i in U, ∀ j ∈ (repr U a s i).val, ∀ k ∈ (repr U a s i).val, R (repr U a p i) j k := by
  classical
  obtain ⟨s,hs⟩ := exists_short_set U a hκ hθ fine normal ht hJ (fun j : J => diagonal U a j)
  have reads (w : Point U a J) :
      (∀ᶠ i in U, repr U a w i ∈ (repr U a s i).val) ↔ ∃ j, diagonal U a j = w := by
    have h := hs w
    rwa [← repr_eq U a w,← repr_eq U a s,Germ.liftRel_coe] at h
  have const (j : J) : repr U a (diagonal U a j) =ᶠ[U] fun _ => j := Germ.coe_eq.mp (repr_eq U a _)
  refine ⟨s,?_,reads,?_⟩
  · intro j
    filter_upwards [const j,(reads _).mpr ⟨j,rfl⟩] with i he hm
    change repr U a (diagonal U a j) i = j at he
    exact he ▸ hm
  intro V p R hr
  by_contra hn
  have bad := U.eventually_not.mpr hn
  simp only [not_forall] at bad
  obtain ⟨z,hz⟩ := choose_pair U a s p
    (fun S v (t : J × J) => (t.1 ∈ S.val ∧ t.2 ∈ S.val) ∧ ¬R v t.1 t.2)
    (bad.mono (fun _ hi => by obtain ⟨j,hj,k,hk,h⟩ := hi; exact ⟨⟨j,k⟩,⟨hj,hk⟩,h⟩))
  let x := map U a Prod.fst z
  let y := map U a Prod.snd z
  have hx := map_repr U a Prod.fst z
  have hy := map_repr U a Prod.snd z
  obtain ⟨j,hj⟩ := (reads x).mp ((hx.and hz).mono (fun _ hi => hi.1.symm ▸ hi.2.1.1))
  obtain ⟨k,hk⟩ := (reads y).mp ((hy.and hz).mono (fun _ hi => hi.1.symm ▸ hi.2.1.2))
  have jEq : (fun i => (repr U a z i).1) =ᶠ[U] fun _ => j := hx.symm.trans (by change repr U a x =ᶠ[U] _; rw [← hj]; exact const j)
  have kEq : (fun i => (repr U a z i).2) =ᶠ[U] fun _ => k := hy.symm.trans (by change repr U a y =ᶠ[U] _; rw [← hk]; exact const k)
  obtain ⟨i,hi,he,hk',hgood⟩ := (hz.and (jEq.and (kEq.and (hr j k)))).exists
  apply hi.2
  change (repr U a z i).1 = j at he
  change (repr U a z i).2 = k at hk'
  rw [he,hk']
  exact hgood

variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] (π : PartialProjection κ P Q)
variable (hθ : θ.IsRegular) (fine : FineOn U a) (normal : NormalOn U a) (ht : FiberOrderType U κ θ a)
variable (hP : ShortInfima κ P)

omit [Nonempty θ.ord.ToType] in
theorem projection_eq_eventually (p : Point U a P) (q : Point U a Q)
    (h : ∃ hd, (projection U a π hθ fine normal ht hP).proj ⟨p,hd⟩ = q) :
    ∀ᶠ i in U, ∃ hd, π.proj ⟨repr U a p i,hd⟩ = repr U a q i := by
  obtain ⟨z,hz,hq⟩ := (projection_graph U a π hθ fine normal ht hP p q).mp h
  have hp := map_repr U a (fun t : π.dom => t.val) z
  have hv := map_repr U a π.proj z
  rw [hz] at hp
  rw [hq] at hv
  filter_upwards [hp,hv] with i hi hj
  exact hi.symm ▸ ⟨(repr U a z i).property,hj.symm⟩

omit [Nonempty θ.ord.ToType] in
theorem projection_le_of_eventually (p : Point U a P) (q : Point U a Q)
    (h : ∀ᶠ i in U, ∃ hd, π.proj ⟨repr U a p i,hd⟩ ≤ repr U a q i) :
    ∃ hd, (projection U a π hθ fine normal ht hP).proj ⟨p,hd⟩ ≤ q := by
  obtain ⟨z,hz⟩ := choose_pair U a p q (fun v w (t : π.dom) => t.val = v ∧ π.proj t ≤ w)
    (h.mono (fun _ hi => by obtain ⟨hd,hv⟩ := hi; exact ⟨⟨_,hd⟩,rfl,hv⟩))
  have hp : map U a Subtype.val z = p := repr_inj U a ((map_repr U a Subtype.val z).trans
    (hz.mono fun _ hi => hi.1))
  obtain ⟨hd,he⟩ := (projection_graph U a π hθ fine normal ht hP p (map U a π.proj z)).mpr ⟨z,hp,rfl⟩
  refine ⟨hd,he ▸ (le_iff U a _ _).mpr ?_⟩
  exact ((map_repr U a π.proj z).and hz).mono fun _ hi => hi.1.trans_le hi.2.2

section Diagram
variable {J : Type u} [LinearOrder J] [Fact (Cardinal.aleph0 < κ)]
variable (D : Uniformization.Diagram κ θ J)
set_option quotPrecheck false
local notation "T" => fun j => Point U a (D.poset j)
local notation "ρ" => fun {j k : J} (h : j < k) =>
  projection U a (D.projection h) hθ fine normal ht (D.stage k).complete

/-- A compatible master and its source bounds lift any lower thread on an
externally short marked segment. The resulting strengthening belongs to
the actual joint domain of all finite paths on this whole segment. -/
theorem lift_marked_thread (hκθ : κ < θ) (hJ : Cardinal.mk J < θ) (hl : D.localLifts)
    (γ : J) (hγ : ∀ j, j ≤ γ) (m : ∀ j, Point U a (D.poset j))
    (thread : ∀ {j k : J} (h : j < k), ∃ hd, (ρ h).proj ⟨m k,hd⟩ = m j)
    (source : ∀ {j k : J} (h : j < k), m k ≤ diagonal U a (D.edge h).source)
    (r : ∀ j : Set.Iio γ, Point U a (D.poset j.val))
    (compatible : ∀ (j k : Set.Iio γ) (h : j < k), ∃ hd, (ρ h).proj ⟨r k,hd⟩ = r j)
    (below : ∀ j : Set.Iio γ, r j ≤ m j.val) :
    ∃ z ≤ m γ, z ∈ InverseSystem.jointDomain T (fun {_ _} h => ρ h)
      ((Fact.out : Cardinal.aleph0 < κ).trans hκθ)
      (fun j => shortInfima U a hθ fine normal ht (D.stage j).complete) Set.univ ⟨γ,Set.mem_univ _⟩ ∧
      ∀ j : Set.Iio γ, ∃ hd, (ρ j.property).proj ⟨z,hd⟩ ≤ r j := by
  classical
  let w (j : J) := if h : j < γ then r ⟨j,h⟩ else m j
  let V := (j : J) → D.poset j
  obtain ⟨pM,hM⟩ := collect_dependent U a hθ hJ m
  obtain ⟨pR,hR⟩ := collect_dependent U a hθ hJ w
  obtain ⟨p,hp⟩ := choose_pair U a pM pR (fun v w (z : V × V) => z = (v,w))
    (Eventually.of_forall fun _ => ⟨_,rfl⟩)
  let atI := repr U a p
  have mr (j : J) : (fun i => (atI i).1 j) =ᶠ[U] repr U a (m j) := by
    have h := map_repr U a (fun f : V => f j) pM
    rw [hM j] at h
    filter_upwards [hp,h] with i hi he
    change (repr U a p i).1 j = _
    rw [hi]
    exact he.symm
  have rr (j : J) (h : j < γ) : (fun i => (atI i).2 j) =ᶠ[U] repr U a (r ⟨j,h⟩) := by
    have he := map_repr U a (fun f : V => f j) pR
    rw [hR j,show w j = r ⟨j,h⟩ from dif_pos h] at he
    filter_upwards [hp,he] with i hi hv
    change (repr U a p i).2 j = _
    rw [hi]
    exact hv.symm
  obtain ⟨s,hfine,_,hall⟩ := marked_test U a (Cardinal.aleph0_pos.trans (Fact.out : Cardinal.aleph0 < κ))
    hθ fine normal ht hJ
  let edge (v : V) (j k : J) := ∀ h : j < k, ∃ hd, (D.projection h).proj ⟨v k,hd⟩ = v j
  have mEdges := hall p (fun z j k => edge z.1 j k) (by
    intro j k
    by_cases h : j < k
    · have hg := projection_eq_eventually U a (D.projection h) hθ fine normal ht (D.stage k).complete _ _ (thread h)
      filter_upwards [hg,mr j,mr k] with i hi hj hk
      intro _
      change (atI i).1 j = _ at hj
      change (atI i).1 k = _ at hk
      change ∃ hd, (D.projection h).proj ⟨(atI i).1 k,hd⟩ = (atI i).1 j
      rw [hj,hk]
      exact hi
    · exact Eventually.of_forall fun _ h' => (h h').elim)
  have mSources := hall p (fun z j k => ∀ h : j < k, z.1 k ≤ (D.edge h).source) (by
    intro j k
    by_cases h : j < k
    · have diag : repr U a (diagonal U a (D.edge h).source) =ᶠ[U] fun _ => (D.edge h).source :=
        Germ.coe_eq.mp (repr_eq U a _)
      filter_upwards [(le_iff U a _ _).mp (source h),mr k,diag] with i hi hk hd
      intro _
      exact hk.trans_le (hi.trans_eq hd)
    · exact Eventually.of_forall fun _ h' => (h h').elim)
  have rEdges := hall p (fun z j k => k < γ → edge z.2 j k) (by
    intro j k
    by_cases hb : k < γ
    · by_cases h : j < k
      · have hg := projection_eq_eventually U a (D.projection h) hθ fine normal ht (D.stage k).complete _ _
          (compatible ⟨j,h.trans hb⟩ ⟨k,hb⟩ h)
        filter_upwards [hg,rr j (h.trans hb),rr k hb] with i hi hj hk
        intro _ _
        change (atI i).2 j = _ at hj
        change (atI i).2 k = _ at hk
        change ∃ hd, (D.projection h).proj ⟨(atI i).2 k,hd⟩ = (atI i).2 j
        rw [hj,hk]
        exact hi
      · exact Eventually.of_forall fun _ _ h' => (h h').elim
    · exact Eventually.of_forall fun _ h' => (hb h').elim)
  have rBelow := hall p (fun z j _ => j < γ → z.2 j ≤ z.1 j) (by
    intro j k
    by_cases h : j < γ
    · filter_upwards [(le_iff U a _ _).mp (below ⟨j,h⟩),rr j h,mr j] with i hi hj hk
      exact fun _ => hj.trans_le (hi.trans_eq hk.symm)
    · exact Eventually.of_forall fun _ h' => (h h').elim)
  let goal (S : {S : Set J // Cardinal.mk S < κ}) (v : V × V) (z : D.poset γ) :=
    z ≤ v.1 γ ∧ ∀ j ∈ S.val, ∀ h : j < γ, ∃ hd, (D.projection h).proj ⟨z,hd⟩ ≤ v.2 j
  have solve : ∀ᶠ i in U, ∃ z, goal (repr U a s i) (atI i) z := by
    filter_upwards [hfine γ,mEdges,mSources,rEdges,rBelow] with i htop he hs hr hb
    let S := (repr U a s i).val
    let top : S := ⟨γ,htop⟩
    let ma : InverseSystem.Thread D.poset D.projection S :=
      ⟨fun j => (atI i).1 j.val,fun j k h => he j.val j.property k.val k.property h⟩
    have hd := InverseSystem.thread_mem_jointDomain D.poset D.projection
      (Fact.out : Cardinal.aleph0 < κ) (fun j => (D.stage j).complete) ma top
    have guard : D.guard S top (ma.val top) := by
      refine ⟨fun j h => hs j.val j.property γ htop h,?_⟩
      intro j k hj hk _
      obtain ⟨_,eq⟩ := ma.property k top hk
      exact eq.trans_le (hs j.val j.property k.val k.property hj)
    let low : D.lowerThread S top := ⟨fun j => (atI i).2 j.val,fun j k h =>
      hr j.val j.property.1 k.val k.property.1 k.property.2 h⟩
    obtain ⟨z,hz,_,hpz⟩ := hl S (repr U a s i).property top (fun j => hγ j.val) (ma.val top) hd guard low (by
      intro j
      obtain ⟨hdom,eq⟩ := ma.property ⟨j.val,j.property.1⟩ top j.property.2
      exact ⟨hdom,(hb j.val j.property.1 γ htop j.property.2).trans_eq eq.symm⟩)
    exact ⟨z,hz,fun j hj h => hpz ⟨j,hj,h⟩⟩
  obtain ⟨z,hz⟩ := choose_pair U a s p goal solve
  have zm : z ≤ m γ := (le_iff U a _ _).mpr ((hz.and (mr γ)).mono fun _ hi => hi.1.1.trans_eq hi.2)
  have zproj (j : Set.Iio γ) : ∃ hd, (ρ j.property).proj ⟨z,hd⟩ ≤ r j := by
    apply projection_le_of_eventually
    filter_upwards [hfine j.val,hz,rr j.val j.property] with i hj hi he
    obtain ⟨hd,hp'⟩ := hi.2 j.val hj j.property
    exact ⟨hd,hp'.trans_eq he⟩
  have sz : Cardinal.mk (Set.univ : Set J) < θ := by simpa using hJ
  let comp (j : J) := shortInfima U a hθ fine normal ht (D.stage j).complete
  let hθ₀ := (Fact.out : Cardinal.aleph0 < κ).trans hκθ
  obtain ⟨b,hbz,hb⟩ := InverseSystem.jointDomain_dense T (fun {j k} h => ρ h) hθ₀ comp
    Set.univ sz ⟨γ,Set.mem_univ _⟩ z
  refine ⟨b,hbz.trans zm,hb,fun j => ?_⟩
  have hbd := InverseSystem.jointDomain_direct T (fun {j k} h => ρ h) hθ₀ comp
    (i := ⟨j.val,Set.mem_univ _⟩) j.property hb
  obtain ⟨hd,hp'⟩ := zproj j
  exact ⟨hbd,((ρ j.property).proj.monotone (show (⟨b,hbd⟩ : (ρ j.property).dom) ≤ ⟨z,hd⟩ from hbz)).trans hp'⟩

end Diagram
end Erdos1172Shioya.UltrapowerStage
