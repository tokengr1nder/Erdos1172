/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaUltrapowerCondition

@[expose] public section

/-! # Set codes for conditions and master points inside the bounded target

The order relation and the incidence of a stage condition in each Boolean
bit are binary relations on the two ordinal domains. These relations,
the domains, and the point encode the forcing condition.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Filter Erdos1172GroundUltrapower Erdos1172PosetCompletion
universe u
namespace Erdos1172Shioya.UltrapowerStage

def relationCode {V W : Type u} (f : V → ZFSet.{u}) (g : W → ZFSet.{u}) (r : V → W → Prop) :=
  ZFSet.range (fun x : {z : V × W // r z.1 z.2} => ZFSet.pair (f x.val.1) (g x.val.2))

def stageOrderCode {κ θ : Cardinal.{u}} (p : Condition κ θ) :=
  relationCode (@ordinalLabel p.presentation.index.toOrd.val) ordinalLabel (fun x y : p.Poset => x ≤ y)

def stageBitsCode {κ θ : Cardinal.{u}} (p : Condition κ θ) :=
  relationCode (@ordinalLabel p.presentation.index.toOrd.val) ordinalLabel
    (fun x : p.Poset => fun k => condition x ≤ p.bits k)

def conditionCode {κ θ : Cardinal.{u}} (p : Condition κ θ) :=
  ZFSet.pair p.presentation.index.toOrd.val.toZFSet
    (ZFSet.pair (stageOrderCode p) (ZFSet.pair (ordinalLabel p.point)
      (ZFSet.pair p.length.toOrd.val.toZFSet (stageBitsCode p))))

private theorem label_inj {o : Ordinal.{u}} : Function.Injective (@ordinalLabel o) :=
  fun _ _ h => Ordinal.ToType.mk.symm.injective (Subtype.ext (Ordinal.toZFSet_injective h))

private theorem mem_relationCode {V W : Type u} (f : V → ZFSet.{u}) (g : W → ZFSet.{u})
    (hf : Function.Injective f) (hg : Function.Injective g) (r : V → W → Prop) (x : V) (y : W) :
    ZFSet.pair (f x) (g y) ∈ relationCode f g r ↔ r x y := by
  rw [relationCode,ZFSet.mem_range]
  constructor
  · rintro ⟨⟨⟨x',y'⟩,h'⟩,he⟩
    have h₁ := hf (ZFSet.pair_inj.mp he).1
    have h₂ := hg (ZFSet.pair_inj.mp he).2
    exact h₁ ▸ h₂ ▸ h'
  · intro h
    exact ⟨⟨(x,y),h⟩,rfl⟩

/-- The code distinguishes the ordinal presentation, its partial order,
the chosen point, the word length, and every regular Boolean coefficient. -/
theorem conditionCode_injective {κ θ : Cardinal.{u}} : Function.Injective (conditionCode (κ := κ) (θ := θ)) := by
  rintro ⟨⟨i,P⟩,sep,cl,x,k,b⟩ ⟨⟨i',Q⟩,sep',cl',y,k',c⟩ h
  obtain ⟨hi,ho,hx,hk,hb⟩ := (show _ ∧ _ ∧ _ ∧ _ ∧ _ from by
    simpa only [conditionCode,ZFSet.pair_inj] using h)
  have ei : i = i' := Ordinal.ToType.mk.symm.injective (Subtype.ext (Ordinal.toZFSet_injective hi))
  have ek : k = k' := Ordinal.ToType.mk.symm.injective (Subtype.ext (Ordinal.toZFSet_injective hk))
  subst i'
  subst k'
  have sameOrder : P = Q := by
    apply PartialOrder.ext
    intro v w
    let r (s t : i.toOrd.val.ToType) := @LE.le _ P.toLE s t
    let r' (s t : i.toOrd.val.ToType) := @LE.le _ Q.toLE s t
    change relationCode ordinalLabel ordinalLabel r = relationCode ordinalLabel ordinalLabel r' at ho
    exact (mem_relationCode _ _ label_inj label_inj r v w).symm.trans
      ((iff_of_eq (congrArg (fun Z : ZFSet => ZFSet.pair (ordinalLabel v) (ordinalLabel w) ∈ Z) ho)).trans
        (mem_relationCode _ _ label_inj label_inj r' v w))
  subst Q
  have ex : x = y := label_inj hx
  subst y
  have ec : b = c := by
    funext t
    apply Heyting.Regular.coe_injective
    apply SetLike.ext
    intro v
    let p : Condition κ θ := ⟨⟨i,P⟩,sep,cl,x,k,b⟩
    let r (s : p.Poset) (j : k.toOrd.val.ToType) := condition s ≤ b j
    let r' (s : p.Poset) (j : k.toOrd.val.ToType) := condition s ≤ c j
    change relationCode ordinalLabel ordinalLabel r = relationCode ordinalLabel ordinalLabel r' at hb
    have he := congrArg (fun Z : ZFSet => ZFSet.pair (ordinalLabel v) (ordinalLabel t) ∈ Z) hb
    have test : r v t ↔ r' v t := (mem_relationCode _ _ label_inj label_inj r v t).symm.trans
      ((iff_of_eq he).trans (mem_relationCode _ _ label_inj label_inj r' v t))
    exact condition_le_iff.symm.trans (test.trans condition_le_iff)
  subst c
  rfl

variable {I : Type u} (U : Ultrafilter I) {κ θ : Cardinal.{u}} (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType]
local notation "jᵇ" => boundedGroundEmbedding U θ a

private theorem pointCode_const {X : Type u} (z : Point U a X) (s : ZFSet.{u}) :
    pointCode U a (fun _ => s) z = (jᵇ s).val := by
  apply congrArg (boundedCollapse U θ a)
  apply Subtype.ext
  change Germ.map (fun _ => s) z.val = Germ.const s
  obtain ⟨η,f,hf⟩ := z.property
  rw [← hf]
  rfl

private theorem imagePair (x y : ZFSet.{u}) :
    (jᵇ (ZFSet.pair x y)).val = ZFSet.pair (jᵇ x).val (jᵇ y).val :=
  pointCode_pair U a (diagonal U a (P := ULift.{u} Unit) ⟨()⟩) (fun _ => x) (fun _ => y)

private theorem imageRelation {V W V' W' : Type u}
    (f : V → ZFSet.{u}) (g : W → ZFSet.{u}) (r : V → W → Prop)
    (f' : V' → ZFSet.{u}) (g' : W' → ZFSet.{u}) (r' : V' → W' → Prop)
    (e : V' ≃ Point U a V) (v : W' ≃ Point U a W)
    (hf : ∀ x, f' x = pointCode U a f (e x)) (hg : ∀ y, g' y = pointCode U a g (v y))
    (hr : ∀ x y, r' x y ↔ Germ.LiftRel r (e x).val (v y).val) :
    relationCode f' g' r' = (jᵇ (relationCode f g r)).val := by
  ext z
  rw [relationCode,ZFSet.mem_range,relationCode,mem_image_carrier_iff]
  constructor
  · rintro ⟨⟨⟨x,y⟩,hxy⟩,rfl⟩
    obtain ⟨w,hw₁,hw₂⟩ := (relation_iff U a r (e x) (v y)).mp ((hr x y).mp hxy)
    refine ⟨w,?_⟩
    rw [pointCode_pair,hf,hg,← hw₁,← hw₂,pointCode_map,pointCode_map]
    rfl
  · rintro ⟨w,rfl⟩
    let x := map U a (fun t : {z : V × W // r z.1 z.2} => t.val.1) w
    let y := map U a (fun t : {z : V × W // r z.1 z.2} => t.val.2) w
    have hxy := (relation_iff U a r x y).mpr ⟨w,rfl,rfl⟩
    refine ⟨⟨⟨e.symm x,v.symm y⟩,(hr _ _).mpr (by rwa [e.apply_symm_apply,v.apply_symm_apply])⟩,?_⟩
    change ZFSet.pair (f' (e.symm x)) (g' (v.symm y)) = _
    rw [pointCode_pair,hf,hg,e.apply_symm_apply,v.apply_symm_apply]
    exact congrArg₂ ZFSet.pair (pointCode_map U a _ f w) (pointCode_map U a _ g w)

variable (hθ : θ.IsInaccessible) (fine : FineOn U a) (normal : NormalOn U a) (ht : FiberOrderType U κ θ a)
local notation "L" => liftCondition U a hθ fine normal ht

def rawEquiv (i : θ.ord.ToType) :
    (imageIndex U a hθ i).toOrd.val.ToType ≃ Point U a i.toOrd.val.ToType :=
  (Equiv.cast (congrArg Ordinal.ToType (imageIndex_ord U a hθ i))).trans (indexEquiv U a _).symm

private theorem castLabel {v w : Ordinal.{u}} (h : v = w) (x : v.ToType) :
    ordinalLabel (Equiv.cast (congrArg Ordinal.ToType h) x) = ordinalLabel x := by
  subst w
  rfl

private theorem rawEquiv_label (i : θ.ord.ToType) (x : (imageIndex U a hθ i).toOrd.val.ToType) :
    ordinalLabel x = pointCode U a ordinalLabel (rawEquiv U a hθ i x) := by
  rw [← indexEquiv_label]
  change ordinalLabel x = ordinalLabel (indexEquiv U a _ ((indexEquiv U a _).symm _))
  rw [Equiv.apply_symm_apply]
  exact (castLabel (imageIndex_ord U a hθ i) x).symm

theorem liftCondition_orderCode (p : Condition κ θ) : stageOrderCode (L p) = (jᵇ (stageOrderCode p)).val := by
  let e := presentationIso U a hθ p
  exact imageRelation U a _ _ _ _ _ _ e.toEquiv e.toEquiv (rawEquiv_label U a hθ _) (rawEquiv_label U a hθ _)
    (fun x y => e.le_iff_le.symm)

private theorem cast_include {v w : Ordinal.{u}} (h : v = w) (x : v.ToType) :
    StringName.includeIndex h.le x = Equiv.cast (congrArg Ordinal.ToType h) x := by
  subst w
  exact Ordinal.ToType.mk.symm.injective (Subtype.ext (StringName.includeIndex_toOrd _ _))

theorem liftCondition_bitsCode (p : Condition κ θ) : stageBitsCode (L p) = (jᵇ (stageBitsCode p)).val := by
  let e := presentationIso U a hθ p
  let v := rawEquiv U a hθ p.length
  apply imageRelation U a _ _ _ _ _ _ e.toEquiv v (rawEquiv_label U a hθ _) (rawEquiv_label U a hθ _)
  intro x k
  let xi := e x
  let ki := v k
  have eq : StringName.includeIndex (imageIndex_ord U a hθ p.length).le k = indexEquiv U a _ ki := by
    change _ = (indexEquiv U a _) ((indexEquiv U a _).symm _)
    rw [Equiv.apply_symm_apply]
    exact cast_include (imageIndex_ord U a hθ p.length) k
  change condition x ≤ (PartialProjection.isoProjection (κ := θ) e).booleanHom
      ((liftedString U a _ p.bits).bits (StringName.includeIndex _ k)) ↔ _
  erw [PartialProjection.iso_condition,eq,liftedString_bit,condition_le_stringBit]
  change _ ↔ Germ.LiftRel _ xi.val ki.val
  rw [← repr_eq U a xi,← repr_eq U a ki]
  rfl

private theorem pointCode_repoint (p : Condition κ θ) (z : Point U a p.Poset) :
    pointCode U a (fun x : p.Poset => conditionCode (p.withPoint x)) z =
      ZFSet.pair (jᵇ p.presentation.index.toOrd.val.toZFSet).val
        (ZFSet.pair (jᵇ (stageOrderCode p)).val (ZFSet.pair (pointCode U a ordinalLabel z)
          (ZFSet.pair (jᵇ p.length.toOrd.val.toZFSet).val (jᵇ (stageBitsCode p)).val))) := by
  unfold conditionCode
  change pointCode U a (fun x : p.Poset => ZFSet.pair p.presentation.index.toOrd.val.toZFSet
    (ZFSet.pair (stageOrderCode p) (ZFSet.pair (ordinalLabel x)
      (ZFSet.pair p.length.toOrd.val.toZFSet (stageBitsCode p))))) z = _
  erw [pointCode_pair U a z (fun _ => p.presentation.index.toOrd.val.toZFSet),
    pointCode_pair U a z (fun _ => stageOrderCode p),pointCode_pair U a z (fun x => ordinalLabel x),
    pointCode_const,pointCode_const,pointCode_const,imagePair]
  rfl

theorem liftCondition_repoint_code (p : Condition κ θ) (x : (L p).Poset) :
    conditionCode ((L p).withPoint x) = pointCode U a (fun z : p.Poset => conditionCode (p.withPoint z))
      (presentationIso U a hθ p x) := by
  rw [pointCode_repoint]
  change ZFSet.pair (L p).presentation.index.toOrd.val.toZFSet
    (ZFSet.pair (stageOrderCode (L p)) (ZFSet.pair (ordinalLabel x)
      (ZFSet.pair (L p).length.toOrd.val.toZFSet (stageBitsCode (L p))))) = _
  let labels := liftCondition_labels U a hθ fine normal ht p
  exact congrArg₂ ZFSet.pair ((congrArg Ordinal.toZFSet labels.1).trans (ordinalImage_code U a _))
    (congrArg₂ ZFSet.pair (liftCondition_orderCode U a hθ fine normal ht p)
      (congrArg₂ ZFSet.pair (rawEquiv_label U a hθ p.presentation.index x)
        (congrArg₂ ZFSet.pair ((congrArg Ordinal.toZFSet labels.2).trans (ordinalImage_code U a _))
          (liftCondition_bitsCode U a hθ fine normal ht p))))

theorem liftCondition_code (p : Condition κ θ) : conditionCode (L p) = (jᵇ (conditionCode p)).val := by
  have h := liftCondition_repoint_code U a hθ fine normal ht p (L p).point
  rw [liftCondition_point,pointCode_diagonal] at h
  exact h

/-- Every repointing, including a master point below the diagonal filter,
belongs to the elementary image of the set of ground forcing conditions. -/
theorem liftCondition_repoint_mem (p : Condition κ θ) (x : (L p).Poset) :
    conditionCode ((L p).withPoint x) ∈ (jᵇ (ZFSet.range (conditionCode (κ := κ) (θ := θ)))).val := by
  rw [mem_image_carrier_iff,liftCondition_repoint_code]
  exact ⟨map U a p.withPoint (presentationIso U a hθ p x),pointCode_map U a p.withPoint conditionCode _⟩

theorem liftCondition_repoint_mem_target (p : Condition κ θ) (x : (L p).Poset) :
    conditionCode ((L p).withPoint x) ∈ boundedTargetClass U θ a :=
  boundedTargetClass_transitive U θ a (jᵇ (ZFSet.range (conditionCode (κ := κ) (θ := θ)))).property
    (liftCondition_repoint_mem U a hθ fine normal ht p x)

def forcingOrder (κ θ : Cardinal.{u}) :=
  relationCode conditionCode conditionCode (@Condition.Refines κ θ)

def repointedCode (p : Condition κ θ) (z : Point U a p.Poset) : ZFSet.{u} :=
  conditionCode ((L p).withPoint ((presentationIso U a hθ p).symm z))

private theorem repointed_eq (p : Condition κ θ) (z : Point U a p.Poset) :
    repointedCode U a hθ fine normal ht p z =
      pointCode U a conditionCode (map U a p.withPoint z) := by
  unfold repointedCode
  erw [liftCondition_repoint_code,OrderIso.apply_symm_apply,pointCode_map]
  rfl

variable [Fact (Cardinal.aleph0 < κ)]

theorem repointed_order (p q : Condition κ θ) (z : Point U a p.Poset) (w : Point U a q.Poset)
    (h : ∀ᶠ i in U, p.withPoint (repr U a z i) ≤ q.withPoint (repr U a w i)) :
    ZFSet.pair (repointedCode U a hθ fine normal ht p z) (repointedCode U a hθ fine normal ht q w) ∈
      (jᵇ (forcingOrder κ θ)).val := by
  let f := map U a p.withPoint z
  let g := map U a q.withPoint w
  have h' : Germ.LiftRel (· ≤ ·) f.val g.val := by
    rw [← repr_eq U a f,← repr_eq U a g,Germ.liftRel_coe]
    exact ((map_repr U a p.withPoint z).and ((map_repr U a q.withPoint w).and h)).mono fun _ hi =>
      hi.1.symm ▸ hi.2.1.symm ▸ hi.2.2
  obtain ⟨t,hf,hg⟩ := (relation_iff U a (· ≤ ·) f g).mp h'
  rw [repointed_eq,repointed_eq,forcingOrder,relationCode,mem_image_graph_iff]
  exact ⟨t,(pointCode_map U a _ conditionCode t).symm.trans (congrArg (pointCode U a conditionCode) hf),
    (pointCode_map U a _ conditionCode t).symm.trans (congrArg (pointCode U a conditionCode) hg)⟩

omit [CountableInterFilter (U : Filter I)] in
private theorem repr_diagonal {P : Type u} [PartialOrder P] (p : P) :
    repr U a (diagonal U a p) =ᶠ[U] fun _ => p := Germ.coe_eq.mp (repr_eq U a _)

theorem repointed_below_diagonal (p : Condition κ θ) (z : Point U a p.Poset) (r : p.Poset)
    (w : Condition κ θ) (hz : z ≤ diagonal U a r) (h : p.withPoint r ≤ w) :
    ZFSet.pair (repointedCode U a hθ fine normal ht p z) (jᵇ (conditionCode w)).val ∈
      (jᵇ (forcingOrder κ θ)).val := by
  have he : repointedCode U a hθ fine normal ht w (diagonal U a w.point) = (jᵇ (conditionCode w)).val :=
    (repointed_eq U a hθ fine normal ht w _).trans rfl
  rw [← he]
  apply repointed_order
  filter_upwards [(le_iff U a _ _).mp hz,repr_diagonal U a r,repr_diagonal U a w.point] with i hi hr hw
  rw [hw]
  exact (Condition.withPoint_le (p.withPoint r) (hi.trans_eq hr)).trans h

theorem master_repoints_edge {p q : Condition κ θ} (E : Uniformization.Edge p q)
    (z : Point U a q.Poset) (w : Point U a p.Poset) (hz : z ≤ diagonal U a E.source)
    (hd : ∃ t : (projection U a E.projection hθ.isRegular fine normal ht q.complete).dom,
      t.val = z ∧ (projection U a E.projection hθ.isRegular fine normal ht q.complete).proj t = w) :
    ZFSet.pair (repointedCode U a hθ fine normal ht q z) (repointedCode U a hθ fine normal ht p w) ∈
      (jᵇ (forcingOrder κ θ)).val := by
  obtain ⟨⟨_,hd⟩,rfl,hw⟩ := hd
  obtain ⟨t,rt₁,rt₂⟩ := (projection_graph U a E.projection hθ.isRegular fine normal ht q.complete _ _).mp ⟨hd,hw⟩
  apply repointed_order
  have h₁ := map_repr U a (fun t : E.projection.dom => t.val) t
  have h₂ := map_repr U a E.projection.proj t
  rw [rt₁] at h₁
  rw [rt₂] at h₂
  filter_upwards [h₁,h₂,(le_iff U a _ _).mp hz,repr_diagonal U a E.source] with i hi hj hl hc
  exact hi.symm ▸ E.repoint_le (repr U a t i) (hi.symm.trans_le (hl.trans_eq hc)) hj.ge

theorem exists_internal_recovered_master {J : Type u} [Preorder J] (D : Uniformization.Diagram κ θ J)
    (F : Order.PFilter (Algebra κ θ)) (proper : ⊥ ∉ F)
    (meets : ∀ S, RecoveredMaster.edgeTests D S → ∃ b ∈ S, b ∈ F)
    (coding : ∀ i, (D.stage i).CodesDense)
    (req : ∀ p ∈ D.requirements, condition p ∈ F)
    (count : ∀ i, (RecoveredMaster.realized D F i).Countable) (s : Set J) :
    ∃ m : InverseSystem.Thread (fun i => Point U a (D.poset i))
        (fun {i j} (h : i < j) =>
          projection U a (D.projection h) hθ.isRegular fine normal ht (D.stage j).complete) s,
      (∀ i, repointedCode U a hθ fine normal ht (D.stage i.val) (m.val i) ∈
        (jᵇ (ZFSet.range (conditionCode (κ := κ) (θ := θ)))).val) ∧
      (∀ i, IsGLB (diagonal U a '' RecoveredMaster.realized D F i.val) (m.val i)) ∧
      (∀ (i : s) (r : D.poset i.val), r ∈ RecoveredMaster.realized D F i.val →
        ∀ w : Condition κ θ, (D.stage i.val).withPoint r ≤ w →
          ZFSet.pair (repointedCode U a hθ fine normal ht (D.stage i.val) (m.val i))
            (jᵇ (conditionCode w)).val ∈ (jᵇ (forcingOrder κ θ)).val) ∧
      ∀ (i j : s), i < j → ZFSet.pair (repointedCode U a hθ fine normal ht (D.stage j.val) (m.val j))
        (repointedCode U a hθ fine normal ht (D.stage i.val) (m.val i)) ∈ (jᵇ (forcingOrder κ θ)).val := by
  obtain ⟨m,hm,hsource⟩ := recovered_thread U a D F hθ.isRegular hθ.aleph0_lt fine normal ht
    proper meets coding req count s
  refine ⟨m,fun i => liftCondition_repoint_mem U a hθ fine normal ht (D.stage i.val) _,hm,?_,?_⟩
  · intro i r hr w hw
    exact repointed_below_diagonal U a hθ fine normal ht _ _ r w ((hm i).1 ⟨r,hr,rfl⟩) hw
  · intro i j h
    obtain ⟨hd,he⟩ := m.property i j h
    exact master_repoints_edge U a hθ fine normal ht (D.edge h) _ _ (hsource i j h) ⟨⟨_,hd⟩,rfl,he⟩

end Erdos1172Shioya.UltrapowerStage
