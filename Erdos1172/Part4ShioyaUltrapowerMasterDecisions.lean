/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaUltrapowerInternalCondition
public import Erdos1172.Part4ShioyaSimultaneousDecision

@[expose] public section

/-! # Dense decisions on the image word below a strengthened master

A short family of positions in j(θ) fits in one late image word. Lift
an earlier refinement through the connecting projection, decide all
the bits at that later stage, and return to the projection domain.
-/

set_option autoImplicit false
noncomputable section
open Filter Erdos1172GroundUltrapower Erdos1172PosetCompletion
universe u
namespace Erdos1172Shioya.UltrapowerStage

variable {I : Type u} (U : Ultrafilter I) {κ θ : Cardinal.{u}} (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType]
variable (hθ : θ.IsInaccessible) (fine : FineOn U a) (normal : NormalOn U a) (ht : FiberOrderType U κ θ a)
local notation "L" => liftCondition U a hθ fine normal ht
local notation "jᵇ" => boundedGroundEmbedding U θ a

include hθ in
theorem short_image_bound {K : Type u} (hK : Cardinal.mk K < θ) (v : K → Ordinal.{u})
    (hv : ∀ k, v k < ordinalImage U a θ.ord) :
    ∃ b < θ.ord, ∀ k, v k < ordinalImage U a b := by
  have localBound (k : K) : ∃ b < θ.ord, v k < ordinalImage U a b := by
    have h := Ordinal.toZFSet_mem_toZFSet_iff.mpr (hv k)
    rw [ordinalImage_code] at h
    obtain ⟨b,hb,he⟩ := mem_boundedDiagonal_cofinal U θ a hθ _ h
    exact ⟨b,hb,Ordinal.toZFSet_mem_toZFSet_iff.mp ((ordinalImage_code U a b).symm ▸ he)⟩
  choose b hb hvb using localBound
  let β := ⨆ k, b k + 1
  have hβ : β < θ.ord := Ordinal.iSup_add_one_lt_of_lt_cof (by rwa [hθ.isRegular.cof_ord]) hb
  exact ⟨β,hβ,fun k => (hvb k).trans ((ordinalImage_strictMono U a) (Ordinal.lt_iSup_add_one b k))⟩

def decides {δ Λ : Cardinal.{u}} (p : Condition δ Λ) (α : Λ.ord.ToType) (x : p.Poset) : Prop :=
  ∃ n : Bool, (p.withPoint x).Decides α n

private theorem decides_lower {δ Λ : Cardinal.{u}} (p : Condition δ Λ) (α : Λ.ord.ToType) :
    IsLowerSet {x | decides p α x} := by
  rintro x y hxy ⟨n,i,hi,hv⟩
  exact ⟨n,i,hi,(condition_mono hxy).trans hv⟩

private theorem decides_dense {δ Λ : Cardinal.{u}} (p : Condition δ Λ) (α : Λ.ord.ToType)
    (hα : α.toOrd.val < p.length.toOrd.val) (x : p.Poset) : ∃ y ≤ x, decides p α y := by
  classical
  let i := Ordinal.ToType.mk (⟨α.toOrd.val,hα⟩ : Set.Iio p.length.toOrd.val)
  have hi : i.toOrd.val = α.toOrd.val := congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
  by_cases h : condition x ⊓ p.bits i = ⊥
  · exact ⟨x,le_rfl,false,i,hi,le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr h)⟩
  · obtain ⟨y,hy⟩ := exists_condition_le h
    obtain ⟨z,hzy,hzx⟩ := (mem_condition_iff x y).mp (condition_le_iff.mp (hy.trans inf_le_left)) y le_rfl
    exact ⟨z,hzx,true,i,hi,(condition_mono hzy).trans (hy.trans inf_le_right)⟩

variable [Fact (Cardinal.aleph0 < κ)]

private theorem projected_repoints {p q : Condition κ θ} (E : Uniformization.Edge p q)
    (z : (projection U a E.projection hθ.isRegular fine normal ht q.complete).dom)
    (w : Point U a p.Poset) (hz : z.val ≤ diagonal U a E.source)
    (hw : (projection U a E.projection hθ.isRegular fine normal ht q.complete).proj z ≤ w) :
    ZFSet.pair (repointedCode U a hθ fine normal ht q z.val) (repointedCode U a hθ fine normal ht p w) ∈
      (jᵇ (forcingOrder κ θ)).val := by
  let ρ := projection U a E.projection hθ.isRegular fine normal ht q.complete
  obtain ⟨t,rt₁,rt₂⟩ := (projection_graph U a E.projection hθ.isRegular fine normal ht q.complete z.val (ρ.proj z)).mp
    ⟨z.property,rfl⟩
  have h₁ := map_repr U a (fun t : E.projection.dom => t.val) t
  have h₂ := map_repr U a E.projection.proj t
  rw [rt₁] at h₁
  rw [rt₂] at h₂
  have diag : repr U a (diagonal U a E.source) =ᶠ[U] fun _ => E.source := Germ.coe_eq.mp (repr_eq U a _)
  apply repointed_order
  filter_upwards [h₁,h₂,(le_iff U a _ _).mp hz,diag,(le_iff U a _ _).mp hw] with i hi hj hl hc hlow
  exact hi.symm ▸ E.repoint_le (repr U a t i) (hi.symm.trans_le (hl.trans_eq hc)) (hj.symm.trans_le hlow)

/-- All prescribed positions are decided on one later genuine condition,
below the selected earlier strengthening in the internal target order. -/
theorem exists_late_master_decisions {J : Type u} [LinearOrder J] (D : Uniformization.Diagram κ θ J)
    (cofinal : ∀ (j : J) (b : Ordinal.{u}), b < θ.ord →
      ∃ k : J, j < k ∧ b ≤ (D.stage k).length.toOrd.val)
    (m : ∀ j, Point U a (D.poset j))
    (thread : ∀ {i j : J} (h : i < j),
      ∃ hd : m j ∈ (projection U a (D.projection h) hθ.isRegular fine normal ht (D.stage j).complete).dom,
        (projection U a (D.projection h) hθ.isRegular fine normal ht (D.stage j).complete).proj ⟨m j,hd⟩ = m i)
    (source : ∀ {i j : J} (h : i < j), m j ≤ diagonal U a (D.edge h).source)
    (i late : J) (w : Point U a (D.poset i)) (hw : w ≤ m i)
    {K : Type u} (hK : Cardinal.mk K < θ) (v : K → (Order.succ θ).ord.ToType)
    (hv : ∀ k, (v k).toOrd.val < ordinalImage U a θ.ord) :
    ∃ (j : J) (z : Point U a (D.poset j)), i < j ∧ late < j ∧ z ≤ m j ∧
      ZFSet.pair (repointedCode U a hθ fine normal ht (D.stage j) z)
        (repointedCode U a hθ fine normal ht (D.stage i) w) ∈ (jᵇ (forcingOrder κ θ)).val ∧
      ∀ k, ∃ n : Bool, ((L (D.stage j)).withPoint ((presentationIso U a hθ (D.stage j)).symm z)).Decides (v k) n := by
  obtain ⟨b,hb,hvb⟩ := short_image_bound U a hθ hK (fun k => (v k).toOrd.val) hv
  obtain ⟨j,hj,hjlen⟩ := cofinal (max i late) b hb
  let hij := (le_max_left i late).trans_lt hj
  let E := D.edge hij
  let ρ := projection U a E.projection hθ.isRegular fine normal ht (D.stage j).complete
  let e := presentationIso U a hθ (D.stage j)
  let q := L (D.stage j)
  obtain ⟨hd,hm⟩ := thread hij
  obtain ⟨y,hym,hyw⟩ := ρ.lifts ⟨m j,hd⟩ w (hw.trans_eq hm.symm)
  have hlen (k : K) : (v k).toOrd.val < q.length.toOrd.val := by
    rw [(liftCondition_labels U a hθ fine normal ht (D.stage j)).2]
    exact (hvb k).trans_le ((ordinalImage_strictMono U a).monotone hjlen)
  obtain ⟨u,huy,hs⟩ := InverseSystem.short_dense_lower_intersection q.complete hK
    (fun k => {x | decides q (v k) x}) (fun k => decides_lower q (v k))
    (fun k => decides_dense q (v k) (hlen k)) (e.symm y.val)
  obtain ⟨z,hzu⟩ := ρ.dense (e u)
  have hzy : z ≤ y := hzu.trans (e.le_symm_apply.mp huy)
  have hzm : z.val ≤ m j := hzy.trans hym
  refine ⟨j,z.val,hij,(le_max_right i late).trans_lt hj,hzm,?_,?_⟩
  · exact projected_repoints U a hθ fine normal ht E z w (hzm.trans (source hij)) ((ρ.proj.monotone hzy).trans hyw)
  · exact fun k => decides_lower q (v k) (e.symm_apply_le.mpr hzu) (hs k)

omit [Nonempty θ.ord.ToType] in
private theorem bounded_schedule {o : Ordinal.{u}} (nonempty : 0 < o) (ho : o < (Order.succ θ).ord) :
    ∃ f : θ.ord.ToType → o.ToType, Function.Surjective f := by
  have hcard : Cardinal.mk o.ToType ≤ Cardinal.mk θ.ord.ToType := by
    rw [Cardinal.mk_toType,Cardinal.mk_ord_toType]
    exact Order.lt_succ_iff.mp (Cardinal.lt_ord.mp ho)
  obtain ⟨e⟩ := (Cardinal.le_def _ _).mp hcard
  let : Nonempty o.ToType := ⟨Ordinal.ToType.mk ⟨0,nonempty⟩⟩
  exact ⟨Function.invFun e,Function.invFun_surjective e.injective⟩

/-- Given the actual master at the two ends of an edge and a previous
strengthening, a descending run inside the later stage decides the entire
specified initial segment, even when that segment has cardinality θ. -/
theorem decide_whole_prefix {p q : Condition κ θ} (E : Uniformization.Edge p q)
    (m : Point U a q.Poset) (w : Point U a p.Poset) (hsrc : m ≤ diagonal U a E.source)
    (hd : m ∈ (projection U a E.projection hθ.isRegular fine normal ht q.complete).dom)
    (hw : w ≤ (projection U a E.projection hθ.isRegular fine normal ht q.complete).proj ⟨m,hd⟩)
    {o : Ordinal.{u}} (hpos : 0 < o) (hlen : o ≤ ordinalImage U a q.length.toOrd.val) :
    ∃ z : θ.ord.ToType → Point U a q.Poset, Antitone z ∧ (∀ n, z n ≤ m) ∧
      (∀ n, ZFSet.pair (repointedCode U a hθ fine normal ht q (z n)) (repointedCode U a hθ fine normal ht p w)
        ∈ (jᵇ (forcingOrder κ θ)).val) ∧
      (∀ n k, n ≤ k → ZFSet.pair (repointedCode U a hθ fine normal ht q (z k))
        (repointedCode U a hθ fine normal ht q (z n)) ∈ (jᵇ (forcingOrder κ θ)).val) ∧
      ∀ α : (Order.succ θ).ord.ToType, α.toOrd.val < o →
        ∃ n b, ∀ t ≥ n, ((L q).withPoint ((presentationIso U a hθ q).symm (z t))).Decides α b := by
  let Q := L q
  let e := presentationIso U a hθ q
  let ρ := projection U a E.projection hθ.isRegular fine normal ht q.complete
  obtain ⟨y,hym,hyw⟩ := ρ.lifts ⟨m,hd⟩ w hw
  have ho : o < (Order.succ θ).ord := hlen.trans_lt
    (((liftCondition_labels U a hθ fine normal ht q).2).symm.trans_lt Q.length.toOrd.property)
  obtain ⟨f,hf⟩ := bounded_schedule hpos ho
  let coord (n : θ.ord.ToType) : (Order.succ θ).ord.ToType := Ordinal.ToType.mk
    ⟨(f n).toOrd.val,(show (f n).toOrd.val < o from (f n).toOrd.property).trans ho⟩
  have hc (n : θ.ord.ToType) : (coord n).toOrd.val = (f n).toOrd.val :=
    congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
  let tasks (n : θ.ord.ToType) : Set ρ.dom := {x | decides Q (coord n) (e.symm x.val)}
  have dense (n) (x : ρ.dom) : ∃ r ≤ x, r ∈ tasks n := by
    have hl : (coord n).toOrd.val < Q.length.toOrd.val :=
      ((hc n).trans_lt (f n).toOrd.property).trans_le (hlen.trans_eq (liftCondition_labels U a hθ fine normal ht q).2.symm)
    obtain ⟨r,hr,hs⟩ := decides_dense Q (coord n) hl (e.symm x.val)
    obtain ⟨t,ht'⟩ := ρ.dense (e r)
    exact ⟨t,ht'.trans (e.le_symm_apply.mp hr),decides_lower Q _ (e.symm_apply_le.mpr ht') hs⟩
  obtain ⟨r,anti,hy,hit⟩ := exists_dense_meeting_chain
    (ρ.domShortInfima (shortInfima U a hθ.isRegular fine normal ht q.complete))
    (fun n => by simpa using Cardinal.mk_Iio_lt n (by simp)) tasks dense y
  have hmaster (n) : (r n).val ≤ m := (hy n).trans hym
  refine ⟨fun n => (r n).val,fun _ _ h => anti h,hmaster,?_,?_,?_⟩
  · exact fun n => projected_repoints U a hθ fine normal ht E (r n) w ((hmaster n).trans hsrc)
      ((ρ.proj.monotone (hy n)).trans hyw)
  · intro n k h
    apply repointed_order
    have hle : (r k).val ≤ (r n).val := anti h
    exact ((le_iff U a _ _).mp hle).mono fun i hi =>
      Condition.withPoint_le (q.withPoint (repr U a (r n).val i)) hi
  · intro α hα
    let k := Ordinal.ToType.mk (⟨α.toOrd.val,hα⟩ : Set.Iio o)
    obtain ⟨n,hn⟩ := hf k
    have he : coord n = α := Ordinal.ToType.mk.symm.injective (Subtype.ext ((hc n).trans
      ((congrArg (fun b : o.ToType => b.toOrd.val) hn).trans (congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)))))
    obtain ⟨b,i,hi,hv⟩ := hit n
    refine ⟨n,b,fun t ht' => ⟨i,hi.trans (congrArg (fun v : (Order.succ θ).ord.ToType => v.toOrd.val) he),?_⟩⟩
    exact (condition_mono (e.symm.monotone (show (r t).val ≤ (r n).val from anti ht'))).trans hv

/-- Every bounded prefix of the entire image word can be read below a
prescribed previous move, while continuing at an arbitrarily late stage
of the recovered diagram. The sign at each position stabilizes along
the resulting θ-long run. -/
theorem exists_recovered_prefix_runs {J : Type u} [LinearOrder J] (D : Uniformization.Diagram κ θ J)
    (F : Order.PFilter (Algebra κ θ)) (proper : ⊥ ∉ F)
    (meets : ∀ S, RecoveredMaster.edgeTests D S → ∃ b ∈ S, b ∈ F)
    (coding : ∀ i, (D.stage i).CodesDense) (req : ∀ p ∈ D.requirements, condition p ∈ F)
    (count : ∀ i, (RecoveredMaster.realized D F i).Countable)
    (cofinal : ∀ (j : J) (b : Ordinal.{u}), b < θ.ord →
      ∃ k : J, j < k ∧ b ≤ (D.stage k).length.toOrd.val) :
    ∃ m : ∀ i, Point U a (D.poset i), (∀ i, IsGLB (diagonal U a '' RecoveredMaster.realized D F i) (m i)) ∧
      ∀ (i late : J) (w : Point U a (D.poset i)), w ≤ m i →
        ∀ o : Ordinal.{u}, 0 < o → o < ordinalImage U a θ.ord →
          ∃ (j : J) (z : θ.ord.ToType → Point U a (D.poset j)), i < j ∧ late < j ∧ Antitone z ∧
            (∀ n, z n ≤ m j) ∧
            (∀ n, ZFSet.pair (repointedCode U a hθ fine normal ht (D.stage j) (z n))
              (repointedCode U a hθ fine normal ht (D.stage i) w) ∈ (jᵇ (forcingOrder κ θ)).val) ∧
            (∀ n k, n ≤ k → ZFSet.pair (repointedCode U a hθ fine normal ht (D.stage j) (z k))
              (repointedCode U a hθ fine normal ht (D.stage j) (z n)) ∈ (jᵇ (forcingOrder κ θ)).val) ∧
            ∀ α : (Order.succ θ).ord.ToType, α.toOrd.val < o → ∃ n b, ∀ t ≥ n,
              ((L (D.stage j)).withPoint ((presentationIso U a hθ (D.stage j)).symm (z t))).Decides α b := by
  let ind (i : J) : (Set.univ : Set J) := ⟨i,Set.mem_univ _⟩
  obtain ⟨m,hm,hs⟩ := recovered_thread U a D F hθ.isRegular hθ.aleph0_lt fine normal ht
    proper meets coding req count Set.univ
  refine ⟨fun i => m.val (ind i),fun i => hm (ind i),?_⟩
  intro i late w hw o hpos ho
  have hem := Ordinal.toZFSet_mem_toZFSet_iff.mpr ho
  rw [ordinalImage_code] at hem
  obtain ⟨b,hb,hob⟩ := mem_boundedDiagonal_cofinal U θ a hθ _ hem
  have hb' : o < ordinalImage U a b := Ordinal.toZFSet_mem_toZFSet_iff.mp ((ordinalImage_code U a b).symm ▸ hob)
  obtain ⟨j,hj,hlen⟩ := cofinal (max i late) b hb
  let hij := (le_max_left i late).trans_lt hj
  obtain ⟨hd,he⟩ := m.property (ind i) (ind j) hij
  obtain ⟨z,hz⟩ := decide_whole_prefix U a hθ fine normal ht (D.edge hij) (m.val (ind j)) w
    (hs (ind i) (ind j) hij) hd (hw.trans_eq he.symm) hpos
    (hb'.le.trans ((ordinalImage_strictMono U a).monotone hlen))
  exact ⟨j,z,hij,(le_max_right i late).trans_lt hj,hz⟩

end Erdos1172Shioya.UltrapowerStage
