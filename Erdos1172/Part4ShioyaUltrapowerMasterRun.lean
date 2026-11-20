/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaUltrapowerMarkedLifts
public import Erdos1172.Part4ShioyaThreadDecisionRun

@[expose] public section

/-! # A single master run through a coded ground diagram -/

set_option autoImplicit false
noncomputable section
open Filter Erdos1172GroundUltrapower Erdos1172PosetCompletion
universe u
namespace Erdos1172Shioya.UltrapowerStage
variable {I : Type u} (U : Ultrafilter I) {κ θ : Cardinal.{u}} (a : I → Set θ.ord.ToType)
variable (hθ : θ.IsRegular) (fine : FineOn U a) (normal : NormalOn U a) (ht : FiberOrderType U κ θ a)
variable {J : Type u} [LinearOrder J] [unc : Fact (Cardinal.aleph0 < κ)]
variable (D : Uniformization.Diagram κ θ J)
set_option quotPrecheck false
local notation "T" => fun j => Point U a (D.poset j)
local notation "ρ" => fun {j k : J} (h : j < k) =>
  projection U a (D.projection h) hθ fine normal ht (D.stage k).complete

private theorem ground_triangle (coding : ∀ j, (D.stage j).CodesDense)
    {i j k : J} (h : i < j) (g : j < k) (q : D.poset k)
    (h₁ : q ≤ (D.edge g).source) (h₂ : q ≤ (D.edge (h.trans g)).source)
    (hd : q ∈ (D.projection g).dom) (hd' : q ∈ (D.projection (h.trans g)).dom)
    (hs : (D.projection g).proj ⟨q,hd⟩ ≤ (D.edge h).source)
    (hc : (D.projection g).proj ⟨q,hd⟩ ∈ (D.projection h).dom) :
    (D.projection h).proj ⟨(D.projection g).proj ⟨q,hd⟩,hc⟩ =
      (D.projection (h.trans g)).proj ⟨q,hd'⟩ := by
  let π := D.projection g
  let σ := D.projection h
  let τ := D.projection (h.trans g)
  let υ := π.comp σ unc.out (D.stage k).complete
  have hp := (π.dom_condition ⟨q,hd⟩ _).mpr (condition_mono hs)
  have he : condition q ≤ extensionValue υ.booleanHom (D.stage i).name (D.stage k).name := by
    rw [show υ.booleanHom = π.booleanHom.comp σ.booleanHom from π.booleanHom_comp σ unc.out _]
    exact extensionValue_trans σ.booleanHom π.booleanHom _ _ _ hp (D.edge h).string_le
      ((condition_mono h₁).trans (D.edge g).string_le)
  exact (coding i).freeze_proj (w := (D.stage k).withPoint q) υ τ he
    ((condition_mono h₂).trans (D.edge (h.trans g)).string_le) q le_rfl ⟨hd,hc⟩ hd'

variable [Nonempty θ.ord.ToType]

/-- Freezing in the ordinary ground diagram gives the same triangle equality
for the lifted partial projections at every guarded point in their domains. -/
theorem projection_triangle (coding : ∀ j, (D.stage j).CodesDense)
    {i j k : J} (h : i < j) (g : j < k) (q : Point U a (D.poset k))
    (h₁ : q ≤ diagonal U a (D.edge g).source) (h₂ : q ≤ diagonal U a (D.edge (h.trans g)).source)
    (hd : q ∈ (ρ g).dom) (hd' : q ∈ (ρ (h.trans g)).dom)
    (hs : (ρ g).proj ⟨q,hd⟩ ≤ diagonal U a (D.edge h).source)
    (hc : (ρ g).proj ⟨q,hd⟩ ∈ (ρ h).dom) :
    (ρ h).proj ⟨(ρ g).proj ⟨q,hd⟩,hc⟩ = (ρ (h.trans g)).proj ⟨q,hd'⟩ := by
  let x := (ρ g).proj ⟨q,hd⟩
  let y := (ρ (h.trans g)).proj ⟨q,hd'⟩
  let z := (ρ h).proj ⟨x,hc⟩
  have val {l : J} (p : Point U a (D.poset l)) (v : D.poset l) (b : p ≤ diagonal U a v) :
      ∀ᶠ t in U, repr U a p t ≤ v := by
    have e : repr U a (diagonal U a v) =ᶠ[U] fun _ => v := Germ.coe_eq.mp (repr_eq U a _)
    exact (((le_iff U a _ _).mp b).and e).mono fun _ ev => ev.1.trans_eq ev.2
  have eqs : repr U a z =ᶠ[U] repr U a y := by
    have e₁ := projection_eq_eventually U a (D.projection g) hθ fine normal ht (D.stage k).complete q x ⟨hd,rfl⟩
    have e₂ := projection_eq_eventually U a (D.projection (h.trans g)) hθ fine normal ht (D.stage k).complete q y ⟨hd',rfl⟩
    have e₃ := projection_eq_eventually U a (D.projection h) hθ fine normal ht (D.stage j).complete x z ⟨hc,rfl⟩
    filter_upwards [e₁,e₂,e₃,val _ _ h₁,val _ _ h₂,val _ _ hs] with t a₁ a₂ a₃ b₁ b₂ b₃
    obtain ⟨d₁,f₁⟩ := a₁
    obtain ⟨d₂,f₂⟩ := a₂
    obtain ⟨d₃,f₃⟩ := a₃
    let d := f₁.symm ▸ d₃
    have eq := ground_triangle D coding h g _ b₁ b₂ d₁ d₂ (f₁.trans_le b₃) d
    have step := congrArg (D.projection h).proj
      (show (⟨(D.projection g).proj ⟨repr U a q t,d₁⟩,d⟩ : (D.projection h).dom) =
        ⟨repr U a x t,d₃⟩ from Subtype.ext f₁)
    exact f₃.symm.trans (step.symm.trans (eq.trans f₂))
  exact Subtype.ext (((repr_eq U a z).symm.trans (Germ.coe_eq.mpr eqs)).trans (repr_eq U a y))

/-- One dense decision at the greatest marked stage extends an entire
lower thread. The returned closed thread contains the decided top point. -/
theorem extend_deciding_thread (hκθ : κ < θ) (hJ : Cardinal.mk J < θ)
    (hl : D.localLifts) (coding : ∀ j, (D.stage j).CodesDense)
    (γ : J) (hγ : ∀ j, j ≤ γ) (m : ∀ j, Point U a (D.poset j))
    (thread : ∀ {j k : J} (h : j < k), ∃ hd, (ρ h).proj ⟨m k,hd⟩ = m j)
    (source : ∀ {j k : J} (h : j < k), m k ≤ diagonal U a (D.edge h).source)
    (r : ∀ j : Set.Iio γ, Point U a (D.poset j.val))
    (compatible : ∀ (j k : Set.Iio γ) (h : j < k), ∃ hd, (ρ h).proj ⟨r k,hd⟩ = r j)
    (below : ∀ j, r j ≤ m j.val) (K : Set (Point U a (D.poset γ))) (lower : IsLowerSet K)
    (dense : ∀ p ≤ m γ, ∃ q ≤ p, q ∈ K) :
    ∃ t : ∀ j, Point U a (D.poset j), (∀ j, t j ≤ m j) ∧ t γ ∈ K ∧
      (∀ j : Set.Iio γ, t j.val ≤ r j) ∧
      ∀ {i j : J} (h : i < j), ∃ hd, (ρ h).proj ⟨t j,hd⟩ = t i := by
  classical
  let h₀ := unc.out.trans hκθ
  let comp (i : J) := shortInfima U a hθ fine normal ht (D.stage i).complete
  let all : Set J := Set.univ
  let idx (j : J) : all := ⟨j,Set.mem_univ j⟩
  obtain ⟨u,hum,_,hu⟩ := lift_marked_thread U a hθ fine normal ht D hκθ hJ hl γ hγ m thread source r compatible below
  obtain ⟨w,hwu,hw⟩ := dense u hum
  obtain ⟨z,hzw,hz⟩ := InverseSystem.jointDomain_dense T (fun {_ _} h => ρ h) h₀ comp all
    (by simpa [all] using hJ) (idx γ) w
  have hzu := hzw.trans hwu
  have hzm := hzu.trans hum
  have dom (i : J) (h : i < γ) : z ∈ (ρ h).dom := InverseSystem.jointDomain_direct T
    (fun {_ _} g => ρ g) h₀ comp (i := idx i) (γ := idx γ) h hz
  let proj (i : J) (h : i < γ) := (ρ h).proj ⟨z,dom i h⟩
  have prev (i : J) (h : i < γ) : proj i h ≤ r ⟨i,h⟩ := by
    obtain ⟨d,e⟩ := hu ⟨i,h⟩
    exact ((ρ h).proj.monotone (show (⟨z,dom i h⟩ : (ρ h).dom) ≤ ⟨u,d⟩ from hzu)).trans e
  let t (i : J) : Point U a (D.poset i) :=
    if eq : i = γ then eq.symm ▸ z else proj i ((hγ i).lt_of_ne eq)
  have top : t γ = z := dif_pos rfl
  have old (i : J) (h : i < γ) : t i = proj i h := dif_neg h.ne
  refine ⟨t,?_,top ▸ lower hzw hw,fun i => (old i.val i.property).trans_le (prev _ _),?_⟩
  · intro i
    rcases (hγ i).lt_or_eq with h | rfl
    · exact ((old _ h).trans_le (prev _ h)).trans (below ⟨_,h⟩)
    · exact top.trans_le hzm
  intro i j hij
  rcases (hγ j).lt_or_eq with hj | rfl
  · have hi := hij.trans hj
    have dj := InverseSystem.jointDomain_project T (fun {_ _} g => ρ g) h₀ comp
      (i := idx j) (γ := idx γ) hj hz
    have di := InverseSystem.jointDomain_direct T (fun {_ _} g => ρ g) h₀ comp
      (i := idx i) (γ := idx j) hij dj
    rw [old _ hi,old _ hj]
    exact ⟨di,projection_triangle U a hθ fine normal ht D coding hij hj z
      (hzm.trans (source hj)) (hzm.trans (source hi)) (dom j hj) (dom i hi)
      (((prev j hj).trans (below ⟨_,hj⟩)).trans (source hij)) di⟩
  · rw [top,old _ hij]
    exact ⟨dom i hij,rfl⟩

/-- One descending run on the entire well-order meets each stage's dense
open requirement. Only its proper initial segments have size below θ. -/
theorem exists_master_run [WellFoundedLT J] (hκθ : κ < θ) (hJ : ∀ j : J, Cardinal.mk (Set.Iic j) < θ)
    (hl : D.localLifts) (coding : ∀ j, (D.stage j).CodesDense)
    (m : ∀ j, Point U a (D.poset j))
    (thread : ∀ {j k : J} (h : j < k), ∃ hd, (ρ h).proj ⟨m k,hd⟩ = m j)
    (source : ∀ {j k : J} (h : j < k), m k ≤ diagonal U a (D.edge h).source)
    (K : ∀ j, Set (Point U a (D.poset j))) (lower : ∀ j, IsLowerSet (K j))
    (dense : ∀ j p, p ≤ m j → ∃ q ≤ p, q ∈ K j) :
    ∃ q : ∀ j, Point U a (D.poset j), (∀ j, q j ≤ m j) ∧ (∀ j, q j ∈ K j) ∧
      ∀ {i j : J} (h : i < j), ∃ hd, (ρ h).proj ⟨q j,hd⟩ ≤ q i := by
  let π := fun {i j : J} (h : i < j) => ρ h
  let comp (j : J) := shortInfima U a hθ fine normal ht (D.stage j).complete
  have sm (j : J) : Cardinal.mk (Set.Iio j) < θ :=
    (Cardinal.mk_le_mk_of_subset Set.Iio_subset_Iic_self).trans_lt (hJ j)
  obtain ⟨t,hb,hit,dec⟩ := InverseSystem.exists_thread_decision_run T (fun {_ _} h => π h) sm comp m K (by
    intro j r hr
    let A := Uniformization.MixedDiagram.restrict D (Set.Iic j)
    let last : Set.Iic j := ⟨j,le_rfl⟩
    let lo (i : Set.Iio last) : Set.Iio j := ⟨i.val.val,i.property⟩
    obtain ⟨t,tm,hit,tr,th⟩ := extend_deciding_thread U a hθ fine normal ht A hκθ (hJ j)
      (Uniformization.MixedDiagram.restrict_localLifts D hl _) (fun i => coding i.val)
      last (fun i => i.property) (fun i => m i.val) (fun h => thread h) (fun h => source h)
      (fun i => r.val (lo i)) (fun i k h => r.property (lo i) (lo k) h) (fun i => hr (lo i))
      (K j) (lower j) (dense j)
    exact ⟨⟨t,fun _ _ h => th h⟩,tm,hit,fun i => tr ⟨⟨i.val,i.property.le⟩,i.property⟩⟩)
  let q (j : J) := (t j).val ⟨j,le_rfl⟩
  refine ⟨q,fun j => hb j _,hit,?_⟩
  intro i j h
  obtain ⟨hd,he⟩ := (t j).property ⟨i,h.le⟩ ⟨j,le_rfl⟩ h
  exact ⟨hd,he.trans_le (dec i j h ⟨i,le_rfl⟩)⟩

section Coded
variable [CountableInterFilter (U : Filter I)] (hbig : θ.IsInaccessible)
local notation "L" => liftCondition U a hbig fine normal ht
local notation "jᵇ" => boundedGroundEmbedding U θ a

/-- Projected lower bounds compare the actual lifted conditions, and their
set-coded pair belongs to the image of the original forcing order. -/
theorem repointed_refines_of_projection {p q : Condition κ θ} (E : Uniformization.Edge p q)
    (z : Point U a q.Poset) (w : Point U a p.Poset) (hz : z ≤ diagonal U a E.source)
    (hd : z ∈ (projection U a E.projection hbig.isRegular fine normal ht q.complete).dom)
    (hw : (projection U a E.projection hbig.isRegular fine normal ht q.complete).proj ⟨z,hd⟩ ≤ w) :
    ((L q).withPoint ((presentationIso U a hbig q).symm z)).Refines
      ((L p).withPoint ((presentationIso U a hbig p).symm w)) ∧
    ZFSet.pair (repointedCode U a hbig fine normal ht q z) (repointedCode U a hbig fine normal ht p w) ∈
      (jᵇ (forcingOrder κ θ)).val := by
  let : Fact (Cardinal.aleph0 < θ) := ⟨hbig.aleph0_lt⟩
  let e := presentationIso U a hbig q
  let e' := presentationIso U a hbig p
  let π := projection U a E.projection hbig.isRegular fine normal ht q.complete
  let E' := liftEdge U a hbig fine normal ht E
  constructor
  · have dm : e (e.symm z) ∈ π.dom := (e.apply_symm_apply z).symm ▸ hd
    have dc : e.symm z ∈ E'.projection.dom := ⟨dm,Set.mem_univ _⟩
    apply E'.repoint_le ⟨e.symm z,dc⟩ (e.symm.monotone hz)
    apply e'.symm.monotone
    exact (congrArg π.proj (show (⟨e (e.symm z),dm⟩ : π.dom) = ⟨z,hd⟩ from
      Subtype.ext (e.apply_symm_apply z))).trans_le hw
  · apply repointed_order
    have eq := projection_eq_eventually U a E.projection hbig.isRegular fine normal ht q.complete
      z (π.proj ⟨z,hd⟩) ⟨hd,rfl⟩
    have diag : repr U a (diagonal U a E.source) =ᶠ[U] fun _ => E.source :=
      Germ.coe_eq.mp (repr_eq U a _)
    filter_upwards [eq,(le_iff U a _ _).mp hz,(le_iff U a _ _).mp hw,diag] with i hi hs hv he
    obtain ⟨d,hy⟩ := hi
    exact E.repoint_le ⟨_,d⟩ (hs.trans_eq he) (hy.trans_le hv)

/-- In one run through the entire recovered ground diagram, meet every
specified stagewise dense open and extend the realized filter at every
coordinate. Both the actual repointings and their internal codes descend. -/
theorem exists_recovered_task_run [WellFoundedLT J] (hκθ : κ < θ)
    (hJ : ∀ j : J, Cardinal.mk (Set.Iic j) < θ) (hl : D.localLifts)
    (F : Order.PFilter (Algebra κ θ)) (proper : ⊥ ∉ F)
    (meets : ∀ S, RecoveredMaster.edgeTests D S → ∃ b ∈ S, b ∈ F)
    (coding : ∀ j, (D.stage j).CodesDense) (req : ∀ p ∈ D.requirements, condition p ∈ F)
    (count : ∀ j, (RecoveredMaster.realized D F j).Countable)
    (K : ∀ j, Set (Point U a (D.poset j))) (lower : ∀ j, IsLowerSet (K j))
    (dense : ∀ j p, ∃ q ≤ p, q ∈ K j) :
    ∃ q : ∀ j, Point U a (D.poset j), (∀ j, q j ∈ K j) ∧
      (∀ j x, x ∈ RecoveredMaster.realized D F j → q j ≤ diagonal U a x) ∧
      (∀ j, repointedCode U a hbig fine normal ht (D.stage j) (q j) ∈
        (jᵇ (ZFSet.range (conditionCode (κ := κ) (θ := θ)))).val) ∧
      ∀ i j : J, i < j →
        ((L (D.stage j)).withPoint ((presentationIso U a hbig (D.stage j)).symm (q j))).Refines
          ((L (D.stage i)).withPoint ((presentationIso U a hbig (D.stage i)).symm (q i))) ∧
        ZFSet.pair (repointedCode U a hbig fine normal ht (D.stage j) (q j))
          (repointedCode U a hbig fine normal ht (D.stage i) (q i)) ∈ (jᵇ (forcingOrder κ θ)).val := by
  let ind (j : J) : (Set.univ : Set J) := ⟨j,Set.mem_univ _⟩
  obtain ⟨m,gm,src⟩ := recovered_thread U a D F hbig.isRegular hbig.aleph0_lt fine normal ht
    proper meets coding req count Set.univ
  obtain ⟨q,qm,hit,prev⟩ := exists_master_run U a hbig.isRegular fine normal ht D hκθ hJ hl coding
    (fun j => m.val (ind j)) (fun {i j} h => m.property (ind i) (ind j) h)
    (fun {i j} h => src (ind i) (ind j) h) K lower (fun j p _ => dense j p)
  refine ⟨q,hit,fun j x hx => (qm j).trans ((gm (ind j)).1 ⟨x,hx,rfl⟩),
    fun j => liftCondition_repoint_mem U a hbig fine normal ht (D.stage j) _,?_⟩
  intro i j h
  obtain ⟨d,hd⟩ := prev h
  exact repointed_refines_of_projection U a fine normal ht hbig (D.edge h) _ _
    ((qm j).trans (src (ind i) (ind j) h)) d hd

end Coded
end Erdos1172Shioya.UltrapowerStage
