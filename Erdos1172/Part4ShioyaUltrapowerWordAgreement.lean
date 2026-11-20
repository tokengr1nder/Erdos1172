/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaUltrapowerGlobalWord
public import Erdos1172.Part4ShioyaRealizedWord

@[expose] public section

/-! # The master word on the image of the original coordinates -/

set_option autoImplicit false
noncomputable section
open Filter Erdos1172GroundUltrapower Erdos1172PosetCompletion
universe u
namespace Erdos1172Shioya.UltrapowerStage
variable {I : Type u} (U : Ultrafilter I) {κ θ : Cardinal.{u}} (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType]
variable (hθ : θ.IsInaccessible) (fine : FineOn U a) (normal : NormalOn U a) (ht : FiberOrderType U κ θ a)
local notation "L" => liftCondition U a hθ fine normal ht

/-- The domain of the stabilized master word contains the concrete image
of each ground index. -/
def wordImageIndex (α : θ.ord.ToType) :
    {β : (Order.succ θ).ord.ToType // β.toOrd.val < ordinalImage U a θ.ord} :=
  ⟨imageIndex U a hθ α,(imageIndex_ord U a hθ α).trans_lt ((ordinalImage_strictMono U a) α.toOrd.property)⟩

/-- A master point below a ground deciding point decides the same bit
in the elementary-image word at the exact elementary-image ordinal. -/
theorem decides_imageIndex (p : Condition κ θ) (x : p.Poset) (z : Point U a p.Poset)
    (hz : z ≤ diagonal U a x) {α : θ.ord.ToType} {b : Bool} (dec : (p.withPoint x).Decides α b) :
    ((L p).withPoint ((presentationIso U a hθ p).symm z)).Decides (imageIndex U a hθ α) b := by
  obtain ⟨i,hi,bit⟩ := dec
  let e := presentationIso U a hθ p
  let j := indexEquiv U a p.length.toOrd.val (diagonal U a i)
  have hj : j.toOrd.val = ordinalImage U a i.toOrd.val := by
    apply Ordinal.toZFSet_injective
    exact (indexEquiv_label U a _ (diagonal U a i)).trans
      ((pointCode_diagonal U a ordinalLabel i).trans (ordinalImage_code U a _).symm)
  let len := (liftCondition_labels U a hθ fine normal ht p).2
  let k := Ordinal.ToType.mk (⟨j.toOrd.val,(show j.toOrd.val < ordinalImage U a p.length.toOrd.val from
    j.toOrd.property).trans_eq len.symm⟩ : Set.Iio (L p).length.toOrd.val)
  have hkj : k.toOrd.val = j.toOrd.val := congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
  have inc : StringName.includeIndex len.le k = j :=
    Ordinal.ToType.mk.symm.injective (Subtype.ext ((StringName.includeIndex_toOrd _ _).trans hkj))
  refine ⟨k,hkj.trans (hj.trans ((congrArg (ordinalImage U a) hi).trans (imageIndex_ord U a hθ α).symm)),?_⟩
  let π := PartialProjection.isoProjection (κ := θ) e
  have eval : (L p).bits k = π.booleanHom (booleanValue U a (diagonal U a (p.bits i))) := by
    change π.booleanHom ((liftedString U a _ p.bits).bits (StringName.includeIndex len.le k)) = _
    rw [inc,liftedString_bit]
    rfl
  have read (c : p.Algebra) (h : condition x ≤ c) :
      condition (e.symm z) ≤ π.booleanHom (booleanValue U a (diagonal U a c)) := by
    apply (PartialProjection.iso_condition e _ _).mpr
    rw [e.apply_symm_apply]
    have hc : map U a condition (diagonal U a x) = diagonal U a (condition x) := rfl
    exact (condition_mono hz).trans ((booleanValue_condition U a (diagonal U a x)).symm.trans_le
      (hc ▸ booleanValue_mono U a ((diagonal U a (P := p.Algebra)).monotone h)))
  cases b with
  | true =>
    change condition (e.symm z) ≤ (L p).bits k
    rw [eval]
    exact read _ bit
  | false =>
    change condition (e.symm z) ≤ ((L p).bits k)ᶜ
    rw [eval]
    exact (read _ bit).trans_eq ((congrArg π.booleanHom (booleanValue_compl U a (diagonal U a (p.bits i)))).trans
      (map_compl' π.booleanHom _))

variable [Fact (Cardinal.aleph0 < κ)]
variable (D : Uniformization.Diagram κ θ θ.ord.ToType) (F : Order.PFilter (Algebra κ θ))

/-- Each source bit that is decided at a realized stage point has its
ground sign in the stabilized word. This implication needs no further
meeting property of the source filter. -/
theorem stabilized_word_at_realized (q : ∀ j, Point U a (D.poset j))
    (word : {β : (Order.succ θ).ord.ToType // β.toOrd.val < ordinalImage U a θ.ord} → Bool)
    (hm : ∀ j x, x ∈ RecoveredMaster.realized D F j → q j ≤ diagonal U a x)
    (chain : ∀ i j : θ.ord.ToType, i < j →
      ((L (D.stage j)).withPoint ((presentationIso U a hθ (D.stage j)).symm (q j))).Refines
        ((L (D.stage i)).withPoint ((presentationIso U a hθ (D.stage i)).symm (q i))))
    (stable : ∀ α, ∃ j, ∀ k ≥ j, ((L (D.stage k)).withPoint
      ((presentationIso U a hθ (D.stage k)).symm (q k))).Decides α.val (word α))
    (j : θ.ord.ToType) (x : D.poset j) (hx : x ∈ RecoveredMaster.realized D F j)
    {α : θ.ord.ToType} {b : Bool} (dec : ((D.stage j).withPoint x).Decides α b) :
    word (wordImageIndex U a hθ α) = b := by
  let : Fact (Cardinal.aleph0 < θ) := ⟨hθ.aleph0_lt⟩
  let Q (k : θ.ord.ToType) := (L (D.stage k)).withPoint ((presentationIso U a hθ (D.stage k)).symm (q k))
  let β := wordImageIndex U a hθ α
  obtain ⟨k,hk⟩ := stable β
  let t := max j k
  have d := decides_imageIndex U a hθ fine normal ht (D.stage j) x (q j) (hm j x hx) dec
  have dt : (Q t).Decides β.val b := by
    rcases (le_max_left j k).lt_or_eq with h | he
    · exact Condition.decides_mono (chain j t h) d
    · change j = t at he
      rw [← he]
      exact d
  have db := hk t (le_max_right _ _)
  change (Q t).Decides β.val (word β) at db
  change word β = b
  cases hb : word β <;> cases b <;> first | rfl | rw [hb] at db
  · exact (Condition.opposite_decisions db dt).elim
  · exact (Condition.opposite_decisions dt db).elim

/-- The stabilized signs on j''θ are exactly the signs of the ground
filter, as measured by membership of its signed decision Boolean values. -/
theorem stabilized_word_agrees (q : ∀ j, Point U a (D.poset j))
    (word : {β : (Order.succ θ).ord.ToType // β.toOrd.val < ordinalImage U a θ.ord} → Bool)
    (hm : ∀ j x, x ∈ RecoveredMaster.realized D F j → q j ≤ diagonal U a x)
    (chain : ∀ i j : θ.ord.ToType, i < j →
      ((L (D.stage j)).withPoint ((presentationIso U a hθ (D.stage j)).symm (q j))).Refines
        ((L (D.stage i)).withPoint ((presentationIso U a hθ (D.stage i)).symm (q i))))
    (stable : ∀ α, ∃ j, ∀ k ≥ j, ((L (D.stage k)).withPoint
      ((presentationIso U a hθ (D.stage k)).symm (q k))).Decides α.val (word α))
    (proper : ⊥ ∉ F) (meets : ∀ α, ∃ b ∈ RecoveredMaster.wordTest D α, b ∈ F)
    (req : ∀ p ∈ D.requirements, condition p ∈ F)
    (covers : ∀ α : θ.ord.ToType, ∃ j, α.toOrd.val < (D.stage j).length.toOrd.val)
    (α : θ.ord.ToType) (b : Bool) :
    word (wordImageIndex U a hθ α) = b ↔ decisionValue κ θ α b ∈ F := by
  obtain ⟨j,x,n,hx,hn,mem⟩ := RecoveredMaster.exists_realized_decision D F proper meets req covers α
  rw [stabilized_word_at_realized U a hθ fine normal ht D F q word hm chain stable j x hx hn]
  have no (h₀ : decisionValue κ θ α false ∈ F) (h₁ : decisionValue κ θ α true ∈ F) : False :=
    proper ((disjoint_iff.mp (decisionValues_disjoint κ θ α)) ▸ F.inf_mem h₀ h₁)
  exact ⟨fun h => h ▸ mem,fun hb => by
    cases n <;> cases b <;> first | rfl | exact (no mem hb).elim | exact (no hb mem).elim⟩

local notation "jᵇ" => boundedGroundEmbedding U θ a

/-- The single master run from the recovered diagram both decides the
full image word and restricts on j''θ to the source generic word. -/
theorem exists_recovered_global_word_agrees (hκθ : κ < θ) (hl : D.localLifts) (proper : ⊥ ∉ F)
    (edges : ∀ S, RecoveredMaster.edgeTests D S → ∃ b ∈ S, b ∈ F)
    (reads : ∀ α, ∃ b ∈ RecoveredMaster.wordTest D α, b ∈ F)
    (coding : ∀ j, (D.stage j).CodesDense) (req : ∀ p ∈ D.requirements, condition p ∈ F)
    (count : ∀ j, (RecoveredMaster.realized D F j).Countable)
    (cofinal : ∀ (j : θ.ord.ToType) (b : Ordinal.{u}), b < θ.ord →
      ∃ k : θ.ord.ToType, j < k ∧ b ≤ (D.stage k).length.toOrd.val) :
    ∃ (q : ∀ j, Point U a (D.poset j))
      (word : {α : (Order.succ θ).ord.ToType // α.toOrd.val < ordinalImage U a θ.ord} → Bool),
      (∀ j x, x ∈ RecoveredMaster.realized D F j → q j ≤ diagonal U a x) ∧
      (∀ j, repointedCode U a hθ fine normal ht (D.stage j) (q j) ∈
        (jᵇ (ZFSet.range (conditionCode (κ := κ) (θ := θ)))).val) ∧
      (∀ i j : θ.ord.ToType, i < j →
        ((L (D.stage j)).withPoint ((presentationIso U a hθ (D.stage j)).symm (q j))).Refines
          ((L (D.stage i)).withPoint ((presentationIso U a hθ (D.stage i)).symm (q i))) ∧
        ZFSet.pair (repointedCode U a hθ fine normal ht (D.stage j) (q j))
          (repointedCode U a hθ fine normal ht (D.stage i) (q i)) ∈ (jᵇ (forcingOrder κ θ)).val) ∧
      (∀ α, ∃ j, ∀ k ≥ j, ((L (D.stage k)).withPoint
        ((presentationIso U a hθ (D.stage k)).symm (q k))).Decides α.val (word α)) ∧
      ∀ α b, word (wordImageIndex U a hθ α) = b ↔ decisionValue κ θ α b ∈ F := by
  obtain ⟨q,word,hm,mem,chain,st⟩ := exists_recovered_global_word U a hθ fine normal ht hκθ D hl F
    proper edges coding req count cofinal
  exact ⟨q,word,hm,mem,chain,st,stabilized_word_agrees U a hθ fine normal ht D F q word hm
    (fun i j h => (chain i j h).1) st proper reads req
    (RecoveredMaster.word_covers_of_cofinal D hθ.aleph0_lt.le cofinal)⟩

end Erdos1172Shioya.UltrapowerStage
