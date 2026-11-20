/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaUltrapowerStrings
public import Erdos1172.Part4ShioyaReindexing

@[expose] public section

/-! # Dual Shioya conditions and edges on elementary-image ordinals

The external parameter θ⁺ bounds the ordinal j(θ). Both labels of each
individual condition are the actual elementary images of its ground labels.
-/

set_option autoImplicit false
noncomputable section
open Filter Erdos1172GroundUltrapower Erdos1172PosetCompletion
universe u
namespace Erdos1172Shioya.UltrapowerStage

variable {I : Type u} (U : Ultrafilter I) {κ θ : Cardinal.{u}} (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType]
variable (hθ : θ.IsInaccessible)

include hθ in
theorem imageOrdinal_bound (i : θ.ord.ToType) : ordinalImage U a i.toOrd.val < (Order.succ θ).ord := by
  obtain ⟨o,ho,he⟩ := boundedDiagonal_ordinal_lt_successor U θ a hθ
  have h := (ordinalImage_strictMono U a) (show i.toOrd.val < θ.ord from i.toOrd.property)
  have eq : ordinalImage U a θ.ord = o := Ordinal.toZFSet_injective ((ordinalImage_code U a _).trans he)
  exact (h.trans_eq eq).trans ho

def imageIndex (i : θ.ord.ToType) : (Order.succ θ).ord.ToType :=
  Ordinal.ToType.mk ⟨ordinalImage U a i.toOrd.val,imageOrdinal_bound U a hθ i⟩

theorem imageIndex_ord (i : θ.ord.ToType) : (imageIndex U a hθ i).toOrd.val = ordinalImage U a i.toOrd.val :=
  congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)

def pointEquiv (i : θ.ord.ToType) :
    (imageIndex U a hθ i).toOrd.val.ToType ≃ Point U a i.toOrd.val.ToType :=
  (Equiv.cast (congrArg Ordinal.ToType (imageIndex_ord U a hθ i))).trans (indexEquiv U a i.toOrd.val).symm

def presentation (p : Condition κ θ) : Presentation (Order.succ θ) :=
  let e : (imageIndex U a hθ p.presentation.index).toOrd.val.ToType ≃ Point U a p.Poset :=
    pointEquiv U a hθ p.presentation.index
  ⟨imageIndex U a hθ p.presentation.index,PartialOrder.lift (β := Point U a p.Poset) e e.injective⟩

def presentationIso (p : Condition κ θ) : (presentation U a hθ p).Carrier ≃o Point U a p.Poset where
  toEquiv := pointEquiv U a hθ p.presentation.index
  map_rel_iff' := Iff.rfl

abbrev pull {P Q : Type u} [PartialOrder P] [PartialOrder Q] (δ : Cardinal.{u}) (e : P ≃o Q) :=
  (PartialProjection.isoProjection (κ := δ) e).booleanHom

variable (fine : FineOn U a) (normal : NormalOn U a) (ht : FiberOrderType U κ θ a)

def liftCondition (p : Condition κ θ) : Condition θ (Order.succ θ) :=
  let e := presentationIso U a hθ p
  ⟨presentation U a hθ p,separative_of_iso e (separative U a p.separative),
    shortInfima_of_iso e (shortInfima U a hθ.isRegular fine normal ht p.complete),
    e.symm (diagonal U a p.point), imageIndex U a hθ p.length,
    fun j => pull θ e ((liftedString U a _ p.bits).bits
      (StringName.includeIndex (imageIndex_ord U a hθ p.length).le j))⟩

theorem liftCondition_labels (p : Condition κ θ) :
    (liftCondition U a hθ fine normal ht p).presentation.index.toOrd.val = ordinalImage U a p.presentation.index.toOrd.val ∧
    (liftCondition U a hθ fine normal ht p).length.toOrd.val = ordinalImage U a p.length.toOrd.val :=
  ⟨imageIndex_ord U a hθ _,imageIndex_ord U a hθ _⟩

theorem liftCondition_point (p : Condition κ θ) :
    presentationIso U a hθ p (liftCondition U a hθ fine normal ht p).point = diagonal U a p.point :=
  (presentationIso U a hθ p).apply_symm_apply _

private theorem pull_inverse {P Q : Type u} [PartialOrder P] [PartialOrder Q] (δ : Cardinal.{u})
    (e : P ≃o Q) (b : Completion Q) : pull δ e.symm (pull δ e b) = b := by
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro q
  suffices he : condition q ≤ pull δ e.symm (pull δ e b) ↔ condition q ≤ b from
    condition_le_iff.symm.trans (he.trans condition_le_iff)
  rw [PartialProjection.iso_condition,PartialProjection.iso_condition,e.apply_symm_apply]

theorem pull_cone {P Q : Type u} [PartialOrder P] [PartialOrder Q] (δ : Cardinal.{u})
    (e : P ≃o Q) (q : Q) : pull δ e (condition q) = condition (e.symm q) := by
  have h : condition q ≤ pull δ e.symm (condition (e.symm q)) :=
    (PartialProjection.iso_condition (κ := δ) e.symm q _).mpr le_rfl
  apply le_antisymm ((OrderHomClass.mono (pull δ e) h).trans_eq (pull_inverse δ e.symm _))
  apply (PartialProjection.iso_condition (κ := δ) e (e.symm q) _).mpr
  rw [e.apply_symm_apply]

def imageProjection {p q : Condition κ θ} (E : Uniformization.Edge p q) :
    PartialProjection θ (liftCondition U a hθ fine normal ht q).Poset (liftCondition U a hθ fine normal ht p).Poset :=
  ((projection U a E.projection hθ.isRegular fine normal ht q.complete).precomposeIso (presentationIso U a hθ q)).comp
    (PartialProjection.isoProjection (presentationIso U a hθ p).symm) hθ.aleph0_lt
    (liftCondition U a hθ fine normal ht q).complete

theorem projection_pull {p q : Condition κ θ} (E : Uniformization.Edge p q) (b : Completion (Point U a p.Poset)) :
    (imageProjection U a hθ fine normal ht E).booleanHom (pull θ (presentationIso U a hθ p) b) =
      pull θ (presentationIso U a hθ q)
        ((projection U a E.projection hθ.isRegular fine normal ht q.complete).booleanHom b) := by
  unfold imageProjection
  erw [PartialProjection.booleanHom_comp,PartialProjection.booleanHom_precomposeIso]
  exact congrArg (fun z => pull θ (presentationIso U a hθ q)
    ((projection U a E.projection hθ.isRegular fine normal ht q.complete).booleanHom z))
    (pull_inverse θ (presentationIso U a hθ p) b)

private theorem hom_inf {A B : Type u} [CompleteBooleanAlgebra A] [CompleteBooleanAlgebra B]
    (f : CompleteLatticeHom A B) (b c : A) : f (b ⊓ c) = f b ⊓ f c := by
  rw [← sInf_pair,map_sInf,Set.image_pair,sInf_pair]

theorem pull_inf {P Q : Type u} [PartialOrder P] [PartialOrder Q] (δ : Cardinal.{u})
    (e : P ≃o Q) (b c : Completion Q) : pull δ e (b ⊓ c) = pull δ e b ⊓ pull δ e c := hom_inf (pull δ e) b c

def liftEdge {p q : Condition κ θ} (E : Uniformization.Edge p q) :
    Uniformization.Edge (liftCondition U a hθ fine normal ht p) (liftCondition U a hθ fine normal ht q) := by
  let ep := presentationIso U a hθ p
  let eq := presentationIso U a hθ q
  let ρ := projection U a E.projection hθ.isRegular fine normal ht q.complete
  let σ := imageProjection U a hθ fine normal ht E
  let source := diagonal U a E.source
  refine ⟨eq.symm source,σ,?_,?_⟩
  · change condition (eq.symm source) ≤ σ.booleanHom (condition (ep.symm (diagonal U a p.point)))
    erw [← pull_cone θ ep,projection_pull,← pull_cone θ eq]
    exact OrderHomClass.mono (pull θ eq) (edge_point U a E hθ.isRegular fine normal ht)
  · obtain ⟨h,hh⟩ := (extensionValue_iff_bits ρ.booleanHom _ _ (condition_ne_bot source)).mp
      (edge_extension U a E hθ.isRegular fine normal ht)
    let old := liftCondition U a hθ fine normal ht p
    let new := liftCondition U a hθ fine normal ht q
    let hp := (liftCondition_labels U a hθ fine normal ht p).2
    let hq := (liftCondition_labels U a hθ fine normal ht q).2
    let hw : old.length.toOrd.val ≤ new.length.toOrd.val := hp.le.trans (h.trans hq.ge)
    apply extensionValue_of_bits _ _ _ hw
    intro i
    let j := StringName.includeIndex hp.le i
    let k := StringName.includeIndex h j
    have hi : StringName.includeIndex hq.le (StringName.includeIndex hw i) = k := by
      apply Ordinal.ToType.mk.symm.injective
      apply Subtype.ext
      exact ((StringName.includeIndex_toOrd _ _).trans (StringName.includeIndex_toOrd _ _)).trans
        ((StringName.includeIndex_toOrd _ _).trans (StringName.includeIndex_toOrd _ _)).symm
    rw [show old.name.bits i = old.bits i from StringName.bits_ofBits _ _,
      show new.name.bits (StringName.includeIndex hw i) = new.bits (StringName.includeIndex hw i) from
        StringName.bits_ofBits _ _]
    change condition (eq.symm source) ⊓ σ.booleanHom (pull θ ep ((liftedString U a _ p.bits).bits j)) =
      condition (eq.symm source) ⊓ pull θ eq ((liftedString U a _ q.bits).bits
        (StringName.includeIndex hq.le (StringName.includeIndex hw i)))
    erw [hi,projection_pull,← pull_cone θ eq,← pull_inf,← pull_inf]
    exact congrArg (pull θ eq) (hh j)

end Erdos1172Shioya.UltrapowerStage
