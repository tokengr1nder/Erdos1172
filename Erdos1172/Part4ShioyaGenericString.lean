/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4DualShioyaForcing

@[expose] public section

/-! # The generic binary string of the dual Shioya forcing

The first part of the proof of Lemma 28 of Eskew and Hayut, *Dense
ideals*, reads a bit from a condition whose point decides that bit in
its presentation. In the regular completion these decisions are dense
and opposite decisions are incompatible. Their suprema are therefore
complementary coefficients of a binary function on the whole ordinal.
-/

set_option autoImplicit false
noncomputable section
open bSet Erdos1172PosetCompletion
open scoped Flypitch
universe u

namespace Erdos1172Shioya

private theorem exists_point_below {P : Type u} [Preorder P] (p : P) {d : Completion P}
    (h : condition p ⊓ d ≠ ⊥) : ∃ r ≤ p, condition r ≤ d := by
  obtain ⟨q, hq⟩ := exists_condition_le h
  obtain ⟨r, hrq, hrp⟩ :=
    (mem_condition_iff p q).mp (condition_le_iff.mp (hq.trans inf_le_left)) q le_rfl
  exact ⟨r, hrp, (condition_mono hrq).trans (hq.trans inf_le_right)⟩

theorem condition_nonempty {κ θ : Cardinal.{u}} (hθ : 1 < θ) : Nonempty (Condition κ θ) := by
  have ho : (1 : Ordinal.{u}) < θ.ord := Cardinal.lt_ord.mpr (by simpa only [Ordinal.card_one] using hθ)
  let j : θ.ord.ToType := Ordinal.ToType.mk ⟨1, ho⟩
  have hj : j.toOrd.val = 1 := congrArg Subtype.val ((Ordinal.ToType.mk (o := θ.ord)).symm_apply_apply _)
  let A : Presentation θ := ⟨j, inferInstance⟩
  have hcard : Cardinal.mk A.Carrier = Cardinal.mk PUnit.{u+1} := by
    change Cardinal.mk j.toOrd.val.ToType = _
    rw [Cardinal.mk_toType, hj, Ordinal.card_one, Cardinal.mk_eq_one]
  let e := (Cardinal.eq.mp hcard).some
  let a : A.Carrier := e.symm PUnit.unit
  have hall (x y : A.Carrier) : x ≤ y := (e.injective (Subsingleton.elim (e x) (e y))).le
  refine ⟨⟨A, fun x y h => (h (hall x y)).elim, ?_, a, j, fun _ => ⊥⟩⟩
  intro L _ _ _ f _
  exact ⟨a, fun z _ => hall a z, fun z _ => hall z a⟩

namespace Condition

variable {κ θ : Cardinal.{u}} [Fact (Cardinal.aleph0 < κ)]

def Decides (p : Condition κ θ) (α : θ.ord.ToType) (n : Bool) : Prop :=
  ∃ i : p.length.toOrd.val.ToType, i.toOrd.val = α.toOrd.val ∧
    condition p.point ≤ if n then p.bits i else (p.bits i)ᶜ

theorem decides_mono {p q : Condition κ θ} (hpq : p ≤ q) {α : θ.ord.ToType} {n : Bool}
    (hq : q.Decides α n) : p.Decides α n := by
  obtain ⟨π, hp, hext⟩ := hpq
  obtain ⟨h, hb⟩ := (extensionValue_iff_bits π.booleanHom q.name p.name (condition_ne_bot p.point)).mp hext
  obtain ⟨i, hi, hqi⟩ := hq
  let j := StringName.includeIndex h i
  refine ⟨j, (StringName.includeIndex_toOrd h i).trans hi, ?_⟩
  have hagree := hb i
  simp only [name, StringName.bits_ofBits] at hagree
  cases n with
  | true =>
    have hone : condition p.point ≤ π.booleanHom (q.bits i) := hp.trans (OrderHomClass.mono _ hqi)
    exact (le_inf le_rfl hone).trans (hagree.le.trans inf_le_right)
  | false =>
    change condition q.point ≤ (q.bits i)ᶜ at hqi
    have hzero : condition p.point ≤ (π.booleanHom (q.bits i))ᶜ := by
      exact (hp.trans (OrderHomClass.mono π.booleanHom hqi)).trans_eq (map_compl' π.booleanHom _)
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff_inf_le.mpr
    exact hagree.ge.trans ((inf_le_inf_right _ hzero).trans (compl_inf_self _).le)

omit [Fact (Cardinal.aleph0 < κ)] in
theorem opposite_decisions {p : Condition κ θ} {α : θ.ord.ToType} (h₀ : p.Decides α false)
    (h₁ : p.Decides α true) : False := by
  obtain ⟨i, hi, h0⟩ := h₀
  obtain ⟨j, hj, h1⟩ := h₁
  have heq : i = j := Ordinal.ToType.mk.symm.injective (Subtype.ext (hi.trans hj.symm))
  subst j
  exact condition_ne_bot p.point (bot_unique ((le_inf h1 h0).trans inf_compl_eq_bot.le))

def withPoint (p : Condition κ θ) (q : p.Poset) : Condition κ θ := {p with point := q}

theorem withPoint_le (p : Condition κ θ) {q : p.Poset} (hq : q ≤ p.point) : p.withPoint q ≤ p := by
  let π : PartialProjection κ p.Poset p.Poset := PartialProjection.identity
  refine ⟨π, ?_, ?_⟩
  · change condition q ≤ π.booleanHom (condition p.point)
    dsimp only [π]
    rw [PartialProjection.booleanHom_id]
    exact condition_mono hq
  · change condition q ≤ extensionValue π.booleanHom p.name p.name
    dsimp only [π]
    rw [PartialProjection.booleanHom_id]
    exact le_top.trans (extensionValue_refl p.name)

theorem exists_decides_present (p : Condition κ θ) (α : θ.ord.ToType)
    (hα : α.toOrd.val < p.length.toOrd.val) :
    ∃ q : Condition κ θ, q ≤ p ∧ (q.Decides α false ∨ q.Decides α true) := by
  let i : p.length.toOrd.val.ToType := Ordinal.ToType.mk ⟨α.toOrd.val, hα⟩
  have hi : i.toOrd.val = α.toOrd.val := congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
  by_cases hd : condition p.point ⊓ p.bits i = ⊥
  · exact ⟨p, le_rfl, Or.inl ⟨i, hi, le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr hd)⟩⟩
  · obtain ⟨r, hrp, hr⟩ := exists_point_below p.point hd
    exact ⟨p.withPoint r, withPoint_le p hrp, Or.inr ⟨i, hi, hr⟩⟩

def pad (p : Condition κ θ) (l : θ.ord.ToType) (h : p.length.toOrd.val ≤ l.toOrd.val) :
    Condition κ θ := {p with length := l, bits := StringName.padBits h p.bits}

theorem pad_le (p : Condition κ θ) (l : θ.ord.ToType) (h : p.length.toOrd.val ≤ l.toOrd.val) :
    p.pad l h ≤ p := by
  let π : PartialProjection κ p.Poset p.Poset := PartialProjection.identity
  refine ⟨π, ?_, ?_⟩
  · change condition p.point ≤ π.booleanHom (condition p.point)
    dsimp only [π]
    rw [PartialProjection.booleanHom_id]
    exact le_rfl
  · change condition p.point ≤ extensionValue π.booleanHom p.name (StringName.ofBits _ (StringName.padBits h p.bits))
    dsimp only [π]
    rw [PartialProjection.booleanHom_id]
    apply extensionValue_of_bits _ _ _ h
    intro i
    simp only [name, StringName.bits_ofBits, CompleteLatticeHom.id_apply, StringName.padBits_includeIndex]

theorem exists_decides (hθ : Cardinal.aleph0 ≤ θ) (p : Condition κ θ) (α : θ.ord.ToType) :
    ∃ q : Condition κ θ, q ≤ p ∧ (q.Decides α false ∨ q.Decides α true) := by
  by_cases hα : α.toOrd.val < p.length.toOrd.val
  · exact p.exists_decides_present α hα
  · let o := Order.succ α.toOrd.val
    have ho : o < θ.ord := (Cardinal.isSuccLimit_ord hθ).succ_lt α.toOrd.property
    let l : θ.ord.ToType := Ordinal.ToType.mk ⟨o, ho⟩
    have hl : l.toOrd.val = o := congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
    have hi : α.toOrd.val < l.toOrd.val := hl ▸ Order.lt_succ _
    have hp : p.length.toOrd.val ≤ l.toOrd.val := (le_of_not_gt hα).trans hi.le
    obtain ⟨q, hq, hd⟩ := (p.pad l hp).exists_decides_present α hi
    exact ⟨q, hq.trans (p.pad_le l hp), hd⟩

omit [Fact (Cardinal.aleph0 < κ)] in
theorem exists_initial_decision (hθ : Cardinal.aleph0 ≤ θ) (α : θ.ord.ToType) (n : Bool) :
    ∃ p : Condition κ θ, p.Decides α n := by
  obtain ⟨p⟩ := condition_nonempty (κ := κ) (Cardinal.one_lt_aleph0.trans_le hθ)
  let o := Order.succ α.toOrd.val
  have ho : o < θ.ord := (Cardinal.isSuccLimit_ord hθ).succ_lt α.toOrd.property
  let l : θ.ord.ToType := Ordinal.ToType.mk ⟨o, ho⟩
  have hl : l.toOrd.val = o := congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
  have hi : α.toOrd.val < l.toOrd.val := hl ▸ Order.lt_succ _
  let i : l.toOrd.val.ToType := Ordinal.ToType.mk ⟨α.toOrd.val, hi⟩
  let q : Condition κ θ := {p with length := l, bits := fun _ => if n then ⊤ else ⊥}
  refine ⟨q, i, congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _), ?_⟩
  cases n <;> simp [q]

end Condition

variable (κ θ : Cardinal.{u}) [Fact (Cardinal.aleph0 < κ)]

def decisionValue (α : θ.ord.ToType) (n : Bool) : Algebra κ θ :=
  ⨆ p : {p : Condition κ θ // p.Decides α n}, condition p.val

def genericBit (α : θ.ord.ToType) : Algebra κ θ := decisionValue κ θ α true

theorem condition_le_decisionValue {p : Condition κ θ} {α : θ.ord.ToType} {n : Bool}
    (hp : p.Decides α n) : condition p ≤ decisionValue κ θ α n :=
  le_iSup (fun q : {q : Condition κ θ // q.Decides α n} => condition q.val) ⟨p, hp⟩

theorem decisionValue_ne_bot (hθ : Cardinal.aleph0 ≤ θ) (α : θ.ord.ToType) (n : Bool) :
    decisionValue κ θ α n ≠ ⊥ := by
  obtain ⟨p, hp⟩ := Condition.exists_initial_decision (κ := κ) hθ α n
  exact fun he => condition_ne_bot p (bot_unique ((condition_le_decisionValue κ θ hp).trans_eq he))

theorem decisionValues_disjoint (α : θ.ord.ToType) :
    Disjoint (decisionValue κ θ α false) (decisionValue κ θ α true) := by
  apply disjoint_iff_inf_le.mpr
  unfold decisionValue
  rw [iSup_inf_eq]
  apply iSup_le
  intro p
  rw [inf_iSup_eq]
  apply iSup_le
  intro q
  apply le_of_eq
  by_contra h
  obtain ⟨r, hrp, hrq⟩ := (condition_inf_ne_bot_iff p.val q.val).mp h
  exact Condition.opposite_decisions (Condition.decides_mono hrp p.property) (Condition.decides_mono hrq q.property)

theorem decisionValues_cover (hθ : Cardinal.aleph0 ≤ θ) (α : θ.ord.ToType) :
    decisionValue κ θ α false ⊔ decisionValue κ θ α true = ⊤ := by
  let S := {p : Condition κ θ | p.Decides α false ∨ p.Decides α true}
  have hS : ∀ p : Condition κ θ, ∃ q ∈ S, q ≤ p := by
    intro p
    obtain ⟨q, hqp, hq⟩ := Condition.exists_decides hθ p α
    exact ⟨q, hq, hqp⟩
  apply top_unique
  rw [← iSup_condition_eq_top_of_dense S hS]
  apply iSup_le
  intro q
  rcases q.property with h | h
  · exact (condition_le_decisionValue κ θ h).trans le_sup_left
  · exact (condition_le_decisionValue κ θ h).trans le_sup_right

theorem decisionValue_false (hθ : Cardinal.aleph0 ≤ θ) (α : θ.ord.ToType) :
    decisionValue κ θ α false = (genericBit κ θ α)ᶜ :=
  (IsCompl.of_eq (disjoint_iff.mp (decisionValues_disjoint κ θ α)) (decisionValues_cover κ θ hθ α)).eq_compl

/-- At a position of an existing string, the generic bit is forced by
the Shioya condition exactly when its point forces the local bit. -/
theorem condition_le_genericBit_iff (p : Condition κ θ) (i : p.length.toOrd.val.ToType)
    (α : θ.ord.ToType) (hi : i.toOrd.val = α.toOrd.val) :
    condition p ≤ genericBit κ θ α ↔ condition p.point ≤ p.bits i := by
  constructor
  · intro hp
    by_contra h
    have hd : condition p.point ⊓ (p.bits i)ᶜ ≠ ⊥ :=
      fun he => h (disjoint_compl_right_iff.mp (disjoint_iff.mpr he))
    obtain ⟨r, hrp, hr⟩ := exists_point_below p.point hd
    let w := p.withPoint r
    have hw : w.Decides α false := ⟨i, hi, hr⟩
    exact condition_ne_bot w (bot_unique ((le_inf (condition_le_decisionValue κ θ hw)
      ((condition_mono (p.withPoint_le hrp)).trans hp)).trans (disjoint_iff_inf_le.mp (decisionValues_disjoint κ θ α))))
  · intro hp
    exact condition_le_decisionValue κ θ (show p.Decides α true from ⟨i, hi, hp⟩)

theorem condition_le_decisionValue_false_iff (p : Condition κ θ) (i : p.length.toOrd.val.ToType)
    (α : θ.ord.ToType) (hi : i.toOrd.val = α.toOrd.val) :
    condition p ≤ decisionValue κ θ α false ↔ condition p.point ≤ (p.bits i)ᶜ := by
  constructor
  · intro hp
    by_contra h
    have hd : condition p.point ⊓ p.bits i ≠ ⊥ :=
      fun he => h (le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr he))
    obtain ⟨r, hrp, hr⟩ := exists_point_below p.point hd
    let w := p.withPoint r
    have hw : w.Decides α true := ⟨i, hi, hr⟩
    exact condition_ne_bot w (bot_unique ((le_inf ((condition_mono (p.withPoint_le hrp)).trans hp)
      (condition_le_decisionValue κ θ hw)).trans (disjoint_iff_inf_le.mp (decisionValues_disjoint κ θ α))))
  · intro hp
    exact condition_le_decisionValue κ θ (show p.Decides α false from ⟨i, hi, hp⟩)

instance algebraNontrivial [Nonempty (Condition κ θ)] : NontrivialCompleteBooleanAlgebra (Algebra κ θ) where
  toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra
  bot_lt_top := bot_lt_top

def genericString [Nonempty (Condition κ θ)] : StringName (Algebra κ θ) θ.ord :=
  StringName.ofBits θ.ord (genericBit κ θ)

theorem genericString_one [Nonempty (Condition κ θ)] (α : θ.ord.ToType) :
    ((genericString κ θ).bits α) = decisionValue κ θ α true := StringName.bits_ofBits _ _

theorem genericString_zero [Nonempty (Condition κ θ)] (hθ : Cardinal.aleph0 ≤ θ) (α : θ.ord.ToType) :
    (bSet.pair (StringName.label α) (0 : bSet (Algebra κ θ)) ∈ᴮ (genericString κ θ).name) =
      decisionValue κ θ α false := by
  rw [StringName.zero_value, genericString_one, decisionValue_false κ θ hθ]
  rfl

end Erdos1172Shioya
