/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingOverBase
public import Erdos1172.Part4CollapseName

@[expose] public section

/-! # A collapse name for a cofinal sequence of coherent stage isomorphisms -/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open Cardinal Erdos1172PositiveBoolean Erdos1172PosetCompletion Erdos1172Collapse
open bSet bSet.ErdosCountableMatrix bSet.ErdosOmegaSequence Lattice
open scoped Flypitch
universe u
namespace Erdos1172LevyCollapse.Matching

variable {X S : Type u}

def wordWeight (n : ℕ) (p : Condition X) : Algebra X :=
  if p.entries.length = n then condition p else ⊥

private theorem weights_disjoint (n : ℕ) (p q : Condition X) (h : p ≠ q) :
    wordWeight n p ⊓ wordWeight n q = ⊥ := by
  classical
  unfold wordWeight
  split_ifs with hp hq <;> try exact bot_unique inf_le_right
  all_goals try exact bot_unique inf_le_left
  by_contra hn
  obtain ⟨r,hrp,hrq⟩ := (condition_inf_ne_bot_iff p q).mp hn
  rcases List.prefix_or_prefix_of_prefix hrp hrq with hpq | hqp
  · exact h (Condition.ext (hpq.eq_of_length (hp.trans hq.symm)))
  · exact h (Condition.ext (hqp.eq_of_length (hq.trans hp.symm)).symm)

private theorem covers [Nonempty X] (n : ℕ) (b : Algebra X)
    (h : ∀ p : Condition X, p.entries.length = n → condition p ≤ b) : ⊤ ≤ b := by
  rw [← iSup_condition_eq_top_of_dense (lengthDense (α := X) n)
    (fun p => by obtain ⟨q,hq,hl⟩ := lengthDense_dense n p; exact ⟨q,hl,hq⟩)]
  apply iSup_le
  intro p
  let q : Condition X := ⟨p.val.entries.take n⟩
  exact (condition_mono (show p.val ≤ q from List.take_prefix _ _)).trans
    (h q (by simpa [q] using Nat.min_eq_left p.property))

def values (run : Condition X → S) (label : S → bSet (Algebra X)) (n : ℕ) :=
  rowName wordWeight (fun p => label (run p)) n

private theorem value_at (run : Condition X → S) (label : S → bSet (Algebra X))
    (p : Condition X) (n : ℕ) (hn : p.entries.length = n) :
    condition p ≤ values run label n =ᴮ label (run p) := by
  simpa only [wordWeight, if_pos hn, values] using
    rowName_agrees wordWeight (fun p => label (run p)) weights_disjoint n p

def related (label : S → bSet (Algebra X)) (R : S → S → Prop)
    (x y : bSet (Algebra X)) : Algebra X :=
  ⨆ t : {t : S × S // R t.1 t.2}, (x =ᴮ label t.val.1) ⊓ (y =ᴮ label t.val.2)

private theorem exists_sequence [Nonempty X] (run : Condition X → S)
    (label : S → bSet (Algebra X)) (R : S → S → Prop) (above : X → S → Prop)
    (hmono : ∀ p q : Condition X, q ≤ p → R (run p) (run q))
    (habove : ∀ (p : Condition X) x, above x (run (extend p [x]))) :
    ∃ f : bSet (Algebra X), (⊤ : Algebra X) ≤ pair (of_nat 0) (label (run ⟨[]⟩)) ∈ᴮ f ∧
      (⊤ : Algebra X) ≤ is_function omega (check'' label) f ∧
      (∀ {Γ : Algebra X} {i j x y : bSet (Algebra X)}, Γ ≤ i ∈ᴮ j →
        Γ ≤ pair i x ∈ᴮ f → Γ ≤ pair j y ∈ᴮ f → Γ ≤ related label R x y) ∧
      ∀ i : X, (⊤ : Algebra X) ≤ ⨆ n : ℕ, ⨆ z : {s : S // above i s},
        pair (of_nat n) (label z.val) ∈ᴮ f := by
  classical
  let v := values run label
  refine ⟨sequenceGraph v,?_,sequenceGraph_is_function (fun n => covers n _ ?_),?_,?_⟩
  · apply covers 0
    intro p hp
    have eq : p = ⟨[]⟩ := Condition.ext (List.length_eq_zero_iff.mp hp)
    subst p
    exact pair_of_nat_mem_iff.mpr (bv_symm (value_at run label ⟨[]⟩ 0 rfl))
  · intro p hp
    apply bv_rw' (value_at run label p n hp) (h_congr := B_ext_mem_left)
    exact le_top.trans (mem_mk' (check'' label) (run p))
  · intro Γ i j x y hij hix hjy
    apply relation_of_sequenceGraph_pairs (P := related label R)
      (fun _ => B_ext_iSup (h := fun _ => B_ext_inf B_ext_bv_eq_left B_ext_const))
      (fun _ => B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_bv_eq_left))
      _ hij hix hjy
    intro m n hmn
    apply le_top.trans (covers n _ ?_)
    intro p hp
    let q : Condition X := ⟨p.entries.take m⟩
    have hq : p ≤ q := List.take_prefix _ _
    have len : q.entries.length = m := by simp [q,hp,Nat.min_eq_left hmn.le]
    exact le_iSup_of_le ⟨(run q,run p),hmono q p hq⟩
      (le_inf ((condition_mono hq).trans (value_at run label q m len)) (value_at run label p n hp))
  · intro i
    let D : Set (Condition X) := {q | above i (run q)}
    rw [← iSup_condition_eq_top_of_dense D (fun p => ⟨extend p [i],habove p i,extend_le _ _⟩)]
    apply iSup_le
    intro p
    apply le_iSup_of_le p.val.entries.length
    apply le_iSup_of_le ⟨run p.val,p.property⟩
    exact pair_of_nat_mem_iff.mpr (bv_symm (value_at run label p.val _ rfl))

variable {J : Type u} [Preorder J] (B C : J → Type u)
  [∀ j, NontrivialCompleteBooleanAlgebra (B j)] [∀ j, NontrivialCompleteBooleanAlgebra (C j)]

/-- A single ground matching of corresponding stages. -/
abbrev StageMatch := Σ j : J, B j ≃o C j

/-- A ground ordinal label for the stage together with its entire matching map. -/
def stageCode (s : StageMatch B C) : PSet.{u} :=
  let e := (Cardinal.eq.mp (Cardinal.mk_ord_toType #(StageMatch B C)).symm).some
  PSet.ordinalMk (e s).toOrd.val

omit [Preorder J] in
theorem stageCode_separated (s t : StageMatch B C)
    (h : PSet.Equiv (stageCode B C s) (stageCode B C t)) : s = t := by
  let e := (Cardinal.eq.mp (Cardinal.mk_ord_toType #(StageMatch B C)).symm).some
  have he : (e s).toOrd.val = (e t).toOrd.val := PSet.eq_of_mk_equiv h
  exact e.injective (Ordinal.ToType.mk.symm.injective (Subtype.ext he))

variable (b : ∀ {i j : J}, i ≤ j → CompleteLatticeHom (B i) (B j))
  (c : ∀ {i j : J}, i ≤ j → CompleteLatticeHom (C i) (C j))

/-- The commuting square on the whole earlier algebra. -/
def ExtendsMatch (s t : StageMatch B C) : Prop :=
  ∃ h : s.1 ≤ t.1, ∀ x, t.2 (b h x) = c h (s.2 x)

/-- Ground data for a sufficiently late pair of collapsing stages.
Only densities, regularity, and the forced countability of the matching cardinal are required. -/
structure CollapsingPair (i t : J) where
  stage : J
  prev : i ≤ stage
  reaches : t ≤ stage
  μ : Cardinal.{u}
  uncountable : ℵ₀ < μ
  regular : μ.IsRegular
  K : Type u
  oldDense : K → Positive (B i)
  small : #K < μ
  coversOld : ∀ a, ∃ k, oldDense k ≤ a
  leftDense : μ.ord.ToType → Positive (B stage)
  coversLeft : ∀ a, ∃ k, leftDense k ≤ a
  rightDense : μ.ord.ToType → Positive (C stage)
  coversRight : ∀ a, ∃ k, rightDense k ≤ a
  collapseLeft : (⊤ : B stage) ≤ injects_into (check (PSet.ordinalMk μ.ord)) omega
  collapseRight : (⊤ : C stage) ≤ injects_into (check (PSet.ordinalMk μ.ord)) omega

variable {B C}

private theorem advance (hb : ∀ {i j} (h : i ≤ j), Function.Injective (b h))
    (hc : ∀ {i j} (h : i ≤ j), Function.Injective (c h))
    (pairing : ∀ i t, CollapsingPair B C i t) (s : StageMatch B C) (t : J) :
    ∃ v : StageMatch B C, ExtendsMatch B C b c s v ∧ t ≤ v.1 := by
  let P := pairing s.1 t
  let φ := CompleteLatticeHom.OrderIso.toCompleteLatticeHom s.2
  obtain ⟨ψ,hψ⟩ := exists_stage_amalgamation (b P.prev) (hb P.prev) ((c P.prev).comp φ)
    ((hc P.prev).comp s.2.injective) P.μ P.uncountable P.regular P.oldDense P.small
    P.coversOld P.leftDense P.coversLeft P.rightDense P.coversRight P.collapseLeft P.collapseRight
  exact ⟨⟨P.stage,ψ⟩,⟨P.prev,hψ⟩,P.reaches⟩

/-- In the further finite-word collapse of the ground stage index there is a
single Boolean function on omega whose values are ground stage matches, which
commute on every earlier selected stage and reach each ground stage. -/
theorem exists_external_matching_sequence_from
    (hb : ∀ {i j} (h : i ≤ j), Function.Injective (b h))
    (hc : ∀ {i j} (h : i ≤ j), Function.Injective (c h))
    (bid : ∀ i (x : B i), b (le_refl i) x = x)
    (cid : ∀ i (x : C i), c (le_refl i) x = x)
    (bcomp : ∀ {i j k} (h : i ≤ j) (h' : j ≤ k) x, b (h.trans h') x = b h' (b h x))
    (ccomp : ∀ {i j k} (h : i ≤ j) (h' : j ≤ k) x, c (h.trans h') x = c h' (c h x))
    (pairing : ∀ i t, CollapsingPair B C i t) (start : StageMatch B C) :
    ∃ f : bSet (Algebra J), (⊤ : Algebra J) ≤ pair (of_nat 0) (check (stageCode B C start)) ∈ᴮ f ∧
      (⊤ : Algebra J) ≤ is_function omega (check (.mk (StageMatch B C) (stageCode B C))) f ∧
      (∀ {Γ : Algebra J} {i j x y : bSet (Algebra J)}, Γ ≤ i ∈ᴮ j →
        Γ ≤ pair i x ∈ᴮ f → Γ ≤ pair j y ∈ᴮ f →
        Γ ≤ ⨆ v : {v : StageMatch B C × StageMatch B C // ExtendsMatch B C b c v.1 v.2},
          (x =ᴮ check (stageCode B C v.val.1)) ⊓ (y =ᴮ check (stageCode B C v.val.2))) ∧
      ∀ i : J, (⊤ : Algebra J) ≤ ⨆ n : ℕ, ⨆ v : {v : StageMatch B C // i ≤ v.1},
        pair (of_nat n) (check (stageCode B C v.val)) ∈ᴮ f := by
  classical
  have : Nonempty J := ⟨start.1⟩
  let next (s : StageMatch B C) (t : J) := (advance b c hb hc pairing s t).choose
  have step (s : StageMatch B C) (t : J) : ExtendsMatch B C b c s (next s t) ∧ t ≤ (next s t).1 :=
    (advance b c hb hc pairing s t).choose_spec
  let run (p : Condition J) := p.entries.foldl next start
  rw [check_unfold (x := PSet.mk (StageMatch B C) (stageCode B C))]
  apply exists_sequence run (fun s => check (stageCode B C s)) (ExtendsMatch B C b c) (fun i s => i ≤ s.1)
  · intro p q h
    obtain ⟨l,rfl⟩ := le_iff_exists_extend.mp h
    clear h
    change ExtendsMatch B C b c (run p) ((p.entries ++ l).foldl next start)
    rw [List.foldl_append]
    suffices ∀ s : StageMatch B C, ExtendsMatch B C b c s (l.foldl next s) from this _
    induction l with
    | nil =>
      intro s
      change ExtendsMatch B C b c s s
      exact ⟨le_rfl, fun x => (congrArg s.2 (bid _ x)).trans (cid _ _).symm⟩
    | cons t l ih =>
      intro s
      obtain ⟨h,hh⟩ := (step s t).1
      obtain ⟨h',hh'⟩ := ih (next s t)
      change ExtendsMatch B C b c s (l.foldl next (next s t))
      exact ⟨h.trans h', fun x => (congrArg (l.foldl next (next s t)).2 (bcomp h h' x)).trans
        ((hh' _).trans ((congrArg (c h') (hh x)).trans (ccomp h h' _).symm))⟩
  · intro p x
    simpa [run,extend,List.foldl_append] using (step (run p) x).2

end Erdos1172LevyCollapse.Matching
