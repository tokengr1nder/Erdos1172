/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaUniformizationShortReading
public import Erdos1172.Part4ShioyaUniformizationGeneric
public import Erdos1172.Part4BooleanSeedKernelName

@[expose] public section

/-! # Mixed diagrams described by their short restrictions

The candidates range over the internal powerset of the ground stage and
edge labels. For each short subsystem, a local witness specifies its entire
diagram including the designated source points. The witnesses for different
subsystems may be chosen on different refinements.
-/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
open bSet Erdos1172PosetCompletion

universe u
namespace Erdos1172Shioya.Uniformization
namespace MixedDiagram

variable {κ θ : Cardinal.{u}} {I : Type u} [Preorder I]

abbrev Cell (κ θ : Cardinal.{u}) (I : Type u) [Preorder I] :=
  (I × Condition κ θ) ⊕ ({p : I × I // p.1 < p.2} × EdgeData κ θ)

def inDiagram (D : Diagram κ θ I) : Cell κ θ I → Prop
  | .inl (i,p) => D.stage i = p
  | .inr (ij,e) => (⟨D.stage ij.val.1,D.stage ij.val.2,D.edge ij.property⟩ : EdgeData κ θ) = e

def includeCell (x : Set I) : Cell κ θ x → Cell κ θ I
  | .inl (i,p) => .inl (i.val,p)
  | .inr (ij,e) => .inr (⟨(ij.val.1.val,ij.val.2.val),ij.property⟩,e)

def restrict (D : Diagram κ θ I) (x : Set I) : Diagram κ θ x where
  stage i := D.stage i.val
  edge {_ _} h := D.edge h

def code (D : Diagram κ θ I) : PSet.{u} :=
  .mk {a : Cell κ θ I // inDiagram D a} (fun a => (labels (Cell κ θ I)).Func a.val)

theorem inDiagram_include (D : Diagram κ θ I) (x : Set I) (a : Cell κ θ x) :
    inDiagram D (includeCell x a) ↔ inDiagram (restrict D x) a := by
  rcases a with ⟨i,p⟩ | ⟨ij,e⟩ <;> rfl

theorem eq_of_cells {D E : Diagram κ θ I} (h : ∀ a, inDiagram D a ↔ inDiagram E a) :
    D = E := by
  obtain ⟨ds,de⟩ := D
  obtain ⟨es,ee⟩ := E
  have hs : ds = es := funext (fun i => ((h (.inl (i,ds i))).mp rfl).symm)
  subst es
  congr 1
  funext i j hij
  have he := ((h (.inr (⟨(i,j),hij⟩,⟨ds i,ds j,de hij⟩))).mp rfl).symm
  change (⟨ds i,ds j,de hij⟩ : EdgeData κ θ) = ⟨ds i,ds j,ee hij⟩ at he
  simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using he

variable [Fact (Cardinal.aleph0 < κ)] [Nonempty (Condition κ θ)]
local notation "W" => Algebra κ θ

def agrees (x : Set I) (D : Diagram κ θ x) (F : bSet W) : W := by
  classical
  exact ⨅ a : Cell κ θ x,
    let m := check ((labels (Cell κ θ I)).Func (includeCell x a)) ∈ᴮ F
    if inDiagram D a then m else mᶜ

theorem agrees_ext (x : Set I) (D : Diagram κ θ x) : B_ext (agrees x D) := by
  classical
  apply B_ext_iInf
  intro a
  by_cases h : inDiagram D a
  · simp only [if_pos h]
    exact B_ext_mem_right
  · simp only [if_neg h]
    exact B_ext_neg (h := B_ext_mem_right)

/-- Every required stage and repointed source belongs to the same generic. -/
def supported (Coding : Condition κ θ → Prop) (x : Set I)
    (d : {D : Diagram κ θ x // D.Valid Set.univ Coding}) (F : bSet W) : W :=
  (⨅ p : d.val.requirements, condition p.val) ⊓ agrees x d.val F

def shortRestrictions (Coding : Condition κ θ → Prop) (F : bSet W) : W :=
  ⨅ x : {s : Set I // Cardinal.mk s < κ},
    ⨆ d : {D : Diagram κ θ x.val // D.Valid Set.univ Coding}, supported Coding x.val d F

theorem shortRestrictions_ext (Coding : Condition κ θ → Prop) :
    B_ext (shortRestrictions (I := I) Coding) :=
  B_ext_iInf (h := fun x => B_ext_iSup (h := fun d =>
    B_ext_inf B_ext_const (agrees_ext x.val d.val)))

def family (I : Type u) [Preorder I] (Coding : Condition κ θ → Prop) : bSet W :=
  comprehend (shortRestrictions (I := I) Coding) (bv_powerset (check (labels (Cell κ θ I))))

theorem mem_family_iff (Coding : Condition κ θ → Prop) (F : bSet W) {Γ : W} :
    Γ ≤ F ∈ᴮ family I Coding ↔
      Γ ≤ F ⊆ᴮ check (labels (Cell κ θ I)) ∧ Γ ≤ shortRestrictions (I := I) Coding F := by
  unfold family
  rw [ErdosRelationGraph.mem_comprehend_and (shortRestrictions_ext Coding),mem_powerset_iff]

theorem code_mem (D : Diagram κ θ I) (a : Cell κ θ I) :
    (check ((labels (Cell κ θ I)).Func a) ∈ᴮ (check (code D) : bSet W)) =
      @ite W (inDiagram D a) (Classical.propDecidable _) ⊤ ⊥ := by
  classical
  by_cases h : inDiagram D a
  · rw [if_pos h]
    exact top_unique (check_mem (PSet.func_mem (code D) ⟨a,h⟩))
  · rw [if_neg h]
    apply bot_unique
    rw [mem_unfold]
    apply iSup_le
    intro b
    change {t : Cell κ θ I // inDiagram D t} at b
    apply inf_le_right.trans_eq
    apply check_bv_eq_bot_of_not_equiv
    exact fun he => h ((labels_separated _ a b.val he) ▸ b.property)

theorem agrees_ground_restriction (D : Diagram κ θ I) (x : Set I) :
    (⊤ : W) ≤ agrees x (restrict D x) (check (code D)) := by
  classical
  apply le_iInf
  intro a
  dsimp only
  rw [code_mem D (includeCell x a)]
  by_cases h : inDiagram (restrict D x) a
  · simp only [if_pos h, if_pos ((inDiagram_include D x a).mpr h),le_refl]
  · simp only [if_neg h, if_neg (fun k => h ((inDiagram_include D x a).mp k)),compl_bot,le_refl]

theorem agrees_ground_unique (D : Diagram κ θ I) (x : Set I) (E : Diagram κ θ x)
    (hn : agrees x E (check (code D)) ≠ ⊥) : E = restrict D x := by
  classical
  apply eq_of_cells
  intro a
  rw [← inDiagram_include]
  let m := check ((labels (Cell κ θ I)).Func (includeCell x a)) ∈ᴮ (check (code D) : bSet W)
  have ha : agrees x E (check (code D)) ≤ (if inDiagram E a then m else mᶜ) :=
    iInf_le (fun t : Cell κ θ x =>
      let b := check ((labels (Cell κ θ I)).Func (includeCell x t)) ∈ᴮ (check (code D) : bSet W)
      if inDiagram E t then b else bᶜ) a
  have hm := code_mem D (includeCell x a)
  change m = _ at hm
  by_cases h : inDiagram E a <;> by_cases k : inDiagram D (includeCell x a)
  · exact iff_of_true h k
  · simp only [if_pos h] at ha
    simp only [if_neg k] at hm
    exact (hn (bot_unique (ha.trans_eq hm))).elim
  · simp only [if_neg h] at ha
    simp only [if_pos k] at hm
    exact (hn (bot_unique (ha.trans_eq ((congrArg (fun b : W => bᶜ) hm).trans compl_top)))).elim
  · exact iff_of_false h k

/-- A ground diagram whose short subsystems satisfy the lifting condition
and the generic requirements has its literal incidence code in the mixed family. -/
theorem ground_mem_family (Coding : Condition κ θ → Prop) (D : Diagram κ θ I)
    {Γ : W} (h : ∀ x : Set I, Cardinal.mk x < κ →
      (restrict D x).Valid {s | Γ ≤ condition s} Coding) :
    Γ ≤ check (code D) ∈ᴮ family I Coding := by
  apply (mem_family_iff Coding _).mpr
  constructor
  · rw [subset_unfold]
    apply le_iInf
    intro a
    rw [← deduction]
    change {t : Cell κ θ I // inDiagram D t} at a
    exact le_top.trans (check_mem (PSet.func_mem (labels (Cell κ θ I)) a.val))
  · apply le_iInf
    intro x
    let D' := restrict D x.val
    have hd := h x.val x.property
    let d : {v : Diagram κ θ x.val // v.Valid Set.univ Coding} :=
      ⟨D',hd.1,Set.subset_univ _,hd.2.2⟩
    apply le_iSup_of_le d
    exact le_inf (le_iInf fun t : D'.requirements => (show Γ ≤ condition t.val from hd.2.1 t.property))
      (le_top.trans (agrees_ground_restriction D x.val))

theorem ground_mem_family_iff (Coding : Condition κ θ → Prop) (D : Diagram κ θ I)
    {Γ : W} (hn : Γ ≠ ⊥) :
    Γ ≤ check (code D) ∈ᴮ family I Coding ↔
      ∀ x : Set I, Cardinal.mk x < κ → (restrict D x).Valid {s | Γ ≤ condition s} Coding := by
  classical
  refine ⟨?_,ground_mem_family Coding D⟩
  intro h x hx
  let s : {s : Set I // Cardinal.mk s < κ} := ⟨x,hx⟩
  let V := {E : Diagram κ θ x // E.Valid Set.univ Coding}
  let v (d : V) := supported Coding x d (check (code D))
  have hs : Γ ≤ ⨆ d, v d := ((mem_family_iff _ _).mp h).2.trans (iInf_le _ s)
  have he (d : V) (hd : v d ≠ ⊥) : d.val = restrict D x :=
    agrees_ground_unique D x d.val (fun hz => hd (bot_unique (inf_le_right.trans_eq hz)))
  obtain ⟨d,hd⟩ : ∃ d : V, v d ≠ ⊥ := by
    by_contra! hm
    exact hn (bot_unique (hs.trans (iSup_le fun d => (hm d).le)))
  have hstat : (restrict D x).Valid Set.univ Coding := he d hd ▸ d.property
  refine ⟨hstat.1,?_,hstat.2.2⟩
  intro p hp
  apply hs.trans
  apply iSup_le
  intro b
  by_cases hb : v b = ⊥
  · exact hb.le.trans bot_le
  · have hin : p ∈ b.val.requirements := (he b hb).symm ▸ hp
    exact inf_le_left.trans (iInf_le (fun q : b.val.requirements => condition q.val) ⟨p,hin⟩)

/-- Membership is equivalent to covering each short restriction by genuine
ground valid diagrams at refinements of every starting condition. -/
theorem condition_mem_family_iff (Coding : Condition κ θ → Prop) (F : bSet W) (p : Condition κ θ) :
    condition p ≤ F ∈ᴮ family I Coding ↔
      condition p ≤ F ⊆ᴮ check (labels (Cell κ θ I)) ∧
      ∀ (x : Set I), Cardinal.mk x < κ → ∀ r ≤ p, ∃ q ≤ r, ∃ D : Diagram κ θ x,
        D.Valid {s | condition q ≤ condition s} Coding ∧ condition q ≤ agrees x D F := by
  rw [mem_family_iff]
  refine and_congr_right fun _ => ⟨?_,?_⟩
  · intro hf x hx r hr
    let s : {s : Set I // Cardinal.mk s < κ} := ⟨x,hx⟩
    have hs := (condition_mono hr).trans (hf.trans (iInf_le _ s))
    obtain ⟨q,hqr,d,hd⟩ := choose_below r (fun d => supported Coding x d F) hs
    exact ⟨q,hqr,d.val,⟨d.property.1,fun u hu =>
      (hd.trans inf_le_left).trans (iInf_le
        (fun t : d.val.requirements => condition t.val) ⟨u,hu⟩),d.property.2.2⟩,hd.trans inf_le_right⟩
  · intro h
    apply le_iInf
    intro x
    apply cone_le_of_refinements
    intro r hr
    obtain ⟨q,hqr,D,hd,hagree⟩ := h x.val x.property r hr
    let d : {D : Diagram κ θ x.val // D.Valid Set.univ Coding} :=
      ⟨D,hd.1,Set.subset_univ _,hd.2.2⟩
    exact ⟨q,hqr,le_iSup_of_le d (le_inf (le_iInf fun t : D.requirements =>
      (show condition q ≤ condition t.val from hd.2.1 t.property)) hagree)⟩

end MixedDiagram
end Erdos1172Shioya.Uniformization
