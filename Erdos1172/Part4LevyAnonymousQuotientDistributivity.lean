/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyAnonymousPartitionRefinement
public import Erdos1172.Part4BooleanQuotientFactorization

@[expose] public section

/-!
# Countable intersections of weighted dense opens in the anonymous quotient

Membership of a target label in an open set carries a source Boolean value.
The separative comparison of labels `q` and `p` excludes the lower
projection of `q ⊓ pᶜ`. Disjoint refinements and simultaneous anonymous
reading yield one condition locally belonging to every dense open.
-/

set_option autoImplicit false
noncomputable section

universe u v

namespace Erdos1172LevyCohen

open Erdos1172PositiveBoolean Erdos1172BooleanFactor Erdos1172CompleteSubalgebra

theorem disjoint_cover_refinement {C I : Type u} [CompleteBooleanAlgebra C]
    (a : I → C) :
    ∃ w : I → C, (∀ i, w i ≤ a i) ∧
      (∀ i j, i ≠ j → w i ⊓ w j = ⊥) ∧ (⨆ i, w i) = ⨆ i, a i := by
  classical
  obtain ⟨_lo, wf⟩ := exists_wellFoundedLT I
  letI := _lo
  haveI : WellFoundedLT (I) := wf
  let past := fun i : I => ⨆ j : {j : I // j < i}, a j.val
  let w := fun i => a i ⊓ (past i)ᶜ
  have hd {i j : I} (h : i < j) : w i ⊓ w j = ⊥ := by
    have hl : w i ≤ past j := inf_le_left.trans (le_iSup (fun k : {k : I // k < j} => a k.val) ⟨i, h⟩)
    exact bot_unique ((inf_le_inf hl (show w j ≤ (past j)ᶜ from inf_le_right)).trans
      inf_compl_eq_bot.le)
  refine ⟨w, fun _ => inf_le_left, ?_, le_antisymm (iSup_mono (fun _ => inf_le_left)) ?_⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hd h
    · exact (inf_comm _ _).trans (hd h)
  · apply iSup_le
    intro i
    apply wf.induction i
    intro j ih
    calc
      a j = a j ⊓ past j ⊔ w j := by
        change a j = a j ⊓ past j ⊔ a j ⊓ (past j)ᶜ
        rw [← inf_sup_left, sup_compl_eq_top, inf_top_eq]
      _ ≤ ⨆ k, w k := sup_le
        (inf_le_right.trans (iSup_le fun k : {k : I // k < j} => ih k.val k.property))
        (le_iSup w j)

section General

variable {B C : Type u} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

private theorem weighted_dense_ambient_cover (e : CompleteLatticeHom B C) (D : Positive C → B)
    (Hvalid : ∀ p, D p ≤ lowerProjection e p.val)
    (Hdense : ∀ p : Positive C, lowerProjection e p.val ≤
      ⨆ q : {q : Positive C // q ≤ p}, D q.val) :
    (⨆ q : Positive C, q.val ⊓ e (D q)) = ⊤ := by
  classical
  let x := ⨆ q : Positive C, q.val ⊓ e (D q)
  change x = ⊤
  by_contra hx
  let p : Positive C := ⟨xᶜ, fun hz => hx (compl_eq_bot.mp hz)⟩
  obtain ⟨q, hq⟩ : ∃ q : {q : Positive C // q ≤ p}, D q.val ≠ ⊥ := by
    by_contra! h
    exact lowerProjection_ne_bot e p.property
      (bot_unique ((Hdense p).trans (iSup_le fun q => (h q).le)))
  have hpos := inf_image_lowerProjection_ne_bot e hq (Hvalid q.val)
  apply hpos
  have h1 : e (D q.val) ⊓ q.val.val ≤ x :=
    (inf_comm _ _).le.trans (le_iSup (fun r : Positive C => r.val ⊓ e (D r)) q.val)
  have h2 : e (D q.val) ⊓ q.val.val ≤ xᶜ :=
    inf_le_right.trans (show q.val.val ≤ xᶜ from q.property)
  exact bot_unique ((le_inf h1 h2).trans inf_compl_eq_bot.le)

private theorem weighted_separative_piece (e : CompleteLatticeHom B C) (D : Positive C → B)
    (Hopen : ∀ p q : Positive C,
      D p ⊓ lowerProjection e q.val ⊓ (lowerProjection e (q.val ⊓ p.valᶜ))ᶜ ≤ D q)
    (d q : Positive C) (b : B) (h : d.val ⊓ e b ≤ q.val ⊓ e (D q)) :
    lowerProjection e d.val ⊓ b ≤ D d := by
  have hmember : lowerProjection e d.val ⊓ b ≤ D q := by
    rw [← lowerProjection_inf_image]
    exact lowerProjection_le e (h.trans inf_le_right)
  have hz : (d.val ⊓ q.valᶜ) ⊓ e b = ⊥ := by
    apply bot_unique
    have hle : (d.val ⊓ q.valᶜ) ⊓ e b ≤ q.val :=
      ((le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans h).trans inf_le_left
    exact (le_inf hle (inf_le_left.trans inf_le_right)).trans inf_compl_eq_bot.le
  have hzero : lowerProjection e (d.val ⊓ q.valᶜ) ⊓ b = ⊥ := by
    rw [← lowerProjection_inf_image, hz]
    exact bot_unique (lowerProjection_le e bot_le)
  have hsep : b ≤ (lowerProjection e (d.val ⊓ q.valᶜ))ᶜ :=
    le_compl_iff_disjoint_left.mpr (disjoint_iff.mpr hzero)
  exact (le_inf (le_inf hmember inf_le_left) (inf_le_right.trans hsep)).trans (Hopen q d)

/-- Density of positive target representatives on which a property holds
at the full projected support gives source-valued density. -/
private theorem weighted_density_of_master (e : CompleteLatticeHom B C) (V : Positive C → B)
    (Hmaster : ∀ r : Positive C, ∃ d : Positive C, d ≤ r ∧ lowerProjection e d.val ≤ V d)
    (p : Positive C) :
    lowerProjection e p.val ≤ ⨆ q : {q : Positive C // q ≤ p}, V q.val := by
  classical
  let x := ⨆ q : {q : Positive C // q ≤ p}, V q.val
  change lowerProjection e p.val ≤ x
  by_contra hp
  have hn : lowerProjection e p.val ⊓ xᶜ ≠ ⊥ := by
    intro h
    exact hp (disjoint_compl_right_iff.mp (disjoint_iff.mpr h))
  let w := lowerProjection e p.val ⊓ xᶜ
  let r : Positive C := ⟨e w ⊓ p.val,
    inf_image_lowerProjection_ne_bot e hn inf_le_left⟩
  obtain ⟨d, hdr, hdV⟩ := Hmaster r
  have hd : d.val ≤ e w ⊓ p.val := hdr
  have h1 : lowerProjection e d.val ≤ x := hdV.trans
    (le_iSup (fun q : {q : Positive C // q ≤ p} => V q.val) ⟨d, hd.trans inf_le_right⟩)
  have h2 : lowerProjection e d.val ≤ xᶜ :=
    (lowerProjection_le e (hd.trans inf_le_left)).trans inf_le_right
  exact lowerProjection_ne_bot e d.property
    (bot_unique ((le_inf h1 h2).trans inf_compl_eq_bot.le))

/-- Simultaneous reading of disjoint partitions yields density of the
intersection of a family of quotient dense opens with the same index type. -/
theorem weighted_dense_intersection_of_partitions {I : Type v} (e : CompleteLatticeHom B C)
    (readPartitions : ∀ (w : I → Positive C → C) (r : Positive C),
      (∀ n i j, i ≠ j → w n i ⊓ w n j = ⊥) → (∀ n, r.val ≤ ⨆ i, w n i) →
      ∃ (d : C) (s : B) (b : I → Positive C → B), d ≠ ⊥ ∧ d ≤ r.val ∧ d ≤ e s ∧
        (∀ n, (⨆ i, b n i) = s) ∧ ∀ n i, d ⊓ e (b n i) = d ⊓ w n i)
    (D : I → Positive C → B) (Hvalid : ∀ n p, D n p ≤ lowerProjection e p.val)
    (Hopen : ∀ n (p q : Positive C), D n p ⊓ lowerProjection e q.val ⊓
      (lowerProjection e (q.val ⊓ p.valᶜ))ᶜ ≤ D n q)
    (Hdense : ∀ n (p : Positive C), lowerProjection e p.val ≤
      ⨆ q : {q : Positive C // q ≤ p}, D n q.val) (p : Positive C) :
    lowerProjection e p.val ≤ ⨆ q : {q : Positive C // q ≤ p}, ⨅ n, D n q.val := by
  classical
  let a := fun n (q : Positive C) => q.val ⊓ e (D n q)
  have Htotal : ∀ n, (⨆ q, a n q) = ⊤ :=
    fun n => weighted_dense_ambient_cover e (D n) (Hvalid n) (Hdense n)
  choose w hwle hwdisj hwcov using fun n => disjoint_cover_refinement (a n)
  apply weighted_density_of_master e (fun q => ⨅ n, D n q) _ p
  intro r
  have Hcov : ∀ n, r.val ≤ ⨆ q, w n q := fun n =>
    le_top.trans_eq ((hwcov n).trans (Htotal n)).symm
  obtain ⟨d, s, b, hd, hdr, hds, hrows, hmatch⟩ := readPartitions w r hwdisj Hcov
  let d' : Positive C := ⟨d, hd⟩
  refine ⟨d', hdr, le_iInf fun n => ?_⟩
  have hu : lowerProjection e d ≤ s := lowerProjection_le e hds
  calc
    lowerProjection e d = lowerProjection e d ⊓ (⨆ q, b n q) := by
      rw [hrows n]
      exact (inf_eq_left.mpr hu).symm
    _ = ⨆ q, lowerProjection e d ⊓ b n q := inf_iSup_eq _ _
    _ ≤ D n d' := by
      apply iSup_le
      intro q
      apply weighted_separative_piece e (D n) (Hopen n) d' q (b n q)
      exact (hmatch n q).le.trans (inf_le_right.trans (hwle n q))

end General

/-- A countable intersection of separatively open dense source-valued
families is dense in the quotient on every positive label. -/
theorem anonymous_quotient_countable_distributivity (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ)
    (D : ℕ → Positive (Algebra κ) → anonymousAlgebra κ)
    (Hvalid : ∀ n p, D n p ≤ lowerProjection (inclusion (anonymousAlgebra κ)) p.val)
    (Hopen : ∀ n (p q : Positive (Algebra κ)),
      D n p ⊓ lowerProjection (inclusion (anonymousAlgebra κ)) q.val ⊓
        (lowerProjection (inclusion (anonymousAlgebra κ)) (q.val ⊓ p.valᶜ))ᶜ ≤ D n q)
    (Hdense : ∀ n (p : Positive (Algebra κ)),
      lowerProjection (inclusion (anonymousAlgebra κ)) p.val ≤
        ⨆ q : {q : Positive (Algebra κ) // q ≤ p}, D n q.val)
    (p : Positive (Algebra κ)) :
    lowerProjection (inclusion (anonymousAlgebra κ)) p.val ≤
      ⨆ q : {q : Positive (Algebra κ) // q ≤ p}, ⨅ n, D n q.val := by
  apply weighted_dense_intersection_of_partitions (I := ℕ) (inclusion (anonymousAlgebra κ)) _ D Hvalid Hopen Hdense p
  intro w r hdisj hcov
  obtain ⟨d,s,b,hd,hdr,_,hds,hrows,_,hmatch⟩ :=
    exists_anonymous_indexed_partition_refinement κ Hκ Hunc _ w r.val r.property hdisj hcov
  exact ⟨d,s,b,hd,hdr,hds,hrows,hmatch⟩

end Erdos1172LevyCohen
