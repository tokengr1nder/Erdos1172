/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalNamedOrder
public import Erdos1172.Part4ShioyaInternalSingletonOrder

@[expose] public section

/-! # Extending an arbitrary named Shioya word with mixed regular columns -/

set_option autoImplicit false
set_option maxHeartbeats 750000
noncomputable section
open scoped Flypitch
open Lattice
universe u
namespace bSet.ErdosShioyaInternal
open ErdosRelationGraph
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

private theorem someIn_iff {P : N} {f : N → B} {Γ : B} (ext : B_ext f) :
    Γ ≤ someIn P f ↔ ∃ p : N, Γ ≤ p ∈ᴮ P ∧ Γ ≤ f p := by
  constructor
  · intro h
    obtain ⟨p,hp⟩ := exists_convert h (B_ext_inf B_ext_mem_left ext)
    exact ⟨p,hp.trans inf_le_left,hp.trans inf_le_right⟩
  · rintro ⟨p,hm,hf⟩
    exact le_iSup_of_le p (le_inf hm hf)

private theorem denseColumn_iff {Γ : B} {P R b i p : N} :
    Γ ≤ denseBelowColumn P R b i p ↔ ∀ {Δ : B}, Δ ≤ Γ → ∀ {q : N}, Δ ≤ q ∈ᴮ P → Δ ≤ edge R q p →
      ∃ t : N, Δ ≤ t ∈ᴮ P ∧ Δ ≤ edge R t q ∧ Δ ≤ edge b t i := by
  constructor
  · intro h Δ hd q hq hqp
    obtain ⟨t,ht,hv⟩ := (someIn_iff (B_ext_inf B_ext_pair_mem_left B_ext_pair_mem_left)).mp
      (projection_imp.mp (allIn_elim (hd.trans h) hq) Δ le_rfl hqp)
    exact ⟨t,ht,hv.trans inf_le_left,hv.trans inf_le_right⟩
  · intro h
    apply allIn_intro
    intro Δ hd q hq
    apply projection_imp.mpr
    intro z hz hqp
    obtain ⟨t,ht,hx,hy⟩ := h (hz.trans hd) (hz.trans hq) hqp
    exact le_iSup_of_le t (le_inf ht (le_inf hx hy))

/-- Two columns with the same incidence at all supported points on every subguard have
the same regularity there. The two indices may belong to different words. -/
theorem regularColumn_of_agree {Γ : B} {P R a b i j : N} (reg : Γ ≤ regularColumnValue P R a i)
    (agrees : ∀ {Δ : B}, Δ ≤ Γ → ∀ {x : N}, Δ ≤ x ∈ᴮ P → (Δ ≤ edge a x i ↔ Δ ≤ edge b x j)) :
    Γ ≤ regularColumnValue P R b j := by
  apply le_inf
  · apply allIn_intro
    intro Δ hd p hp
    apply allIn_intro
    intro z hz q hq
    apply projection_imp.mpr
    intro t ht h
    have base := (ht.trans hz).trans hd
    have hp' := (ht.trans hz).trans hp
    have hq' := ht.trans hq
    have down := allIn_elim (allIn_elim (base.trans (reg.trans inf_le_left)) hp') hq'
    exact (agrees base hp').mp (projection_imp.mp down t le_rfl
      (le_inf (h.trans inf_le_left) ((agrees base hq').mpr (h.trans inf_le_right))))
  · apply allIn_intro
    intro Δ hd p hp
    apply projection_imp.mpr
    intro z hz den
    have base := hz.trans hd
    apply (agrees base (hz.trans hp)).mp
    apply projection_imp.mp (allIn_elim (base.trans (reg.trans inf_le_right)) (hz.trans hp)) z le_rfl
    apply denseColumn_iff.mpr
    intro t ht q hq hqp
    obtain ⟨v,hv,hvq,hb⟩ := denseColumn_iff.mp den ht hq hqp
    exact ⟨v,hv,hvq,(agrees (ht.trans base) hv).mpr hb⟩

/-- Any subset of the column index set gives a family of mixed constant columns on
an arbitrary reflexive order. -/
theorem constant_regularColumns {Γ : B} {P R L : N} (reg : Γ ≤ partialOrderValue P R) (Z : N)
    (hZ : Γ ≤ Z ⊆ᴮ L) : Γ ≤ regularColumnsValue P R L (prod P Z) := by
  refine le_inf (ErdosIndependentHomogeneous.prod_codomain_mono hZ) (allIn_intro ?_)
  intro Δ hd i _
  apply le_inf
  · apply allIn_intro
    intro b _ p hp
    apply allIn_intro
    intro c hc _ _
    apply projection_imp.mpr
    intro d dh h
    exact mem_prod ((dh.trans hc).trans hp) (mem_prod_iff.mp (h.trans inf_le_right)).2
  · apply allIn_intro
    intro b hb p hp
    apply projection_imp.mpr
    intro c hc den
    have hp' := hc.trans hp
    have refl := allIn_elim (((hc.trans hb).trans hd).trans (reg.trans (inf_le_right.trans inf_le_left))) hp'
    obtain ⟨_,_,_,bit⟩ := denseColumn_iff.mp den le_rfl hp' refl
    exact mem_prod hp' (mem_prod_iff.mp bit).2

def overlayBits (P L old a b : N) : N := relationGraph P L (fun p i =>
  ((i ∈ᴮ old) ⊓ edge a p i) ⊔ ((i ∈ᴮ old)ᶜ ⊓ edge b p i))

private theorem overlay_iff {Γ : B} {P L old a b p i : N} :
    Γ ≤ edge (overlayBits P L old a b) p i ↔ Γ ≤ p ∈ᴮ P ∧ Γ ≤ i ∈ᴮ L ∧
      Γ ≤ ((i ∈ᴮ old) ⊓ edge a p i) ⊔ ((i ∈ᴮ old)ᶜ ⊓ edge b p i) :=
  mem_relationGraph_iff (fun _ => B_ext_sup (h₁ := B_ext_inf B_ext_const B_ext_pair_mem_left)
    (h₂ := B_ext_inf B_ext_const B_ext_pair_mem_left)) (fun _ => B_ext_sup (h₁ := B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
      (h₂ := B_ext_inf (B_ext_neg (h := B_ext_mem_left)) B_ext_pair_mem_right))

theorem overlay_old {Γ : B} {P L old a b p i : N} (hp : Γ ≤ p ∈ᴮ P) (hi : Γ ≤ i ∈ᴮ L) (ho : Γ ≤ i ∈ᴮ old) :
    Γ ≤ edge (overlayBits P L old a b) p i ↔ Γ ≤ edge a p i := by
  constructor
  · intro h
    apply (le_inf ho (overlay_iff.mp h).2.2).trans
    rw [inf_sup_left]
    apply sup_le (inf_le_right.trans inf_le_right)
    exact ((le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans inf_compl_eq_bot.le).trans bot_le
  · intro h
    exact overlay_iff.mpr ⟨hp,hi,(le_inf ho h).trans le_sup_left⟩

theorem overlay_fresh {Γ : B} {P L old a b p i : N} (hp : Γ ≤ p ∈ᴮ P) (hi : Γ ≤ i ∈ᴮ L) (ho : Γ ≤ (i ∈ᴮ old)ᶜ) :
    Γ ≤ edge (overlayBits P L old a b) p i ↔ Γ ≤ edge b p i := by
  constructor
  · intro h
    apply (le_inf ho (overlay_iff.mp h).2.2).trans
    rw [inf_sup_left,← inf_assoc,compl_inf_eq_bot,bot_inf_eq,bot_sup_eq]
    exact inf_le_right.trans inf_le_right
  · intro h
    exact overlay_iff.mpr ⟨hp,hi,(le_inf ho h).trans le_sup_right⟩

theorem overlay_regular {Γ : B} {P R L old a b : N} (ha : Γ ≤ regularColumnsValue P R old a)
    (hb : Γ ≤ regularColumnsValue P R L b) : Γ ≤ regularColumnsValue P R L (overlayBits P L old a b) := by
  refine le_inf relationGraph_subset (allIn_intro ?_)
  intro Δ hd i hi
  let c := i ∈ᴮ old
  have split : Δ = (Δ ⊓ c) ⊔ (Δ ⊓ cᶜ) := by rw [← inf_sup_left,sup_compl_eq_top,inf_top_eq]
  apply split.le.trans (sup_le ?_ ?_)
  · apply regularColumn_of_agree (allIn_elim (inf_le_left.trans (hd.trans (ha.trans inf_le_right))) inf_le_right)
    intro z hz p hp
    exact (overlay_old hp ((hz.trans inf_le_left).trans hi) (hz.trans inf_le_right)).symm
  · apply regularColumn_of_agree (inf_le_left.trans (allIn_elim (hd.trans (hb.trans inf_le_right)) hi))
    intro z hz p hp
    exact (overlay_fresh hp ((hz.trans inf_le_left).trans hi) (hz.trans inf_le_right)).symm

def Fields.extendWord (s : Fields B) (L b : N) : Fields B :=
  {s with length := L,bits := overlayBits s.carrier L s.length s.bits b}

theorem extendWord_mem_and_refines {Γ : B} {K L b : N} {θ : Cardinal.{u}} (s : Fields B)
    (valid : Γ ≤ s.code ∈ᴮ conditionSet K θ) (bound : Γ ≤ L ∈ᴮ check (PSet.ordinalMk θ.ord))
    (len : Γ ≤ s.length ⊆ᴮ L) (payload : Γ ≤ regularColumnsValue s.carrier s.order L b) :
    Γ ≤ pair (s.extendWord L b).code s.code ∈ᴮ orderSet K θ := by
  obtain hv := valid.trans_eq (code_mem_conditionSet K θ s)
  have shape := hv.trans inf_le_left
  have law := hv.trans inf_le_right
  have po := law.trans inf_le_left
  have sr := shape.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  let t := s.extendWord L b
  have tv : Γ ≤ t.code ∈ᴮ conditionSet K θ := by
    rw [code_mem_conditionSet]
    refine le_inf (le_inf (shape.trans inf_le_left) (le_inf bound (le_inf (shape.trans
      (inf_le_right.trans (inf_le_right.trans inf_le_left))) (le_inf (sr.trans inf_le_left) ?_))))
      (le_inf po (le_inf (law.trans (inf_le_right.trans inf_le_left)) (le_inf
        (law.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))
        (overlay_regular (law.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))) payload))))
    exact relationGraph_subset
  apply mem_orderSet.mpr ⟨tv,valid,le_iSup_of_le t (le_iSup_of_le s (le_inf (le_inf bv_refl bv_refl) ?_))⟩
  apply le_iSup_of_le s.carrier
  apply le_iSup_of_le (projectionIdentity s.carrier)
  refine le_inf (le_inf (projectionIdentity_value K s.carrier s.order po) (projectionIdentity_point _ _ _)) (le_inf len ?_)
  refine le_iInf fun p => le_iInf fun q => le_iInf fun i => projection_imp.mpr ?_
  intro Δ hd h
  have hpq := projectionIdentity_pair.mp (h.trans (inf_le_left.trans inf_le_left))
  have hi := h.trans inf_le_right
  have hiL := mem_of_mem_subset (hd.trans len) hi
  refine le_inf (projection_imp.mpr fun z hz bit => ?_) (projection_imp.mpr fun z hz bit => ?_)
  · exact bv_rw'' (ϕ := fun v => edge s.bits v i) (hz.trans hpq.2.2)
      ((overlay_old (a := s.bits) (b := b) (hz.trans hpq.1) (hz.trans hiL) (hz.trans hi)).mp bit)
      B_ext_pair_mem_left
  · exact (overlay_old (a := s.bits) (b := b) (hz.trans hpq.1) (hz.trans hiL) (hz.trans hi)).mpr
      (bv_rw'' (bv_symm (hz.trans hpq.2.2)) bit B_ext_pair_mem_left)

theorem extendWord_mixedBits {Γ : B} {K L Z : N} {θ : Cardinal.{u}} (s : Fields B)
    (valid : Γ ≤ s.code ∈ᴮ conditionSet K θ) (bound : Γ ≤ L ∈ᴮ check (PSet.ordinalMk θ.ord))
    (len : Γ ≤ s.length ⊆ᴮ L) (bits : Γ ≤ Z ⊆ᴮ L) :
    Γ ≤ pair (s.extendWord L (prod s.carrier Z)).code s.code ∈ᴮ orderSet K θ := by
  have po := (valid.trans_eq (code_mem_conditionSet K θ s)).trans (inf_le_right.trans inf_le_left)
  exact extendWord_mem_and_refines s valid bound len (constant_regularColumns po Z bits)

end bSet.ErdosShioyaInternal
