/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.SetTheory.Cardinal.Cofinality.Club
public import Mathlib.SetTheory.Cardinal.Arithmetic

@[expose] public section

open Cardinal Order Set

namespace ClubClosure

variable {V : Type} [LinearOrder V] [WellFoundedLT V]

/-- Closure points for an arbitrary map of a well-order. -/
def ClosedUnder (f : V → V) (a : V) : Prop := ∀ b < a, f b < a

/-- If the images of bounded prefixes have strict bounds and the ambient
cofinality is uncountable, closure points form a club. -/
theorem isClub_closedUnder_of_bounded (f : V → V)
    (hcof : ℵ₀ < cof V)
    (hbound : ∀ a : V, ∃ b : V, a < b ∧ ∀ x ≤ a, f x < b) :
    IsClub {a | ClosedUnder f a} := by
  classical
  refine ⟨?_, ?_⟩
  · intro s hs _ _ a ha b hb
    obtain ⟨c, hc, hbc, hca⟩ := ha.exists_between hb
    exact (hs hc b hbc).trans_le hca
  · intro a
    let _ : Nonempty V := ⟨a⟩
    let _ : OrderBot V := WellFoundedLT.toOrderBot V
    let _ : ConditionallyCompleteLinearOrderBot V :=
      WellFoundedLT.conditionallyCompleteLinearOrderBot V
    choose step hstep hstepf using hbound
    let seq : ℕ → V := fun n => step^[n] a
    have hseq : ∀ n, seq (n + 1) = step (seq n) := by
      intro n
      exact Function.iterate_succ_apply' step n a
    have hsmall : #(Set.range seq) < cof V := by
      calc
        #(Set.range seq) ≤ #ℕ := Cardinal.mk_range_le
        _ = ℵ₀ := Cardinal.mk_nat
        _ < cof V := hcof
    have hnot : ¬ IsCofinal (Set.range seq) := fun hc => hsmall.not_ge (Order.cof_le hc)
    have hbounded : BddAbove (Set.range seq) := .of_not_isCofinal hnot
    let top := sSup (Set.range seq)
    have hlub : IsLUB (Set.range seq) top := isLUB_csSup (Set.range_nonempty seq) hbounded
    refine ⟨top, ?_, hlub.1 ⟨0, rfl⟩⟩
    intro b hb
    obtain ⟨c, ⟨n, rfl⟩, hbc, _⟩ := hlub.exists_between hb
    exact (hstepf (seq n) b hbc.le).trans_le (by rw [← hseq]; exact hlub.1 ⟨n + 1, rfl⟩)

/-- In a regular cardinal order of uncountable cofinality, every self-map
has a club of closure points. -/
theorem isClub_closedUnder [IsRegularCardinalOrder V]
    (f : V → V) (hcof : ℵ₀ < cof V) :
    IsClub {a | ClosedUnder f a} := by
  apply isClub_closedUnder_of_bounded f hcof
  intro a
  have hinitial : #(Set.Iic a) < cof V := by
    rw [Order.cof_eq_cardinalMk]
    apply Cardinal.mk_Iic_lt a
    · exact Cardinal.ord_cardinalMk
    · simpa only [Order.cof_eq_cardinalMk] using hcof.le
  have himage : #(f '' Set.Iic a) < cof V := Cardinal.mk_image_le.trans_lt hinitial
  obtain ⟨b, hb⟩ := not_isCofinal_iff.mp (fun hc => himage.not_ge (Order.cof_le hc))
  have huniv : ¬ BddAbove (Set.univ : Set V) := by
    intro h
    obtain ⟨c, hc⟩ := h
    have ht : IsGreatest (Set.univ : Set V) c := ⟨Set.mem_univ _, hc⟩
    have hone : cof V ≤ 1 := by
      apply (Order.cof_le (s := {c}) ?_).trans
      · simp
      · intro x
        exact ⟨c, Set.mem_singleton c, hc (Set.mem_univ x)⟩
    exact (hcof.trans_le hone).not_ge Cardinal.one_le_aleph0
  obtain ⟨c, _, hc⟩ := not_bddAbove_iff.mp huniv (max a b)
  refine ⟨c, (le_max_left a b).trans_lt hc, ?_⟩
  intro x hx
  exact (hb (f x) ⟨x, hx, rfl⟩).trans ((le_max_right a b).trans_lt hc)

/-- Extend an operation on ranked objects to a self-map of the ambient
well-order. Outside the range of the ranks the extension is the identity. -/
noncomputable def onRanks {C : Type} (r : C ↪ V) (f : C → V) (x : V) : V := by
  classical
  exact if h : ∃ c, r c = x then f h.choose else x

@[simp] theorem onRanks_apply {C : Type} (r : C ↪ V) (f : C → V) (c : C) :
    onRanks r f (r c) = f c := by
  classical
  have h : ∃ d, r d = r c := ⟨c, rfl⟩
  have he : h.choose = c := r.injective h.choose_spec
  simp only [onRanks, dif_pos h, he]

/-- There is a club on which an operation preserves the ranks below the cut. -/
theorem isClub_rankClosed [IsRegularCardinalOrder V] {C : Type}
    (r : C ↪ V) (f : C → V) (hcof : ℵ₀ < cof V) :
    IsClub {a | ∀ c, r c < a → f c < a} := by
  refine ⟨?_, ?_⟩
  · intro s hs _ _ a ha c hc
    obtain ⟨b, hb, hcb, hba⟩ := ha.exists_between hc
    exact (hs hb c hcb).trans_le hba
  · intro a
    obtain ⟨b, hb, hab⟩ := (isClub_closedUnder (onRanks r f) hcof).isCofinal a
    refine ⟨b, ?_, hab⟩
    intro c hc
    simpa only [onRanks_apply] using hb (r c) hc

/-- One witness for each named set suffices to reflect containment of any
fixed set. The set being reflected is arbitrary; it need not be named. -/
theorem exists_club_reflects [IsRegularCardinalOrder V] {C : Type}
    (r : C ↪ V) (named : C → Set V) (s : Set V) (hcof : ℵ₀ < cof V) :
    ∃ club : Set V, IsClub club ∧ ∀ a ∈ club, ∀ c, r c < a →
      s ∩ Set.Iio a ⊆ named c → s ⊆ named c := by
  classical
  let witness : C → V := fun c =>
    if h : (s \ named c).Nonempty then h.choose else r c
  refine ⟨{a | ∀ c, r c < a → witness c < a}, isClub_rankClosed r witness hcof, ?_⟩
  intro a ha c hc hlocal x hx
  by_contra hnot
  have hn : (s \ named c).Nonempty := ⟨x, hx, hnot⟩
  have hmem : witness c ∈ s \ named c := by
    simpa only [witness, dif_pos hn] using hn.choose_spec
  exact hmem.2 (hlocal ⟨hmem.1, ha c hc⟩)

end ClubClosure
