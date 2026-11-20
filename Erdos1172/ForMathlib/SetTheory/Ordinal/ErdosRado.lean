/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.SetTheory.Cardinal.Pigeonhole
public import Erdos1172.ForMathlib.SetTheory.Cardinal.ErdosRadoCodes
public import Erdos1172.ForMathlib.SetTheory.Ordinal.PartitionRelationAPI

@[expose] public section

open Cardinal Ordinal Set Function

/-!
# The pair case of the Erdős--Rado theorem at `ω₁`

This file develops the canonical-branch (or ramification) construction used in the
pair case of the Erdős--Rado theorem.  For a graph on `ω₂`, and a proposed last
vertex `a`, the construction recursively selects the least vertex below `a` which
has the same adjacency pattern to all vertices selected earlier as `a` does.

If a branch has length `ω₁`, it is end-homogeneous.  If every branch stops,
its first stopping level together with its Boolean adjacency profile determines
the last vertex.  CH bounds the set of these countable profiles by `ℵ₁`, which
contradicts the `ℵ₂` possible last vertices.
-/

namespace ErdosRado

abbrev W1 : Type := (omega 1 : Ordinal.{0}).ToType
abbrev W2 : Type := (omega 2 : Ordinal.{0}).ToType

variable (G : SimpleGraph W2)

/-- A candidate for the next point in the canonical branch ending at `a`. -/
private def IsCandidate (a : W2) (i : W1) (previous : ∀ j, j < i → W2)
    (x : W2) : Prop :=
  x < a ∧
    (∀ j (hj : j < i), previous j hj < x) ∧
    ∀ j (hj : j < i), G.Adj (previous j hj) x ↔ G.Adj (previous j hj) a

/-- Choose the least candidate, returning the terminal point itself if none exists. -/
private noncomputable def nextPoint (a : W2) (i : W1)
    (previous : ∀ j, j < i → W2) : W2 := by
  classical
  exact if h : Set.Nonempty {x | IsCandidate G a i previous x} then
    wellFounded_lt.min {x | IsCandidate G a i previous x} h
  else a

/-- The canonical branch with terminal point `a`. -/
private noncomputable def branch (a : W2) : W1 → W2 :=
  WellFoundedLT.fix (nextPoint G a)

private theorem branch_eq_nextPoint (a : W2) (i : W1) :
    branch G a i = nextPoint G a i (fun j _ ↦ branch G a j) := by
  change WellFoundedLT.fix (nextPoint G a) i =
    nextPoint G a i (fun j _ ↦ WellFoundedLT.fix (nextPoint G a) j)
  rw [WellFoundedLT.fix_eq]

/-- A branch is live at `i` exactly when the chosen point is still below its terminal point. -/
private def Live (a : W2) (i : W1) : Prop := branch G a i < a

private theorem branch_eq_terminal_of_no_candidate {a : W2} {i : W1}
    (h : ¬ Set.Nonempty {x | IsCandidate G a i (fun j _ ↦ branch G a j) x}) :
    branch G a i = a := by
  classical
  rw [branch_eq_nextPoint]
  unfold nextPoint
  rw [dif_neg h]

private theorem branch_candidate_of_live {a : W2} {i : W1} (hi : Live G a i) :
    IsCandidate G a i (fun j _ ↦ branch G a j) (branch G a i) := by
  classical
  rw [branch_eq_nextPoint]
  unfold nextPoint
  split_ifs with h
  · exact wellFounded_lt.min_mem _ h
  · exfalso
    have heq := branch_eq_terminal_of_no_candidate G h
    rw [Live, heq] at hi
    exact (lt_irrefl _ hi)

private theorem branch_live_of_candidate {a : W2} {i : W1} {x : W2}
    (hx : IsCandidate G a i (fun j _ ↦ branch G a j) x) : Live G a i := by
  classical
  rw [Live, branch_eq_nextPoint]
  unfold nextPoint
  rw [dif_pos ⟨x, hx⟩]
  exact (wellFounded_lt.min_mem
    {y : W2 | IsCandidate G a i (fun j _ ↦ branch G a j) y} ⟨x, hx⟩).1

private theorem branch_le_of_candidate {a : W2} {i : W1} {x : W2}
    (hx : IsCandidate G a i (fun j _ ↦ branch G a j) x) : branch G a i ≤ x := by
  classical
  rw [branch_eq_nextPoint]
  unfold nextPoint
  rw [dif_pos ⟨x, hx⟩]
  exact wellFounded_lt.min_le
    (s := {y : W2 | IsCandidate G a i (fun j _ ↦ branch G a j) y}) hx

private theorem branch_lt_of_lt_of_live {a : W2} {i j : W1}
    (hji : j < i) (hi : Live G a i) : branch G a j < branch G a i :=
  (branch_candidate_of_live G hi).2.1 j hji

private theorem branch_adj_iff_terminal_of_lt_of_live {a : W2} {i j : W1}
    (hji : j < i) (hi : Live G a i) :
    G.Adj (branch G a j) (branch G a i) ↔ G.Adj (branch G a j) a :=
  (branch_candidate_of_live G hi).2.2 j hji

private theorem branch_strictMono {a : W2} (ha : ∀ i, Live G a i) :
    StrictMono (branch G a) := by
  intro i j hij
  exact branch_lt_of_lt_of_live G hij (ha j)

/-- Boolean encoding of an edge.  This lets us count profiles by cardinal exponentiation. -/
private noncomputable def edgeColor (x y : W2) : Bool := by
  classical
  exact if G.Adj x y then true else false

private theorem edgeColor_eq_iff {x y z : W2} :
    edgeColor G x y = edgeColor G x z ↔ (G.Adj x y ↔ G.Adj x z) := by
  classical
  simp [edgeColor]

private theorem edgeColor_eq_true_iff {x y : W2} :
    edgeColor G x y = true ↔ G.Adj x y := by
  classical
  simp [edgeColor]

/-- A Boolean profile with a bounded initial-segment support.  Keeping the value function
nondependent makes equality of profiles convenient; `boundedProfile_surjection` below
recovers the sharp dependent-sum cardinal bound. -/
private structure BoundedProfile where
  height : W1
  value : W1 → Bool
  value_eq_false : ∀ j, ¬ j < height → value j = false

private noncomputable def failureCode (height : W2 → W1) (a : W2) : BoundedProfile where
  height := height a
  value j := if j < height a then edgeColor G (branch G a j) a else false
  value_eq_false j hj := by simp [hj]

/-- If every branch is assigned its first failure level, its level and pre-failure
adjacency profile uniquely determine the terminal point. -/
private theorem failureCode_injective
    (height : W2 → W1)
    (hfail : ∀ a, ¬ Live G a (height a))
    (hbefore : ∀ a j, j < height a → Live G a j) :
    Injective (failureCode G height) := by
  classical
  intro a b hab
  by_contra hne
  wlog hablt : a < b generalizing a b with H
  · exact H hab.symm (fun h ↦ hne h.symm)
      (lt_of_le_of_ne (le_of_not_gt hablt) (fun h ↦ hne h.symm))
  have hh : height a = height b := congrArg BoundedProfile.height hab
  have hp : (failureCode G height a).value = (failureCode G height b).value :=
    congrArg BoundedProfile.value hab
  have hpAt (j : W1) (hj : j < height a) :
      edgeColor G (branch G a j) a = edgeColor G (branch G b j) b := by
    have hc := congrFun hp j
    have hjb : j < height b := by simpa only [← hh] using hj
    simpa only [failureCode, hj, hjb, if_pos] using hc
  have hbranches : ∀ j (hj : j < height a), branch G a j = branch G b j := by
    intro j
    induction j using WellFoundedLT.induction with
    | ind j ih =>
      intro hj
      have hla : Live G a j := hbefore a j hj
      have hlb : Live G b j := hbefore b j (by simpa only [← hh] using hj)
      have hca := branch_candidate_of_live G hla
      have hcb : IsCandidate G b j (fun k _ ↦ branch G b k) (branch G b j) :=
        branch_candidate_of_live G hlb
      have habProfile (k : W1) (hk : k < j) :
          G.Adj (branch G a k) a ↔ G.Adj (branch G a k) b := by
        have hc := hpAt k (hk.trans hj)
        have hik := ih k hk (hk.trans hj)
        rw [← hik] at hc
        exact (edgeColor_eq_iff G).mp hc
      have hxaForB :
          IsCandidate G b j (fun k _ ↦ branch G b k) (branch G a j) := by
        refine ⟨hca.1.trans hablt, ?_, ?_⟩
        · intro k hk
          change branch G b k < branch G a j
          rw [← ih k hk (hk.trans hj)]
          exact hca.2.1 k hk
        · intro k hk
          change G.Adj (branch G b k) (branch G a j) ↔ G.Adj (branch G b k) b
          rw [← ih k hk (hk.trans hj)]
          exact (hca.2.2 k hk).trans (habProfile k hk)
      have hxbForA :
          IsCandidate G a j (fun k _ ↦ branch G a k) (branch G b j) := by
        have hxb_lt_xa : branch G b j ≤ branch G a j :=
          branch_le_of_candidate G hxaForB
        refine ⟨hxb_lt_xa.trans_lt hca.1, ?_, ?_⟩
        · intro k hk
          change branch G a k < branch G b j
          rw [ih k hk (hk.trans hj)]
          exact hcb.2.1 k hk
        · intro k hk
          change G.Adj (branch G a k) (branch G b j) ↔ G.Adj (branch G a k) a
          have hik := ih k hk (hk.trans hj)
          rw [hik]
          have hpB : G.Adj (branch G b k) a ↔ G.Adj (branch G b k) b := by
            simpa only [hik] using habProfile k hk
          exact (hcb.2.2 k hk).trans hpB.symm
      exact le_antisymm (branch_le_of_candidate G hxbForA)
        (branch_le_of_candidate G hxaForB)
  have haCandidateForB :
      IsCandidate G b (height a) (fun j _ ↦ branch G b j) a := by
    refine ⟨hablt, ?_, ?_⟩
    · intro j hj
      change branch G b j < a
      rw [← hbranches j hj]
      exact (branch_candidate_of_live G (hbefore a j hj)).1
    · intro j hj
      change G.Adj (branch G b j) a ↔ G.Adj (branch G b j) b
      rw [← hbranches j hj]
      have hc := hpAt j hj
      exact (edgeColor_eq_iff G).mp (by simpa only [hbranches j hj] using hc)
  have hlive : Live G b (height a) := branch_live_of_candidate G haCandidateForB
  rw [hh] at hlive
  exact hfail b hlive

/-- Restrict a bounded profile to its actual initial-segment domain. -/
private def restrictProfile (p : BoundedProfile) :
    Σ i : W1, Set.Iio i → Bool :=
  ⟨p.height, fun j ↦ p.value j.1⟩

private theorem restrictProfile_injective : Injective restrictProfile := by
  intro p q hpq
  cases p with
  | mk i value hvalue =>
    cases q with
    | mk j value' hvalue' =>
      have hij : i = j := (Sigma.mk.inj_iff.mp hpq).1
      subst j
      have hrestricted :
          (fun x : Set.Iio i ↦ value x.1) = (fun x : Set.Iio i ↦ value' x.1) :=
        eq_of_heq (Sigma.mk.inj_iff.mp hpq).2
      have hvalues : value = value' := by
        funext x
        by_cases hx : x < i
        · exact congrFun hrestricted ⟨x, hx⟩
        · rw [hvalue x hx, hvalue' x hx]
      congr 1

/-- Under CH, some canonical branch remains live through all of `ω₁`. -/
private theorem exists_full_live_branch
    (hCH : Cardinal.CH) :
    ∃ a : W2, ∀ i : W1, Live G a i := by
  classical
  by_contra hfull
  have hstop : ∀ a : W2, ∃ i : W1, ¬ Live G a i := by
    intro a
    exact not_forall.mp (by
      intro ha
      exact hfull ⟨a, ha⟩)
  let height : W2 → W1 := fun a ↦
    wellFounded_lt.min {i | ¬ Live G a i} (hstop a)
  have hfail : ∀ a, ¬ Live G a (height a) := by
    intro a
    exact wellFounded_lt.min_mem {i | ¬ Live G a i} (hstop a)
  have hbefore : ∀ a j, j < height a → Live G a j := by
    intro a j hj
    by_contra hjlive
    have hnlt := wellFounded_lt.not_lt_min {i | ¬ Live G a i} hjlive
    exact hnlt (by simpa only [height] using hj)
  let code : W2 → Σ i : W1, Set.Iio i → Bool :=
    restrictProfile ∘ failureCode G height
  have hcodeInjective : Injective code :=
    restrictProfile_injective.comp
      (failureCode_injective G height hfail hbefore)
  exact hCH.not_injective_omega_two_to_sigma_Iio_omega_one_bool code hcodeInjective

/-- A full branch has an `ω₁`-sized set of levels with one fixed end color. -/
private theorem exists_branch_color_fiber
    (hCH : Cardinal.CH) :
    ∃ (a : W2) (s : Set W1) (c : Bool),
      (∀ i, Live G a i) ∧
      typeLT s = ω_ 1 ∧
      ∀ x : s, edgeColor G (branch G a x.1) a = c := by
  classical
  obtain ⟨a, ha⟩ := exists_full_live_branch G hCH
  let color : W1 → Bool := fun i ↦ edgeColor G (branch G a i) a
  obtain ⟨c, hc⟩ := Cardinal.infinite_pigeonhole color
    (by simp [W1])
    (by simp [W1])
  let s : Set W1 := color ⁻¹' {c}
  have hscard : #s = ℵ_ 1 := by
    simpa only [s, W1, Cardinal.mk_toType, Ordinal.card_omega] using hc
  have hstype : typeLT s = ω_ 1 := by
    apply le_antisymm
    · simpa using Ordinal.type_set_le s
    · simpa only [hscard, Cardinal.ord_aleph] using
        (Cardinal.ord_le_type ((· < ·) : s → s → Prop))
  refine ⟨a, s, c, ha, hstype, ?_⟩
  rintro ⟨i, hi⟩
  exact hi

/-- The full branch, its terminal point, and the constant end color contain a
monochromatic subset of order type `ω₁ + 1`. -/
private theorem exists_monochromatic_omegaOne_add_one
    (hCH : Cardinal.CH) :
    ∃ t : Set W2, typeLT t = ω_ 1 + 1 ∧
      (G.IsClique t ∨ Gᶜ.IsClique t) := by
  classical
  obtain ⟨a, s, c, ha, hstype, hcolor⟩ := exists_branch_color_fiber G hCH
  let image : Set W2 := branch G a '' s
  let t : Set W2 := insert a image
  have himageType : typeLT image = ω_ 1 := by
    have heq : typeLT s = typeLT (branch G a '' s) :=
      (((branch_strictMono G ha).strictMonoOn s).orderIso (branch G a) s).ordinalType_congr
    exact heq.symm.trans hstype
  have himageCard : #image = ℵ_ 1 := by
    have hc := congrArg Ordinal.card himageType
    simpa only [Ordinal.card_type, Ordinal.card_omega] using hc
  have homega_le : ω_ 1 ≤ typeLT t := by
    have hcard : (ℵ_ 1 : Cardinal.{0}) ≤ #t := by
      rw [← himageCard]
      exact Cardinal.mk_le_mk_of_subset (Set.subset_insert a image)
    simpa only [Cardinal.ord_aleph] using
      ((Cardinal.ord_le_ord.mpr hcard).trans
        (Cardinal.ord_le_type ((· < ·) : t → t → Prop)))
  have hmax : ∃ x : t, IsMax x := by
    refine ⟨⟨a, Set.mem_insert a image⟩, ?_⟩
    rw [isMax_iff_forall_not_lt]
    rintro ⟨y, hy⟩ hylt
    rcases hy with rfl | ⟨i, hi, rfl⟩
    · exact (lt_irrefl _ hylt)
    · exact (not_lt_of_ge (ha i).le) hylt
  have htypeSucc : typeLT t ∈ Set.range Order.succ :=
    Ordinal.type_lt_mem_range_succ_iff.mpr hmax
  have htype_ne : typeLT t ≠ ω_ 1 := by
    intro heq
    have hnot : ¬ Order.IsSuccPrelimit (ω_ 1) :=
      Order.not_isSuccPrelimit_iff_mem_range_succ.mpr (heq ▸ htypeSucc)
    exact hnot (Cardinal.isSuccLimit_omega 1).isSuccPrelimit
  have htarget : ω_ 1 + 1 ≤ typeLT t := by
    exact Order.succ_le_iff.mpr (lt_of_le_of_ne homega_le htype_ne.symm)
  have hadj : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → (G.Adj x y ↔ c = true) := by
    intro x hx y hy hxy
    change x ∈ insert a (branch G a '' s) at hx
    change y ∈ insert a (branch G a '' s) at hy
    rcases hx with hxa | ⟨i, hi, hix⟩
    · subst x
      rcases hy with hya | ⟨j, hj, hjy⟩
      · subst y
        exact (hxy rfl).elim
      · subst y
        have hjend : G.Adj (branch G a j) a ↔ c = true := by
          rw [← edgeColor_eq_true_iff G, hcolor ⟨j, hj⟩]
        simpa only [G.adj_comm] using hjend
    · subst x
      rcases hy with hya | ⟨j, hj, hjy⟩
      · subst y
        rw [← edgeColor_eq_true_iff G, hcolor ⟨i, hi⟩]
      · subst y
        have hiend : G.Adj (branch G a i) a ↔ c = true := by
          rw [← edgeColor_eq_true_iff G, hcolor ⟨i, hi⟩]
        have hjend : G.Adj (branch G a j) a ↔ c = true := by
          rw [← edgeColor_eq_true_iff G, hcolor ⟨j, hj⟩]
        rcases lt_trichotomy i j with hij | hij | hji
        · exact (branch_adj_iff_terminal_of_lt_of_live G hij (ha j)).trans hiend
        · subst j
          exact (hxy rfl).elim
        · have hrev :=
            (branch_adj_iff_terminal_of_lt_of_live G hji (ha i)).trans hjend
          simpa only [G.adj_comm] using hrev
  have htClique : G.IsClique t ∨ Gᶜ.IsClique t := by
    by_cases hc : c = true
    · left
      intro x hx y hy hxy
      exact (hadj x hx y hy hxy).mpr hc
    · right
      intro x hx y hy hxy
      rw [SimpleGraph.compl_adj]
      exact ⟨hxy, fun hxyG ↦ hc ((hadj x hx y hy hxy).mp hxyG)⟩
  obtain ⟨u, hut, hutype⟩ := Ordinal.exists_subset_typeLT_eq t htarget
  refine ⟨u, hutype, ?_⟩
  exact htClique.imp (·.subset hut) (·.subset hut)

/-- The pair case of the Erdős--Rado theorem at `ℵ₀`, in the precise power
form of CH needed by the proof:
`ω₂ → (ω₁ + 1, ω₁ + 1)²`. -/
theorem ordinalRamsey_omegaTwo_omegaOne_add_one
    (hCH : Cardinal.CH) :
    OrdinalRamsey (ω_ 2 : Ordinal.{0}) (ω_ 1 + 1) (ω_ 1 + 1) := by
  intro red blue hcompl
  obtain ⟨t, htype, hred | hredCompl⟩ :=
    exists_monochromatic_omegaOne_add_one red hCH
  · exact Or.inl ⟨t, hred, htype⟩
  · refine Or.inr ⟨t, ?_, htype⟩
    rwa [← hcompl.compl_eq]

end ErdosRado
