/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CountablyUniversalLabels
public import Erdos1172.Part3IteratedHechlerCentering

@[expose] public section

/-!
# Countable amalgamation in universal profile classes

Profiles in one covering class agree wherever both are active. Their
countable union is again a profile, with exactly the union of supports.
For whole-stem labels this says that overlapping active coordinates
have identical stems, not merely compatible values at some entries.

The final centering API retains its history-amalgamation premise. It
does not claim to have constructed an uncountable Hechler iteration.
-/

open Cardinal Ordinal Set Function

namespace Erdos1172Part3CountableProfileAmalgamation

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3CountableSupportProfiles (Profile support StemProfile)
open Erdos1172Part3CountablyUniversalLabels (CountableCover exists_countableCover_of_gch)
open Erdos1172Part3HechlerCentering (Stem mk_Stem_le)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)

variable {I V : Type}

def Extends (q p : Profile I V) : Prop :=
  ∀ i v, p.val i = some v → q.val i = some v

def unionSupport (C : Set (Profile I V)) : Set I := ⋃ p ∈ C, support p

theorem unionSupport_countable {C : Set (Profile I V)} (hC : C.Countable) :
    (unionSupport C).Countable := hC.biUnion (fun p _ => p.property)

theorem exists_exact_amalgamation (cover : CountableCover I V)
    (C : Set (Profile I V)) (hC : C.Countable) (value : W1)
    (hvalue : ∀ p ∈ C, cover.code p = value) :
    ∃ q : Profile I V, support q = unionSupport C ∧ ∀ p ∈ C, Extends q p := by
  classical
  let merged (i : I) : Option V :=
    if i ∈ unionSupport C then cover.label value i else none
  have hsmall : {i | merged i ≠ none} ⊆ unionSupport C := by
    intro i hi
    by_contra hnot
    change merged i ≠ none at hi
    simp only [merged, if_neg hnot, ne_eq, not_true_eq_false] at hi
  let q : Profile I V := ⟨merged, (unionSupport_countable hC).mono hsmall⟩
  have hinc : ∀ p ∈ C, Extends q p := by
    intro p hp i v hiv
    have hi : i ∈ support p := by
      change p.val i ≠ none
      rw [hiv]
      exact Option.some_ne_none v
    have hmem : i ∈ unionSupport C :=
      Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hi⟩⟩
    have hlabel := cover.code_spec p i v hiv
    rw [hvalue p hp] at hlabel
    change merged i = some v
    simp only [merged, if_pos hmem, hlabel]
  refine ⟨q, Set.Subset.antisymm hsmall ?_, hinc⟩
  intro i hi
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hi
  obtain ⟨hpC, hip⟩ := Set.mem_iUnion.mp hp
  change p.val i ≠ none at hip
  cases hiv : p.val i with
  | none => exact (hip hiv).elim
  | some v =>
    change q.val i ≠ none
    rw [hinc p hpC i v hiv]
    exact Option.some_ne_none v

noncomputable def stemCover (hGCH : GCH) (hI : #I ≤ ℵ_ 2) : CountableCover I Stem :=
  Classical.choice (exists_countableCover_of_gch hGCH hI (mk_Stem_le hGCH.toCH))

theorem same_code_same_active_stem (hGCH : GCH) (hI : #I ≤ ℵ_ 2)
    {p q : StemProfile I} (hcode : (stemCover hGCH hI).code p = (stemCover hGCH hI).code q)
    {i : I} {s t : Stem} (hp : p.val i = some s) (hq : q.val i = some t) : s = t :=
  (stemCover hGCH hI).agree_on_overlap hcode hp hq

/-- The entire omegaTwo coordinate set is covered; no assumption that
the coordinate set has cardinality at most omegaOne remains. -/
theorem omegaTwo_stem_amalgamation (hGCH : GCH)
    (C : Set (StemProfile W2)) (hC : C.Countable) (value : W1)
    (hvalue : ∀ p ∈ C, (stemCover hGCH (by
      simp only [W2, Cardinal.mk_toType, Ordinal.card_omega, le_refl])).code p = value) :
    ∃ q : StemProfile W2, support q = unionSupport C ∧ ∀ p ∈ C, Extends q p :=
  exists_exact_amalgamation _ C hC value hvalue

variable {P : Type} [Preorder P]

/-- A reusable centering construction for histories. The substantive
order-specific lower-bound assertion remains explicit. -/
noncomputable def centered_of_profile_amalgamation
    (cover : CountableCover I V) (profile : P → Profile I V)
    (hfuse : ∀ C : Set P, C.Countable →
      (∀ p ∈ C, ∀ q ∈ C, ∀ i v w,
        (profile p).val i = some v → (profile q).val i = some w → v = w) →
      ∃ lower : P, ∀ p ∈ C, lower ≤ p) : CountablyCenteredCode P where
  code p := cover.code (profile p)
  lower := by
    intro C hC value hvalue
    apply hfuse C hC
    intro p hp q hq i v w hpv hqw
    exact cover.agree_on_overlap ((hvalue p hp).trans (hvalue q hq).symm) hpv hqw

end Erdos1172Part3CountableProfileAmalgamation
