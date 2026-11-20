/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4PosetGenericFilter
public import Erdos1172.Part4LevyInitialSegmentProjection
public import Erdos1172.Part4LevyCollapseNames

@[expose] public section

/-!
# Extending a collapse condition to the larger cardinal

Empty coordinates outside the initial segment determine an exact order
embedding. The complete homomorphism takes each principal Boolean cone
to the cone of this one extended condition. Membership in the transported
generic can consequently be tested on this single upper condition.
-/

set_option autoImplicit false
noncomputable section
open scoped Flypitch Erdos1172LevyCollapse
universe u

namespace Erdos1172LevyCollapse

open bSet ErdosNameTransport Erdos1172PosetGeneric Erdos1172PosetCompletion

variable {κ θ : Cardinal.{u}}

def zeroExtension (h : κ ≤ θ) (p : BelowCondition κ) : BelowCondition θ :=
  restrict (Set.range (initialCoordinate h)) (Classical.choose (initialProjection_surjective h p))

theorem zeroExtension_off (h : κ ≤ θ) (p : BelowCondition κ) {k : θ.ord.ToType}
    (hk : k ∉ Set.range (initialCoordinate h)) : zeroExtension h p k = ⊤ :=
  restrict_apply_of_not_mem hk _

theorem initialProjection_zeroExtension (h : κ ≤ θ) (p : BelowCondition κ) :
    initialProjection h (zeroExtension h p) = p := by
  let r := Classical.choose (initialProjection_surjective h p)
  have hpr : initialProjection h r = p := Classical.choose_spec (initialProjection_surjective h p)
  apply Eq.trans _ hpr
  apply DFinsupp.ext
  intro i
  apply Erdos1172Collapse.Condition.ext
  rw [initialProjection_entries, initialProjection_entries]
  unfold zeroExtension
  rw [restrict_apply_of_mem (Set.mem_range_self i)]

theorem zeroExtension_entries (h : κ ≤ θ) (p : BelowCondition κ) (i : κ.ord.ToType) :
    ((zeroExtension h p) (initialCoordinate h i)).entries = (p i).entries.map (initialAlphabet h i) := by
  have ht : (((zeroExtension h p) (initialCoordinate h i)).entries.map (initialAlphabet h i).symm) =
      (p i).entries := by rw [← initialProjection_entries, initialProjection_zeroExtension]
  simpa using congrArg (List.map (initialAlphabet h i)) ht

theorem initialProjection_le_iff_le_zeroExtension (h : κ ≤ θ) (r : BelowCondition θ)
    (p : BelowCondition κ) : initialProjection h r ≤ p ↔ r ≤ zeroExtension h p := by
  constructor
  · intro hr k
    by_cases hk : k ∈ Set.range (initialCoordinate h)
    · obtain ⟨i, rfl⟩ := hk
      change ((zeroExtension h p) (initialCoordinate h i)).entries <+: (r (initialCoordinate h i)).entries
      rw [zeroExtension_entries]
      have hi : (p i).entries <+: ((initialProjection h r) i).entries := hr i
      rw [initialProjection_entries] at hi
      simpa using hi.map (initialAlphabet h i)
    · rw [zeroExtension_off h p hk]
      exact le_top
  · intro hr
    exact ((initialProjection h).monotone hr).trans_eq (initialProjection_zeroExtension h p)

theorem initialCollapseHom_condition (h : κ ≤ θ) (p : BelowCondition κ) :
    initialCollapseHom h (condition p) = condition (zeroExtension h p) := by
  unfold initialCollapseHom
  rw [completionHom_condition_eq_iSup]
  apply le_antisymm
  · apply iSup_le
    intro r
    exact condition_mono ((initialProjection_le_iff_le_zeroExtension h r.val p).mp r.property)
  · exact le_iSup_of_le ⟨zeroExtension h p, (initialProjection_zeroExtension h p).le⟩ le_rfl

end Erdos1172LevyCollapse
