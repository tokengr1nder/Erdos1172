/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyOrdinalSegments
public import Erdos1172.Part4LevyUncountability
public import Erdos1172.Part4InternalHartogsUniqueness

@[expose] public section

/-!
# The actual below-κ collapse makes checked κ the internal omega-one

All mixed members of checked κ are countable, while checked κ itself is
not. Together with its ordinal property, these facts identify it with the
internal Hartogs ordinal of omega. This uses the actual constructed algebra
and proved chain condition; no cardinal-identification hypothesis is supplied.

The checked ground cardinal κ is not silently identified with the old
ground omega-one. This result proves neither GCH nor the required ideal
or anonymous-collapse construction.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch

universe u

namespace Erdos1172LevyCollapse

open bSet Erdos1172PosetCompletion

theorem below_checked_upper_hartogsProperty (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ) :
    (⊤ : Completion (BelowCondition κ)) ≤
      ErdosHartogs.hartogsProperty omega (check (PSet.ordinalMk κ.ord)) :=
  le_inf (check_Ord (PSet.Ord_mk κ.ord))
    (le_inf (forces_below_upper_uncountable κ Hκ Hunc) (below_checked_members_countable κ))

/-- This is the actual new internal omega-one, determined uniquely by
its complete internal Hartogs property, including arbitrary mixed members. -/
theorem below_checked_upper_eq_omegaOne (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ) :
    (⊤ : Completion (BelowCondition κ)) ≤ check (PSet.ordinalMk κ.ord) =ᴮ ErdosOmegaTwo.omegaOne :=
  ErdosOmegaTwo.omegaOne_property_unique (below_checked_upper_hartogsProperty κ Hκ Hunc)

end Erdos1172LevyCollapse
