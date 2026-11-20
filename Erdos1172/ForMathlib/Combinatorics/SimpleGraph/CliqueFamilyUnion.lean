/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.ForMathlib.SetTheory.Ordinal.CliqueBlockExtension

@[expose] public section

open Ordinal Set

universe u v

namespace Ordinal

/-- The range of a strictly monotone map has exactly the order type of its
domain.  This packages the `StrictMonoOn.orderIso` argument used repeatedly
when a transfinite clique is assembled by choosing one point at each stage. -/
theorem typeLT_range_of_strictMono
    {I V : Type u}
    [LinearOrder I] [WellFoundedLT I]
    [LinearOrder V] [WellFoundedLT V]
    (f : I → V) (hf : StrictMono f) :
    typeLT (Set.range f) = typeLT I := by
  have heq : typeLT (Set.univ : Set I) =
      typeLT (f '' (Set.univ : Set I)) :=
    ((hf.strictMonoOn (Set.univ : Set I)).orderIso
      f (Set.univ : Set I)).ordinalType_congr
  rw [Set.image_univ] at heq
  calc
    typeLT (Set.range f) = typeLT (Set.univ : Set I) := heq.symm
    _ = typeLT I := OrderIso.Set.univ.ordinalType_congr

end Ordinal
