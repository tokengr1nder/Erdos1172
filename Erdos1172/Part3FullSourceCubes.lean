/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3RankedCoreBlockAssembly

@[expose] public section

/-!
# Cubic source cores in the full transfinite order

The constructed local square witnesses supply whole square blocks in
every locally coded neighborhood. Fusion assembles omegaOne such blocks
into a cubic core. The source remains an actual regular-name membership
requirement, and the endpoint bounds every possible decided vertex.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3FullSourceCubes

open ErdosRadoCHAsym (W1 W2 IsOmegaOneSup)
open Erdos1172Part3TransfiniteStageLocality (Full Earlier restriction)
open Erdos1172Part3TransfiniteHechlerOrder (mk_stage_le)
open Erdos1172Part3TransfiniteHechlerCentering (omegaTwoCC)
open Erdos1172Part3TransfiniteHechlerClosure (full_countablyClosed)
open Erdos1172Part3StationarySquareDecisions (Square)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularStageLocality (EventuallyLocal eventuallyLocal_ground)
open Erdos1172Part3RegularNeighborhoodCode (Code eval rank blockRank)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3RankedCoreBlockAssembly
open Erdos1172Part3NeighborhoodCode (alephZero_lt_cof_W2)
open OrdinalRamsey (HasCliqueOfType)

abbrev Cube := W1 ×ₗ Square

end Erdos1172Part3FullSourceCubes
