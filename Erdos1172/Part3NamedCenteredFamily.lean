/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CenteredStationaryLoss
public import Erdos1172.Part3RegularMembership
public import Erdos1172.Part3IteratedHechlerCentering

@[expose] public section

/-!
# Centered families with actual named future membership

Finite intersections are required to stay positive only at conditions
where all selected future vertices are actually present. This retains
the condition compatibility needed by the stationary small-loss argument.
The blue extraction law is an explicit input, not a partition conclusion.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3NamedCenteredFamily

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3StationaryDecisions (possible)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3NeighborhoodCode (cof_W2)
open Erdos1172Part3FiniteIdealEndpoint (clique_add_two)
open Erdos1172Part3RedCoreIdeal (mk_eq_alephTwo_of_isCofinal)
open OrdinalRamsey (HasCliqueOfType)

variable {P : Type} [Preorder P]

def rowsMeet (H : SimpleGraph W2) (rows : RegularName P W2) (t : Finset W2) :
    RegularName P W2 := meet rows (ground {x | ∀ b ∈ t, H.Adj x b})

theorem rowsMeet_empty (H : SimpleGraph W2) (rows : RegularName P W2) :
    rowsMeet H rows ∅ = rows := by
  apply RegularName.ext
  intro p x
  simp only [rowsMeet, meet, ground, Set.mem_setOf_eq, Finset.notMem_empty,
    false_implies, implies_true, and_true]

def Centered (J : RegularName P (RegularName P W2)) (H : SimpleGraph W2)
    (rows future : RegularName P W2) (p0 : P) (family : Set W2) : Prop :=
  ∀ t : Finset W2, (↑t : Set W2) ⊆ family → ∀ p : P, p ≤ p0 →
    (∀ b ∈ t, future.holds p b) → (neg J).holds p (rowsMeet H rows t)

def BlueExtraction (J : RegularName P (RegularName P W2)) (H : SimpleGraph W2)
    (rows : RegularName P W2) (p0 : P) : Prop :=
  ∀ p : P, p ≤ p0 → ∀ X : RegularName P W2,
    (∀ q : P, q ≤ p → ∀ x : W2, X.holds q x → rows.holds q x) → ¬J.holds p X →
      ∃ C : Set W2, H.IsClique C ∧ typeLT C = ω_ 1 ∧
        ∀ x ∈ C, ∃ q : P, q ≤ p ∧ X.holds q x

theorem exists_maximal_centered (J : RegularName P (RegularName P W2))
    (H : SimpleGraph W2) (rows future : RegularName P W2) (p0 : P)
    (hrows : (neg J).holds p0 rows) :
    ∃ family : Set W2, Maximal (fun family =>
      family ⊆ possible future.holds p0 ∧ Centered J H rows future p0 family) family := by
  classical
  have hempty : (∅ : Set W2) ⊆ possible future.holds p0 ∧
      Centered J H rows future p0 ∅ := by
    refine ⟨Set.empty_subset _, ?_⟩
    intro t ht p hpp0 hfuture
    have hte : t = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun _ h => ht h)
    rw [hte, rowsMeet_empty]
    exact (neg J).persistent hpp0 hrows
  obtain ⟨family, _, hfamily⟩ := zorn_subset_nonempty
    {family | family ⊆ possible future.holds p0 ∧ Centered J H rows future p0 family}
    (fun chain hchain hordered hne => by
      refine ⟨⋃₀ chain, ⟨?_, ?_⟩, ?_⟩
      · rintro x ⟨c, hc, hxc⟩
        exact (hchain hc).1 hxc
      · intro t ht p hpp0 hfuture
        obtain ⟨c, hc, htc⟩ := hordered.directedOn.exists_mem_subset_of_finite_of_subset_sUnion
          hne t.finite_toSet ht
        exact (hchain hc).2 t htc p hpp0 hfuture
      · exact fun c hc => Set.subset_sUnion_of_mem hc) ∅ hempty
  exact ⟨family, hfamily⟩

theorem ordered_pair_red (J : RegularName P (RegularName P W2))
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (rows future : RegularName P W2) (p0 : P) (a : W2)
    (hr : ∀ p : P, p ≤ p0 → ∀ x, rows.holds p x → x < a)
    (hf : ∀ p : P, p ≤ p0 → ∀ b, future.holds p b → a < b)
    (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (hcore : BlueExtraction J H rows p0)
    {family : Set W2} (hcenter : Centered J H rows future p0 family)
    {b c : W2} (hb : b ∈ family) (hc : c ∈ family) (hbc : b < c)
    (p : P) (hpp0 : p ≤ p0) (hUb : future.holds p b) (hUc : future.holds p c) :
    G.Adj b c := by
  classical
  rw [← hcompl.symm.compl_eq, SimpleGraph.compl_adj]
  refine ⟨hbc.ne, ?_⟩
  intro hHbc
  let t : Finset W2 := {b, c}
  have ht : (↑t : Set W2) ⊆ family := by
    intro x hx
    have hx' : x = b ∨ x = c := by simpa only [t, Finset.mem_coe,
      Finset.mem_insert, Finset.mem_singleton] using hx
    rcases hx' with rfl | rfl
    · exact hb
    · exact hc
  have hfuture : ∀ x ∈ t, future.holds p x := by
    intro x hx
    have hx' : x = b ∨ x = c := by simpa only [t,
      Finset.mem_insert, Finset.mem_singleton] using hx
    rcases hx' with rfl | rfl
    · exact hUb
    · exact hUc
  obtain ⟨C, hC, hCt, hmem⟩ := hcore p hpp0 (rowsMeet H rows t)
    (fun q hqp x hx => hx.1) ((hcenter t ht p hpp0 hfuture) p le_rfl)
  apply hblue (clique_add_two hC hCt ?_ hbc hHbc ?_ ?_)
  · intro x hx
    obtain ⟨q, hqp, hqx⟩ := hmem x hx
    exact (hr q (hqp.trans hpp0) x hqx.1).trans (hf p hpp0 b hUb)
  · intro x hx
    exact (hmem x hx).choose_spec.2.2 b (by simp [t])
  · intro x hx
    exact (hmem x hx).choose_spec.2.2 c (by simp [t])

/-- Possible family members are assigned actual conditions. Each center
fiber is a ground red clique, so all fibers, and hence the family, are
bounded. No uncountable lower bound on the conditions is used. -/
theorem centered_bounded (center : CountablyCenteredCode P)
    (J : RegularName P (RegularName P W2)) (G H : SimpleGraph W2)
    (hcompl : IsCompl G H) (rows future : RegularName P W2) (p0 : P) (a : W2)
    (hr : ∀ p : P, p ≤ p0 → ∀ x, rows.holds p x → x < a)
    (hf : ∀ p : P, p ≤ p0 → ∀ b, future.holds p b → a < b)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (hcore : BlueExtraction J H rows p0)
    {family : Set W2} (hfamily : family ⊆ possible future.holds p0)
    (hcenter : Centered J H rows future p0 family) :
    ∃ bound : W2, ∀ b ∈ family, b < bound := by
  classical
  let condition (b : family) : P := (hfamily b.property).choose
  have hcondition (b : family) : condition b ≤ p0 ∧ future.holds (condition b) b.val :=
    (hfamily b.property).choose_spec
  let fiber (i : W1) : Set W2 :=
    {b | ∃ hb : b ∈ family, center.code (condition ⟨b, hb⟩) = i}
  have hclique (i : W1) : G.IsClique (fiber i) := by
    rintro b ⟨hb, hbi⟩ c ⟨hc, hci⟩ hne
    obtain ⟨q, hqb, hqc⟩ := center.common_lower (hbi.trans hci.symm)
    have hqp0 := hqb.trans (hcondition ⟨b, hb⟩).1
    have hUb := future.persistent hqb (hcondition ⟨b, hb⟩).2
    have hUc := future.persistent hqc (hcondition ⟨c, hc⟩).2
    rcases lt_or_gt_of_ne hne with hbc | hcb
    · exact ordered_pair_red J G H hcompl rows future p0 a hr hf hblue hcore
        hcenter hb hc hbc q hqp0 hUb hUc
    · exact (ordered_pair_red J G H hcompl rows future p0 a hr hf hblue hcore
        hcenter hc hb hcb q hqp0 hUc hUb).symm
  have hnoncofinal (i : W1) : ¬IsCofinal (fiber i) := by
    intro hcof
    exact hred ⟨fiber i, hclique i,
      Erdos1172Part3Failure.typeLT_eq_omegaTwo_of_mk_eq (mk_eq_alephTwo_of_isCofinal hcof)⟩
  choose bounds hbounds using fun i => not_isCofinal_iff.mp (hnoncofinal i)
  have hsmall : #(Set.range bounds) < Order.cof W2 := by
    rw [cof_W2]
    apply Cardinal.mk_range_le.trans_lt
    simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using
      (Cardinal.aleph_lt_aleph.mpr (by norm_num : (1 : Ordinal.{0}) < 2))
  obtain ⟨bound, hbound⟩ := not_isCofinal_iff.mp
    (fun hc => hsmall.not_ge (Order.cof_le hc))
  refine ⟨bound, ?_⟩
  intro b hb
  exact (hbounds (center.code (condition ⟨b, hb⟩)) b ⟨hb, rfl⟩).trans
    (hbound _ ⟨center.code (condition ⟨b, hb⟩), rfl⟩)

end Erdos1172Part3NamedCenteredFamily
