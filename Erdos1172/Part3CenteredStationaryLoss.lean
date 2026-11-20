/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3ConvergentCore
public import Erdos1172.Part3RedPredecessorReflection
public import Mathlib.Data.Set.Finite.Lattice

@[expose] public section

/-!
# A maximal centered family supplies stationary small blue losses

Only finite ideal closure is used. A maximal family of blue columns with
positive finite intersections is red homogeneous when every positive row
set contains a blue omegaOne core and blue omegaOne+2 is forbidden. If
there is no source-sized red clique, this family is bounded. Its finite
maximality witnesses can then be frozen on a stationary future.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3CenteredStationaryLoss

open Erdos1172Part3NeighborhoodCode (W2 cof_W2 alephZero_lt_cof_W2)
open Erdos1172Part3FiniteIdealEndpoint
open Erdos1172Part3TwoSuccessorBootstrap (stationary_inter_club isCofinal_of_stationary)
open Erdos1172Part3RedCoreIdeal (mk_eq_alephTwo_of_isCofinal)
open OrdinalRamsey (HasCliqueOfType)

theorem exists_stationary_fiber_of_small {I : Type} (hI : #I < ℵ_ 2)
    {s : Set W2} (hs : IsStationary s) (f : s → I) :
    ∃ i : I, IsStationary {a : W2 | ∃ ha : a ∈ s, f ⟨a, ha⟩ = i} := by
  classical
  by_contra h
  push Not at h
  choose clubs hclubs hdisjoint using fun i => not_isStationary_iff.mp (h i)
  have hc : IsClub (⋂ i, clubs i) := IsClub.iInter alephZero_lt_cof_W2.ne'
    (by simpa only [Cardinal.lift_id, cof_W2] using hI) hclubs
  obtain ⟨a, has, hac⟩ := hs hc
  exact Set.disjoint_left.mp (hdisjoint (f ⟨a, has⟩)) ⟨has, rfl⟩
    (Set.mem_iInter.mp hac (f ⟨a, has⟩))

def rowsMeet (H : SimpleGraph W2) (rows : Set W2) (t : Finset W2) : Set W2 :=
  {x | x ∈ rows ∧ ∀ b ∈ t, H.Adj x b}

def Centered (J : FiniteSmallness W2) (H : SimpleGraph W2)
    (rows family : Set W2) : Prop :=
  ∀ t : Finset W2, (↑t : Set W2) ⊆ family → ¬J.small (rowsMeet H rows t)

theorem exists_maximal_centered (J : FiniteSmallness W2) (H : SimpleGraph W2)
    (rows future : Set W2) (hrows : ¬J.small rows) :
    ∃ family : Set W2, Maximal
      (fun family => family ⊆ future ∧ Centered J H rows family) family := by
  classical
  have hempty : (∅ : Set W2) ⊆ future ∧ Centered J H rows ∅ := by
    refine ⟨Set.empty_subset _, ?_⟩
    intro t ht
    have hte : t = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun _ h => ht h)
    simpa only [hte, rowsMeet, Finset.notMem_empty, false_implies, implies_true,
      and_true, Set.ofPred_mem_eq] using hrows
  obtain ⟨family, _, hfamily⟩ := zorn_subset_nonempty
    {family | family ⊆ future ∧ Centered J H rows family} (fun chain hchain hordered hne => by
      refine ⟨⋃₀ chain, ⟨?_, ?_⟩, ?_⟩
      · rintro x ⟨c, hc, hxc⟩
        exact (hchain hc).1 hxc
      · intro t ht
        obtain ⟨c, hc, htc⟩ := hordered.directedOn.exists_mem_subset_of_finite_of_subset_sUnion
          hne t.finite_toSet ht
        exact (hchain hc).2 t htc
      · exact fun c hc => Set.subset_sUnion_of_mem hc) ∅ hempty
  exact ⟨family, hfamily⟩

theorem centered_family_red (J : FiniteSmallness W2)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (rows future : Set W2) (a : W2) (hr : rows ⊆ Set.Iio a) (hf : future ⊆ Set.Ioi a)
    (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (hcore : ∀ x : Set W2, x ⊆ rows → ¬J.small x →
      ∃ c : Set W2, c ⊆ x ∧ H.IsClique c ∧ typeLT c = ω_ 1)
    {family : Set W2} (hfamily : family ⊆ future) (hcenter : Centered J H rows family) :
    G.IsClique family := by
  classical
  have noBluePair {p q : W2} (hp : p ∈ family) (hq : q ∈ family) (hpq : p < q) :
      ¬H.Adj p q := by
    intro hpqH
    let t : Finset W2 := {p, q}
    have ht : (↑t : Set W2) ⊆ family := by
      intro x hx
      have he : x = p ∨ x = q := by simpa only [t, Finset.mem_coe,
        Finset.mem_insert, Finset.mem_singleton] using hx
      rcases he with rfl | rfl
      · exact hp
      · exact hq
    obtain ⟨c, hc, hclique, htype⟩ := hcore (rowsMeet H rows t)
      (fun _ hx => hx.1) (hcenter t ht)
    exact hblue (clique_add_two hclique htype
      (fun x hx => (hr (hc hx).1).trans (hf (hfamily hp))) hpq hpqH
      (fun x hx => (hc hx).2 p (by simp [t]))
      (fun x hx => (hc hx).2 q (by simp [t])))
  intro p hp q hq hpq
  rw [← hcompl.symm.compl_eq, SimpleGraph.compl_adj]
  refine ⟨hpq, ?_⟩
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · exact noBluePair hp hq hlt
  · exact fun h => noBluePair hq hp hgt h.symm

theorem exists_stationary_small_loss (J : FiniteSmallness W2)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (rows future : Set W2) (a : W2) (hr : rows ⊆ Set.Iio a) (hf : future ⊆ Set.Ioi a)
    (hrows : ¬J.small rows) (hfuture : IsStationary future)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (hcore : ∀ x : Set W2, x ⊆ rows → ¬J.small x →
      ∃ c : Set W2, c ⊆ x ∧ H.IsClique c ∧ typeLT c = ω_ 1) :
    ∃ x : Set W2, x ⊆ rows ∧ ¬J.small x ∧
      ∃ domain : Set W2, domain ⊆ future ∧ IsStationary domain ∧
        ∀ b ∈ domain, J.small (x ∩ {v | H.Adj v b}) := by
  classical
  obtain ⟨family, hfamily⟩ := exists_maximal_centered J H rows future hrows
  have hclique := centered_family_red J G H hcompl rows future a hr hf hblue hcore
    hfamily.1.1 hfamily.1.2
  have hnoncofinal : ¬IsCofinal family := by
    intro hcof
    exact hred ⟨family, hclique, Erdos1172Part3Failure.typeLT_eq_omegaTwo_of_mk_eq
      (mk_eq_alephTwo_of_isCofinal hcof)⟩
  obtain ⟨bound, hbound⟩ := not_isCofinal_iff.mp hnoncofinal
  let later : Set W2 := future ∩ Set.Ioi bound
  have hlater : IsStationary later := stationary_inter_club hfuture
    (Set.isClub_Ioi_of_aleph0_lt_cof alephZero_lt_cof_W2 bound)
  have witness (b : later) : ∃ t : Finset W2, (↑t : Set W2) ⊆ family ∧
      J.small (rowsMeet H rows t ∩ {x | H.Adj x b.val}) := by
    have hb : b.val ∉ family := fun h => (hbound b.val h).asymm b.property.2
    have hnot : ¬Centered J H rows (insert b.val family) := by
      intro hcenter
      have hi : insert b.val family ⊆ future := Set.insert_subset b.property.1 hfamily.1.1
      exact hb (hfamily.2 ⟨hi, hcenter⟩ (Set.subset_insert _ _) (Set.mem_insert _ _))
    unfold Centered at hnot
    push Not at hnot
    obtain ⟨t, ht, hsmall⟩ := hnot
    refine ⟨t.erase b.val, ?_, J.mono ?_ hsmall⟩
    · intro x hx
      rcases Finset.mem_erase.mp hx with ⟨hxb, hxt⟩
      exact (Set.mem_insert_iff.mp (ht hxt)).resolve_left hxb
    · intro x hx
      refine ⟨hx.1.1, ?_⟩
      intro y hyt
      by_cases hyb : y = b.val
      · subst y
        exact hx.2
      · exact hx.1.2 y (Finset.mem_erase.mpr ⟨hyb, hyt⟩)
  let Witness := {t : Finset W2 // (↑t : Set W2) ⊆ family}
  have hfamilyCard : #family ≤ ℵ_ 1 := by
    have he : #family ≤ #(Set.Iio bound) := Cardinal.mk_le_of_injective
      (f := fun b : family => (⟨b.val, hbound b.val b.property⟩ : Set.Iio bound))
      (fun _ _ h => Subtype.ext (congrArg (fun z : Set.Iio bound => z.val) h))
    apply he.trans
    exact Erdos1172Part3CountableRankClosure.mk_local_le (Embedding.refl W2) bound
  have hWitness : #Witness < ℵ_ 2 := by
    obtain ⟨e⟩ : Nonempty (family ↪ ErdosRadoCHAsym.W1) := (Cardinal.le_def _ _).mp (by
      simpa only [ErdosRadoCHAsym.W1, Cardinal.mk_toType, Ordinal.card_omega] using hfamilyCard)
    have hcard : #Witness = #(Finset family) := Cardinal.mk_congr
      (Equiv.finsetSubtypeComm (fun x : W2 => x ∈ family)).symm
    rw [hcard]
    have hle : #(Finset family) ≤ #(Finset ErdosRadoCHAsym.W1) :=
      Cardinal.mk_le_of_injective (Finset.map_injective e)
    have hinfinite : Infinite ErdosRadoCHAsym.W1 := by
      apply Cardinal.aleph0_le_mk_iff.mp
      simp only [ErdosRadoCHAsym.W1, Cardinal.mk_toType, Ordinal.card_omega]
      exact Cardinal.aleph0_le_aleph 1
    rw [Cardinal.mk_finset_of_infinite ErdosRadoCHAsym.W1] at hle
    apply hle.trans_lt
    simpa only [ErdosRadoCHAsym.W1, Cardinal.mk_toType, Ordinal.card_omega] using
      (Cardinal.aleph_lt_aleph.mpr (by norm_num : (1 : Ordinal.{0}) < 2))
  let chosen : later → Witness := fun b => ⟨(witness b).choose, (witness b).choose_spec.1⟩
  obtain ⟨t, ht⟩ := exists_stationary_fiber_of_small hWitness hlater chosen
  let domain : Set W2 := {b | ∃ hb : b ∈ later, chosen ⟨b, hb⟩ = t}
  refine ⟨rowsMeet H rows t.val, fun _ hx => hx.1, hfamily.1.2 t.val t.property,
    domain, ?_, ht, ?_⟩
  · rintro b ⟨hb, _⟩
    exact hb.1
  · rintro b ⟨hb, heq⟩
    have h := (witness ⟨b, hb⟩).choose_spec.2
    have hval : (witness ⟨b, hb⟩).choose = t.val := congrArg Subtype.val heq
    rwa [hval] at h

end Erdos1172Part3CenteredStationaryLoss
