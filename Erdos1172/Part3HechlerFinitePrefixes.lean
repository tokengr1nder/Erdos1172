/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3HechlerStagesAfterLimit

@[expose] public section

open Cardinal Ordinal Set Order

namespace Erdos1172Part3HechlerFinitePrefixes

open Erdos1172Part3CountableHechlerLimit
open Erdos1172Part3IteratedHechlerOrder (base_le)

structure Prefix (hGCH : GCH) (n : ℕ) where
  point : ∀ k : ℕ, k ≤ n → At hGCH k
  coherent : ∀ k (hk : k < n),
    (point (k + 1) (Nat.succ_le_of_lt hk)).base = point k hk.le

variable {hGCH : GCH} {n : ℕ}

noncomputable def singleton (p : At hGCH 0) : Prefix hGCH 0 where
  point k hk := by
    have heq : k = 0 := Nat.le_zero.mp hk
    exact heq.symm ▸ p
  coherent k hk := (Nat.not_lt_zero k hk).elim

noncomputable def append (p : Prefix hGCH n) (q : At hGCH (n + 1))
    (hbase : q.base = p.point n le_rfl) : Prefix hGCH (n + 1) := by
  let f (k : ℕ) (hk : k ≤ n + 1) : At hGCH k :=
    if hkn : k ≤ n then p.point k hkn else by
      have heq : k = n + 1 := by omega
      exact heq.symm ▸ q
  refine ⟨f, ?_⟩
  intro k hk
  by_cases hkn : k < n
  · dsimp only [f]
    rw [dif_pos (Nat.succ_le_of_lt hkn), dif_pos hkn.le]
    exact p.coherent k hkn
  · have heq : k = n := by omega
    subst k
    dsimp only [f]
    rw [dif_neg (by omega : ¬n + 1 ≤ n), dif_pos le_rfl]
    exact hbase

theorem append_point_of_le (p : Prefix hGCH n) (q : At hGCH (n + 1))
    (hbase : q.base = p.point n le_rfl) (k : ℕ) (hk : k ≤ n) :
    (append p q hbase).point k (hk.trans (Nat.le_succ n)) = p.point k hk := by
  dsimp only [append]
  rw [dif_pos hk]

theorem append_point_last (p : Prefix hGCH n) (q : At hGCH (n + 1))
    (hbase : q.base = p.point n le_rfl) :
    (append p q hbase).point (n + 1) le_rfl = q := by
  dsimp only [append]
  rw [dif_neg (by omega : ¬n + 1 ≤ n)]

/-- Every finite-stage strengthening has a coherent finite prefix below
the corresponding prefix of the original limit condition. -/
theorem exists_prefix_below (p : Limit hGCH) : ∀ n : ℕ, ∀ q : At hGCH n,
    q ≤ p.point n → ∃ segment : Prefix hGCH n,
      segment.point n le_rfl = q ∧ ∀ k hk, segment.point k hk ≤ p.point k := by
  intro n
  induction n with
  | zero =>
    intro q hq
    refine ⟨singleton q, rfl, ?_⟩
    intro k hk
    have heq : k = 0 := Nat.le_zero.mp hk
    subst k
    exact hq
  | succ n ih =>
    intro q hq
    have hbase : q.base ≤ p.point n := by
      have h := base_le hq
      rwa [p.coherent n] at h
    obtain ⟨segment, hlast, hprefix⟩ := ih q.base hbase
    refine ⟨append segment q hlast.symm, append_point_last _ _ _, ?_⟩
    intro k hk
    by_cases hkn : k ≤ n
    · rw [append_point_of_le segment q hlast.symm k hkn]
      exact hprefix k hkn
    · have heq : k = n + 1 := by omega
      subst k
      rw [append_point_last]
      exact hq

end Erdos1172Part3HechlerFinitePrefixes
