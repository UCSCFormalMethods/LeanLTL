import LeanLTL.Examples.Scenic.AccurateDistanceKnownRefinement.Lib

open LeanLTL
open LeanLTL.Notation
open TraceSet

namespace AccurateDistanceKnownRefinement

theorem imp_guarantees : ⊨ LLTL[(assumptions ∧ i_guarantees) → guarantees] := by
  simp [assumptions, i_guarantees, TraceSet.sem_entail_iff, TraceSet.sat_imp_iff,
    A0, A1, IG0, IG1, IG2, IG3, IG4, G0, sat_and_iff]
  intro t hA0 hA1 hA2 hIG0 hIG1 hIG2 hIG3 hIG4
  simp [sat_globally_iff, sat_wshift_iff, sat_imp_iff] at *

  intro n h_n h_bc
  specialize hIG0 n h_n h_bc
  specialize hIG2 n h_n h_bc
  specialize hIG4 n h_n

  simp [push_ltl] at hIG0 hIG2 hIG4 ⊢

  generalize (t.toFun! n).N0 = N0 at *
  generalize (t.toFun! n).N1 = N1 at *
  generalize (t.toFun! n).N2 = N2 at *
  generalize (t.toFun! n).N3 = N3 at *
  generalize (t.toFun! n).N4 = N4 at *

  by_cases h1: N0 < N1 <;> by_cases h2: N1 < N2 <;> simp_all

  have : N0 ⊔ N1 = N1 := by exact max_eq_right_of_lt h1
  simp [this]; exact hIG2.left

  have : N1 ⊔ N2 = N2 := by exact max_eq_right_of_lt h2
  simp [this]

  by_cases h3 : N0 < N2
  have : N0 ⊓ N2 = N0 := by exact min_eq_left_of_lt h3
  simp [this]; exact hIG0.left

  simp at h3
  by_cases h4: N2 = N0 <;> simp_all
  linarith
