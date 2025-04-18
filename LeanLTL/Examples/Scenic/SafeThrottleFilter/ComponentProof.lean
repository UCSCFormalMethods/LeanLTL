import LeanLTL.Examples.Scenic.SafeThrottleFilter.Lib

open LeanLTL
open LeanLTL.Notation
open TraceSet

namespace SafeThrottleFilter

theorem imp_assumptions : ⊨ LLTL[(assumptions ∧ fprops) → guarantees] := by
  simp only [le_top, inf_of_le_right, fprops]
  rintro t ⟨hF0, hF1, hF2⟩
  simp only [F0, F1, F2] at *
  simp [guarantees, G0]

  simp only [sat_globally_iff, sat_wshift_iff, sat_imp_iff]
  intro n h_n h1
  simp [sat_sget_iff] at h1
  obtain ⟨h_next_ts, d, hd, h1⟩ := h1
  simp [push_ltl] at hF1 hF2
  have : ↑(n + 1) < t.length := by
    clear hd h1 hF1 hF2
    revert h_n h_next_ts
    cases t.length
    · simp
    · norm_cast; omega

  specialize hF1 (n + 1) this
  specialize hF2 n h_n
  simp [h_next_ts, CF_N1, CF_N2, CF] at hF1 hF2
  simp [push_ltl, h_next_ts]
  simp [push_ltl] at hF1 hF2
  simp [add_comm 1]
  rw [← hF1]

  cases ht : t.shift n h_n using Trace.unshift_cases with
  | singleton s =>
    have := congrArg Trace.length ht
    simp at this
    rw [this] at h_next_ts
    simp at h_next_ts
  | unshift s t' => ?_

  have ht' : t.shift (n + 1) this = t' := by
    simp only [add_comm n]
    rw [← Trace.shift_shift]
    simp [ht]
    assumption
    simpa
  simp only [add_comm 1 n, ht', ht, TraceFun.of_eval!_apply_unshift] at hd h1 hF1 hF2 ⊢

  simp [push_ltl] at h1 hd
  cases hd

  cases t' using Trace.unshift_cases with
  | singleton s' | unshift s' _ =>
    simp at hF1 hF2 h1 ⊢
    rw [hF1]
    simp [ComponentFunc] at hF1
    split at hF1
    · rename_i hh
      simp at hF1
      rw [← hF1]
      norm_num
    · rename_i hh
      simp at hF1
      simp [ComponentFunc, hh, hF1] at hF2
      split at hF2
      · simp at hF2
        simp_all
        linarith
      · simp at hF2
        simp_all
        linarith
