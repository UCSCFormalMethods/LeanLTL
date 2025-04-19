import LeanLTL.Examples.Scenic.SafeThrottleFilter.Lib

open LeanLTL
open LeanLTL.Notation
open TraceSet

namespace SafeThrottleFilter

theorem imp_assumptions : ⊨ LLTL[(assumptions ∧ fprops) → guarantees] := by
  simp only [le_top, inf_of_le_right, fprops]
  rintro t ⟨-, hF1, hF2⟩
  simp only [F0, F1, F2] at *
  simp [guarantees, G0]

  simp only [sat_globally_iff, sat_wshift_iff, sat_imp_iff]
  intro n h_n h1
  simp [sat_sget_iff] at h1
  obtain ⟨_, ⟨h_next_ts, rfl⟩, d, hd, h1⟩ := h1
  simp [push_ltl, h_next_ts] at hd
  cases hd
  simp [push_ltl] at hF1 hF2
  have : ↑(n + 1) < t.length := by
    clear h1 hF1 hF2
    revert h_n h_next_ts
    cases t.length
    · simp
    · norm_cast; omega
  specialize hF1 (n + 1) this
  specialize hF2 n h_n
  simp [h_next_ts, CF_N1, CF_N2, CF, push_ltl, ComponentFunc] at hF1 hF2
  simp [push_ltl, h_next_ts] at h1 ⊢
  simp [add_comm 1] at *
  split at hF1 <;> simp at hF1
  · rw [← hF1]
    norm_num
  · split at hF2 <;> simp_all <;> linarith
