import LeanLTLExamples.Scenic.KeepsDistanceRefinement.Lib

open LeanLTL
open LeanLTL.Notation
open TraceSet

namespace KeepsDistanceRefinement

set_option maxHeartbeats 10000000

-- Constants
abbrev min_dist : TraceFun TraceState ℚ := LLTLV[5]
abbrev max_brake : TraceFun TraceState ℚ := LLTLV[0.9]
abbrev max_accel : TraceFun TraceState ℚ := LLTLV[0.5]
abbrev perception_distance : TraceFun TraceState ℚ := LLTLV[1000]
abbrev abs_dist_err : TraceFun TraceState ℚ := LLTLV[0.1]
abbrev abs_speed_err : TraceFun TraceState ℚ := LLTLV[1.6]
abbrev max_speed : TraceFun TraceState ℚ := LLTLV[5.4]

-- # Lemmas
lemma max_rdc_change :
    ⊨ LLTL[(assumptions ∧ i_guarantees) → 𝐆 ((𝐗 (← rel_dist_covered)) ≤ (0 ⊔ ((← max_rdc_delta) + (← rel_dist_covered))))] := by
  -- Setup
  intro t h
  have a_ig := h
  repeat rw [sat_and_iff] at h
  rcases h with ⟨⟨hA0, hA1, hA2, hA3, hA4, hA5, hA6⟩, ⟨hIG0, hIG1, hIG2, hIG3⟩⟩
  simp only [A0, A1, A2, A3, A4, A5, A6, IG0, IG1, IG2, IG3] at *

  simp [push_ltl]
  intro n h_n
  have h_n' : 1 < t.length - n := by
    rw [sat_globally_iff] at hA6
    specialize hA6 n
    simp [push_ltl, h_n] at hA6
    exact hA6.1
  use ↑⌈(t.toFun! (1 + n)).N5 / 0.9⌉ * ((t.toFun! (1 + n)).N5 - (t.toFun! (1 + n)).N3 + 1.6)
  simp only [and_true, h_n', true_and]

  have h_n'' : ↑(n + 1) < t.length := by
    revert h_n'
    cases t.length
    · simp
    · norm_cast; omega

  simp [push_ltl] at hA1 hA3 hA4
  have hA1_1 := hA1 n h_n
  have hA2_2 := hA1 (n + 1) h_n''
  specialize hA3 n h_n
  specialize hA4 n h_n
  simp [h_n', add_comm 1] at hA3 hA4 ⊢

  let N4 := (t.toFun! n).N4
  let N3 := (t.toFun! n).N3
  let N5 := (t.toFun! n).N5
  let XN4 := (t.toFun! (n + 1)).N4
  let XN3 := (t.toFun! (n + 1)).N3
  let XN5 := (t.toFun! (n + 1)).N5
  revert hA1_1 hA2_2 hA3 hA4
  refold_let N4 N3 N5 XN4 XN3 XN5
  intro hA1_1 hA2_2 hA3 hA4

  have h_ST_pos : 0 ≤ ⌈(N5 + 0.5) / 0.9⌉ := by
    refine Int.ceil_nonneg ?_
    ring_nf; linarith

  have h_XST_pos : 0 ≤ ⌈XN5 / 0.9⌉ := by
    refine Int.ceil_nonneg ?_
    ring_nf; linarith

  have h_le : (XN5 - XN3 + 0.6) ≤ (N5 - N3 + 0.9 + 0.5 + 0.6) := by
    nlinarith

  have : ⌈XN5 / 0.9⌉ ≤ ⌈(N5 + 0.5) / 0.9⌉ := by
    refine Int.ceil_le_ceil ?_
    ring_nf at *; nlinarith

  by_cases h_neg1: (N5 - N3 + 0.9 + 0.5 + 1.6) ≤ 0
  . have h_neg2: (XN5 - XN3 + 0.4) ≤ 0 := by linarith
    left
    simp at h_neg2
    qify at *; nlinarith

  right
  simp at h_neg1
  by_cases h_neg2: (XN5 - XN3 + 0.6) ≤ 0
  . qify at *; nlinarith

  simp at h_neg2
  qify at *; nlinarith

-- Show trivial safety if we are outside the buffer distance.
lemma gt_bd_safety : ⊨ LLTL[(assumptions ∧ i_guarantees) → 𝐆 (((← lead_dist) > (← buffer_dist)) → ((← lead_dist) > (← min_dist)))] := by
  -- Setup
  simp [TraceSet.sem_imp]
  intro t h
  have a_ig := h
  repeat rw [sat_and_iff] at h
  rcases h with ⟨⟨hA0, hA1, hA2, hA3, hA4, hA5, hA6⟩, ⟨hIG0, hIG1, hIG2, hIG3⟩⟩
  simp only [A0, A1, A2, A3, A4, A5, A6, IG0, IG1, IG2, IG3] at *

  simp [push_ltl]
  intro n h_n h

  have : t.shift n h_n ⊨ LLTL[0 ≤ 0 ⊔ ((← max_rdc_delta) + (← rel_dist_covered))] := by simp [push_ltl]
  simp [push_ltl, -le_sup_iff, -le_sup_left] at this

  linarith

lemma le_bd_imp_bc : ⊨ LLTL[(assumptions ∧ i_guarantees) → 𝐆 (((← lead_dist) ≤ (← buffer_dist)) → (← behind_car))] := by
  -- Setup
  intro t h
  have a_ig := h
  repeat rw [sat_and_iff] at h
  rcases h with ⟨⟨hA0, hA1, hA2, hA3, hA4, hA5, hA6⟩, ⟨hIG0, hIG1, hIG2, hIG3⟩⟩
  simp only [A0, A1, A2, A3, A4, A5, A6, IG0, IG1, IG2, IG3] at *

  simp [sat_globally_iff, sat_wshift_iff, sat_imp_iff]
  intro n h_n h
  simp [push_ltl] at h ⊢
  refine ⟨_, Iff.rfl, ?_⟩

  by_cases h_sup : t.shift n h_n ⊨ LLTL[((← max_rdc_delta) + (← rel_dist_covered)) ≤ 0] <;> simp [push_ltl] at h_sup
  . have : t.shift n h_n ⊨ LLTL[(0 ⊔ ((← max_rdc_delta) + (← rel_dist_covered))) = 0] := by simp [push_ltl]; trivial
    simp [push_ltl, -sup_eq_left] at this
    simp [this] at h
    simp
    linarith

  have : t.shift n h_n ⊨ LLTL[(0 ⊔ ((← max_rdc_delta) + (← rel_dist_covered))) = ((← max_rdc_delta) + (← rel_dist_covered))] := by
    simp [push_ltl]; linarith
  simp [push_ltl, -sup_eq_right] at this
  simp [this] at h

  have ST_bounds : t.shift n h_n ⊨ LLTL[0 ≤ ⌈((← self.speed) + (← max_accel))/(← max_brake)⌉ ∧ ⌈((← self.speed) + (← max_accel))/(← max_brake)⌉ ≤ ⌈((← max_speed) + (← max_accel))/(← max_brake)⌉] := by
    simp [push_ltl]

    simp [push_ltl] at hA1
    specialize hA1 n h_n

    constructor
    . refine Int.ceil_nonneg ?_
      ring_nf; linarith
    . refine Int.ceil_le_ceil ?_
      ring_nf; linarith
  simp [push_ltl] at ST_bounds
  rcases ST_bounds with ⟨ST_bound1, ST_bound2⟩

  simp [push_ltl] at hA1 hA2
  specialize hA1 n h_n
  specialize hA2 n h_n

  ring_nf at *
  generalize ⌈5 / 9 + ((t.shift n h_n).toFun! 0).N5 * (10 / 9)⌉ = ST at *

  interval_cases using ST_bound1, ST_bound2 <;> linarith

lemma le_nbc_imp_ld_bd : ⊨ LLTL[(assumptions ∧ i_guarantees) → 𝐆 ((𝐗ˢ ((← lead_dist) ≤ (← buffer_dist))) → (← behind_car))] := by
  -- Setup
  intro t h
  have a_ig := h
  repeat rw [sat_and_iff] at h
  rcases h with ⟨⟨hA0, hA1, hA2, hA3, hA4, hA5, hA6⟩, ⟨hIG0, hIG1, hIG2, hIG3⟩⟩
  simp only [A0, A1, A2, A3, A4, A5, A6, IG0, IG1, IG2, IG3] at *

  simp [sat_globally_iff, sat_wshift_iff, sat_imp_iff]
  intro n h_n h_bc
  simp [push_ltl] at h_bc
  obtain ⟨h_1t_mn, h_bc⟩ := h_bc

  have h_n'' : ↑(n + 1) < t.length := by
    revert h_1t_mn
    cases t.length
    · simp
    · norm_cast; omega

  have ST_bounds : t.shift (n+1) h_n'' ⊨
      LLTL[0 ≤ ⌈((← self.speed)+(← max_accel))/(← max_brake)⌉ ∧ ⌈((← self.speed)+(← max_accel))/(← max_brake)⌉ ≤ ⌈((← max_speed)+(← max_accel))/(← max_brake)⌉] := by
    simp [push_ltl]

    simp [push_ltl] at hA1
    specialize hA1 (n+1) h_n''

    constructor
    . refine Int.ceil_nonneg ?_
      ring_nf at *; linarith
    . refine Int.ceil_le_ceil ?_
      ring_nf at *; linarith
  simp [push_ltl] at ST_bounds
  rcases ST_bounds with ⟨ST_bound1, ST_bound2⟩


  simp [push_ltl] at hA1 hA2 hA6 ⊢
  have hA1_1 := hA1 n h_n
  have hA2_1 := hA2 n h_n
  have hA1_2 := hA1 (n+1) h_n''
  have hA2_2 := hA2 (n+1) h_n''
  specialize hA6 n h_n
  simp [h_1t_mn] at hA6

  simp only [add_comm 1 n] at *

  let N4 := (t.toFun! n).N4
  let XN4 := (t.toFun! (n + 1)).N4
  let XN3 := (t.toFun! (n + 1)).N3
  let XN5 := (t.toFun! (n + 1)).N5
  revert hA1_1 hA2_1 hA1_2 hA2_2 h_bc hA6
  refold_let N4 XN4 XN3 XN5
  intro hA1_1 hA2_1 hA1_2 hA2_2 h_bc hA6
  refine ⟨_, Iff.rfl, ?_⟩

  simp [hA6] at h_bc

  by_cases h_neg : ↑⌈(XN5 + 0.5) / 0.9⌉ * (XN5 - XN3 + 0.9 + 0.5 + 1.6) ≤ 0
  · simp at h_neg
    simp [h_neg] at h_bc
    ring_nf at *; linarith

  simp at h_neg
  have : 0 ⊔ ↑⌈(XN5 + 0.5) / 0.9⌉ * (XN5 - XN3 + 0.9 + 0.5 + 1.6) = ↑⌈(XN5 + 0.5) / 0.9⌉ * (XN5 - XN3 + 0.9 + 0.5 + 1.6) := by
    exact max_eq_right_of_lt h_neg
  simp [this] at h_bc

  generalize ⌈(XN5 + 0.5) / 0.9⌉ = ST at *
  ring_nf at *
  interval_cases using ST_bound1, ST_bound2 <;> linarith

-- lead_dist ≤ buffer_dist always implies our next speed will be 0 or decrease by min_slowdown.
lemma le_bd_slowdown : ⊨ LLTL[(assumptions ∧ i_guarantees) →
    𝐆 (((← lead_dist) ≤ (← buffer_dist)) →
      (((𝐗 (← self.speed)) = 0) ∨ ((𝐗 (← self.speed)) = (← self.speed) - 0.9)))] := by
  -- Setup
  intro t h
  have a_ig := h
  repeat rw [sat_and_iff] at h
  rcases h with ⟨⟨hA0, hA1, hA2, hA3, hA4, hA5, hA6⟩, ⟨hIG0, hIG1, hIG2, hIG3⟩⟩
  simp only [A0, A1, A2, A3, A4, A5, A6, IG0, IG1, IG2, IG3] at *

  simp [sat_globally_iff, sat_wshift_iff, sat_imp_iff]
  intro n' h_n' h_ld_bd

  have h_n'' : 1 < t.length - n' := by
    rw [sat_globally_iff] at hA6
    specialize hA6 n'
    simp [push_ltl, h_n'] at hA6
    exact hA6.1
  have h_n''' : ↑(n' + 1) < t.length := by
    revert h_n''
    cases t.length
    · simp
    · norm_cast; omega

  -- Extract guarantee about behind_car using le_bd_imp_bc
  have le_bd_imp_bc := le_bd_imp_bc
  simp [TraceSet.sem_imp] at le_bd_imp_bc
  specialize le_bd_imp_bc t a_ig
  simp [sat_globally_iff, sat_wshift_iff, sat_imp_iff] at le_bd_imp_bc
  specialize le_bd_imp_bc n' h_n' h_ld_bd

  have : ¬ (n' = 0) := by
    by_contra; rename_i contra
    simp [push_ltl, contra] at h_ld_bd hA5
    linarith

  have h_nm1 : n' - 1 < t.length := by exact tsub_lt_of_lt h_n'
  have h_tl_nm1 : 1 < t.length - (↑n' - 1) := by
    -- have foo := h_n'
    clear h_ld_bd le_bd_imp_bc
    generalize t.length = tl at h_n' ⊢
    cases tl
    . exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
    norm_cast at h_n' ⊢
    omega

  have nmp1 : 1 + (n' - 1) = n' := by omega

  -- Extract guarantees about perception system output
  simp [sat_globally_iff, sat_wshift_iff, sat_imp_iff, sat_and_iff] at hIG0
  have hIG0' := hIG0
  specialize hIG0 n' h_n' le_bd_imp_bc
  rcases hIG0 with ⟨hIG0_1, hIG0_2⟩


  have le_nbc_imp_ld_bd := le_nbc_imp_ld_bd
  simp [TraceSet.sem_entail_iff, sat_globally_iff, sat_wshift_iff, sat_imp_iff] at le_nbc_imp_ld_bd
  specialize le_nbc_imp_ld_bd t a_ig (n' - 1) h_nm1 (by
    simp [push_ltl]
    use h_tl_nm1
    simp [nmp1]
    simp [push_ltl] at h_ld_bd
    trivial
  )

  -- Extract guarantees about control system signals
  have h_pd_bd_err : t.shift (n' - 1) h_nm1 ⊨ LLTL[(𝐗 (← SCENIC_INTERNAL_VAR_0)) ≤ (← p_buffer_dist) + 0.1] := by
    simp [push_ltl] at hIG0_2 h_ld_bd hA1 ⊢
    specialize hA1 n' h_n'
    simp [h_tl_nm1, nmp1]
    refine le_trans hIG0_2 ?_
    rw [← le_sub_iff_add_le]
    refine le_trans h_ld_bd ?_
    simp only [add_sub_cancel_right, add_le_add_iff_right, add_le_add_iff_left, le_refl, true_and]

    simp [push_ltl] at hIG1
    specialize hIG1 n' h_n'

    simp [push_ltl] at hA6
    specialize hA6 (n'-1) h_nm1
    simp [h_tl_nm1, nmp1] at hA6

    generalize h_N0: (t.toFun! (n'-1)).N0 = N0 at *
    generalize h_XN0: (t.toFun! n').N0 = XN0 at *
    generalize h_N1: (t.toFun! n').N1 = N1 at *
    generalize h_N3: (t.toFun! n').N3 = N3 at *
    generalize h_N5: (t.toFun! n').N5 = N5 at *

    have : ⌈(N5 + 0.5) / 0.9⌉ ≥ 0 := by
      refine Int.ceil_nonneg ?_
      ring_nf at *; linarith


    simp only [hIG1, le_refl, true_and]

    have : (N5 - N3) ≤ (N0 - XN0 + 1.6) := by
      simp [push_ltl] at hA3 hA4
      specialize hIG0' (n'-1) h_nm1 le_nbc_imp_ld_bd
      specialize hA3 (n'-1) h_nm1
      specialize hA4 (n'-1) h_nm1
      simp [push_ltl, h_tl_nm1,nmp1,h_N3, h_N5] at hA3 hA4 hIG0'
      ring_nf at *; nlinarith

    have : (N5 - N3 + 0.9 + 0.5 + 1.6) ≤ (N0 - XN0 + 0.9 + 0.5 + 2 * 1.6) := by
      ring_nf; linarith

    by_cases h_neg: (N0 - XN0 + 0.9 + 0.5 + 2 * 1.6) ≤ 0
    . have : (N5 - N3 + 0.9 + 0.5 + 1.6) ≤ 0 := by linarith

      have : ⌈(N5 + 0.5) / 0.9⌉ * (N5 - N3 + 0.9 + 0.5 + 1.6) ≤ 0 := by ring_nf at *; qify at *; nlinarith
      simp [this]

    simp at h_neg
    have : ↑⌈(N5 + 0.5) / 0.9⌉ * (N0 - XN0 + 0.9 + 0.5 + 2 * 1.6) ≥ 0 := by ring_nf at *; qify at *; nlinarith
    simp [this]

    ring_nf at *; qify at *; nlinarith

  simp [sat_globally_iff, sat_wshift_iff, sat_imp_iff] at hIG2
  specialize hIG2 (n'-1) h_nm1 h_pd_bd_err

  -- Extract guarantee about braking effect
  simp [sat_globally_iff, sat_wshift_iff, sat_imp_iff] at hIG3
  specialize hIG3 (n') h_n' (by
    simp [push_ltl] at hIG2 ⊢
    simp [h_tl_nm1] at hIG2 ⊢
    simp [nmp1] at hIG2
    trivial
  )

  exact hIG3

-- def n₀_reqs (t: Trace TraceState) (n: ℕ) (h_n: n < t.length) (n₀: ℕ):=
--   ∃ (h_n₀_n : n₀ ≤ n),
--   (((t.shift (n₀-1) (by sorry))⊨FLTL[lead_dist > buffer_dist])
--   ∧ (∀ (n_i: ℕ) (h_nb_bound : (n₀ ≤ n_i) ∧ (n_i ≤ (n))),
--     (((t.shift (n_i) (by sorry))⊨FLTL[lead_dist ≤ buffer_dist]))))

def n₀_reqs (t: Trace TraceState) (n: ℕ) (h_n: n < t.length) (n₀: ℕ) :=
  ∃ (h_n₀_n : n₀ ≤ n),
  (((t.shift (n₀-1) (by
    revert h_n h_n₀_n; cases t.length; simp only [ENat.coe_lt_top, implies_true]; norm_cast; omega
  )) ⊨ LLTL[(← lead_dist) > (← buffer_dist)])
  ∧ (∀ (n_i: ℕ) (h_nb_bound : (n₀ ≤ n_i) ∧ (n_i ≤ (n))),
    (((t.shift n_i (by
      revert h_n h_n₀_n; cases t.length; simp only [ENat.coe_lt_top, implies_true]; norm_cast; omega
    )) ⊨ LLTL[(← lead_dist) ≤ (← buffer_dist)]))))

lemma braking_block_bounds (t : Trace TraceState) (h : t ⊨ LLTL[assumptions ∧ i_guarantees])
    (n : ℕ) (h_n : n < t.length)
    (h_n_le_bd : t.shift n h_n ⊨ LLTL[(← lead_dist) ≤ (← buffer_dist)]) :
    ∃ (n₀: ℕ), (n₀_reqs t n h_n n₀) := by
  -- Setup
  have a_ig := h
  repeat rw [sat_and_iff] at h
  rcases h with ⟨⟨hA0, hA1, hA2, hA3, hA4, hA5, hA6⟩, ⟨hIG0, hIG1, hIG2, hIG3⟩⟩
  simp only [A0, A1, A2, A3, A4, A5, A6, IG0, IG1, IG2, IG3] at *

  simp [n₀_reqs]

  -- We will choose the the timestep after the latest timestep from the set
  -- of timesteps less than n, where lead_dist > buffer_dist
  let sn' := {n' : ℕ | ∃ (h_n': n' < n),
    (t.shift n' (gt_trans h_n (ENat.coe_lt_coe.mpr h_n')) ⊨ LLTL[(← lead_dist) > (← buffer_dist)])}
  use (sSup sn') + 1

  -- Show useful properties about this set
  simp only [add_tsub_cancel_right, and_imp, exists_and_left, exists_prop]
  have h_sn'_nempty : sn'.Nonempty := by
    simp only [Set.Nonempty]
    use 0
    simp [sn']
    constructor
    . by_contra; rename_i contra
      simp only [not_lt, nonpos_iff_eq_zero] at contra
      simp [contra] at h_n_le_bd
      rcases hA5 with ⟨hA5_1, _⟩
      simp [push_ltl] at h_n_le_bd hA5_1
      linarith
    . exact hA5.left
  have h_sn'_ba : BddAbove sn' := by
    simp [BddAbove, upperBounds, Set.Nonempty]
    use n
    intro a h_a_N3
    simp [sn'] at h_a_N3
    rcases h_a_N3 with ⟨h_a_N3, _⟩
    linarith

  have h_n'_mem := Nat.sSup_mem h_sn'_nempty h_sn'_ba
  obtain ⟨h_n'_lt, h_n'_mem⟩ := h_n'_mem
  use h_n'_lt

  constructor
  . simp [sn'] at h_n'_mem ⊢
    exact h_n'_mem
  . intro n_i h1
    by_contra; rename_i contra
    have := le_csSup h_sn'_ba (?_: n_i ∈ _)
    . linarith
    simp [sn']
    by_cases n_i = n <;> rename_i h_eq
    . simp [h_eq] at contra
      trivial
    use (by refine Nat.lt_of_le_of_ne h1.right h_eq)
    simp [push_ltl] at contra ⊢
    linarith

lemma bb_init_ld (t : Trace TraceState) (h : t ⊨ LLTL[assumptions ∧ i_guarantees])
    (n : ℕ) (h_n : n < t.length)
    (h_n_le_bd : t.shift n h_n ⊨ LLTL[(← lead_dist) ≤ (← buffer_dist)])
    (n₀ : ℕ) (h_n₀ : n₀_reqs t n h_n n₀)
    (i : ℕ) (h_i_bound: i ≤ n - n₀) :
    have h_n_i : n₀ + i < t.length := by
      simp [n₀_reqs] at h_n₀
      rcases h_n₀ with ⟨h_1, h_2, h_3⟩
      have : n₀ + i ≤ n := by omega
      have : (n₀ + i : ENat) ≤ n := by
        norm_cast
      exact lt_of_le_of_lt this h_n
    (lead_dist (t.shift (n₀ + i) h_n_i)).get (by simp [push_ltl])
    ≥ (min_dist (t.shift (n₀ + i) h_n_i)).get (by simp [push_ltl])
      + (0 ⊔ (rel_dist_covered (t.shift (n₀ + i) h_n_i)).get (by simp [push_ltl])) + 1 := by
  intro h_n₀_i
  clear_value h_n₀_i
  have a_ig := h
  repeat rw [sat_and_iff] at h
  rcases h with ⟨⟨hA0, hA1, hA2, hA3, hA4, hA5, hA6⟩, ⟨hIG0, hIG1, hIG2, hIG3⟩⟩
  simp only [A0, A1, A2, A3, A4, A5, A6, IG0, IG1, IG2, IG3] at *

  simp only [n₀_reqs] at h_n₀
  rcases h_n₀ with ⟨h_n₀_n, h_n₀_1, h_n₀_2⟩

  have : n₀ > 0 := by
    by_contra; rename_i contra
    simp at contra
    simp [contra] at *
    specialize h_n₀_2 0 (by omega)
    simp [push_ltl] at h_n₀_1 h_n₀_2
    linarith

  have h_n₀ : n₀ < t.length := by
    specialize h_n₀_2 n₀ (by constructor <;> omega)
    generalize_proofs at h_n₀_2; trivial
  have h_n₀_m1 : n₀-1 < t.length := by
    generalize_proofs at h_n₀_1; trivial

  induction i
  . simp [push_ltl] at hA1 hA2 hA6 ⊢

    have hA1_1 := hA1 (n₀-1) h_n₀_m1
    have hA1_2 := hA1 n₀ h_n₀
    have hA2_1 := hA2 (n₀-1) h_n₀_m1
    have hA2_2 := hA2 n₀ h_n₀
    specialize hA6 (n₀-1) h_n₀_m1

    have max_rdc_change := max_rdc_change
    simp [TraceSet.sem_imp, -le_sup_iff, -sup_le_iff] at max_rdc_change
    specialize max_rdc_change t a_ig
    simp [push_ltl, -le_sup_iff, -sup_le_iff] at max_rdc_change
    specialize max_rdc_change (n₀-1) h_n₀_m1

    have : 1 < t.length - (↑n₀ - 1) := by
      cases h_tl: t.length <;> simp [h_tl] at h_n h_n₀ ⊢
      . have : 1 + (↑n₀ - 1)< (⊤: ENat) := by exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
        exact (enat_cancel 1 (⊤ - (↑n₀ - 1)) (n₀ - 1)).mp this
      . norm_cast
        omega
    simp [this, -le_sup_iff, -sup_le_iff] at hA6 max_rdc_change

    have : 1 + (n₀ - 1) = n₀ := by omega
    simp [this, -le_sup_iff, -sup_le_iff] at hA6 max_rdc_change

    simp [push_ltl] at h_n₀_1

    generalize (t.toFun! (n₀ - 1)).N4 = N4 at *
    generalize (t.toFun! (n₀ - 1)).N3 = N3 at *
    generalize (t.toFun! (n₀ - 1)).N5 = N5 at *
    generalize (t.toFun! n₀).N4 = XN4 at *
    generalize (t.toFun! n₀).N3 = XN3 at *
    generalize (t.toFun! n₀).N5 = XN5 at *

    rw [hA6]

    have : 5 + 0 ⊔ ↑⌈(N5 + 0.5) / 0.9⌉ * (N5 - N3 + 0.9 + 0.5 + 1.6) + 1 ≤ N4 - (N5 - N3) := by linarith
    refine le_trans ?_ this

    have : 0 ⊔ ↑⌈XN5 / 0.9⌉ * (XN5 - XN3 + 1.6) ≤ 0 ⊔ ↑⌈(N5 + 0.5) / 0.9⌉ * (N5 - N3 + 0.9 + 0.5 + 1.6) := by
      by_cases this: ↑⌈XN5 / 0.9⌉ * (XN5 - XN3 + 1.6) ≥ 0
      . have : 0 ⊔ ↑⌈XN5 / 0.9⌉ * (XN5 - XN3 + 1.6) = ↑⌈XN5 / 0.9⌉ * (XN5 - XN3 + 1.6) := by
          exact max_eq_right this
        simp [this, -le_sup_iff, -sup_le_iff]
        exact max_rdc_change
      simp at this
      have : 0 ⊔ ↑⌈XN5 / 0.9⌉ * (XN5 - XN3 + 1.6) = 0 := by exact max_eq_left_of_lt this
      simp [this]

    ring_nf at *; linarith
  . rename_i i ih
    specialize ih (by omega)
    simp [push_ltl] at ih ⊢

    have : n₀ + (i + 1) = n₀ + i + 1 := by omega
    simp [this]

    have h_n₀_i : n₀ + i < t.length := by
      refine lt_trans ?_ h_n₀_i
      norm_cast
      omega

    simp [h_n₀_i] at ih

    generalize_proofs at *

    have h_n₀_i_1 : n₀ + i + 1 < t.length := by
      trivial

    simp [push_ltl] at hA1 hA2 hA3 hA4 hA6
    have hA1_1 := hA1 (n₀ + i) h_n₀_i
    have hA1_2 := hA1 (n₀ + i + 1) h_n₀_i_1
    specialize hA2 (n₀ + i) h_n₀_i
    specialize hA3 (n₀ + i) h_n₀_i
    specialize hA4 (n₀ + i) h_n₀_i
    specialize hA6 (n₀ + i) h_n₀_i

    have h_slowdown := le_bd_slowdown
    simp [TraceSet.sem_entail_iff, sat_globally_iff, sat_wshift_iff, sat_imp_iff] at h_slowdown
    specialize h_slowdown t a_ig (n₀ + i) h_n₀_i (h_n₀_2 (n₀ + i) (by constructor <;> omega))
    simp [push_ltl] at h_slowdown

    have : 1 < t.length - (↑n₀ + ↑i) := by
      cases h_tl: t.length
      . have : 1 + (↑n₀ + ↑i) < (⊤: ENat) := by
          exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
        exact (enat_cancel 1 (⊤ - (↑n₀ + ↑i)) ((fun x1 x2 => x1 + x2) n₀ i)).mp this
      . simp [h_tl] at h_n₀_i h_n₀_i_1
        norm_cast at *
        omega
    simp [this] at h_slowdown hA3 hA4 hA6

    simp [add_comm (n₀ + i) 1, hA6] at *

    generalize (t.toFun! (n₀ + i)).N4 = N4 at *
    generalize (t.toFun! (n₀ + i)).N3 = N3 at *
    generalize (t.toFun! (n₀ + i)).N5 = N5 at *
    generalize (t.toFun! (1 + (n₀ + i))).N4 = XN4 at *
    generalize (t.toFun! (1 + (n₀ + i))).N3 = XN3 at *
    generalize (t.toFun! (1 + (n₀ + i))).N5 = XN5 at *

    by_cases h_slowdown_case: XN5 = 0
    . subst h_slowdown_case

      by_cases this: N5 = 0
      . subst this
        simp at ih ⊢
        linarith

      have : ⌈N5 / 0.9⌉ = 1 := by
        refine Int.ceil_eq_iff.mpr ?_
        simp
        constructor <;> try (ring_nf at *; linarith)
        rcases hA1_1 with ⟨hA1_1, hA1_2⟩
        have : 0 < N5 := lt_of_le_of_ne hA1_1 fun a => this a.symm
        ring_nf at *; nlinarith
      simp [this] at ih

      by_cases this: (N5 - N3 + 1.6) < 0
      . have : 0 ⊔ (N5 - N3 + 1.6) = 0 := by exact max_eq_left_of_lt this
        simp [this] at ih
        simp
        ring_nf at *; nlinarith

      simp at this
      have : 0 ⊔ (N5 - N3 + 1.6) = (N5 - N3 + 1.6) := by exact max_eq_right this
      simp [this] at ih
      simp
      ring_nf at *; nlinarith

    . simp [h_slowdown_case] at h_slowdown
      simp [h_slowdown]
      have : ⌈(N5 - 0.9) / 0.9⌉ = ⌈N5 / 0.9⌉ - 1 := by
        have : (N5 - 0.9) / 0.9 = N5 / 0.9 - 1 := by ring
        rw [this]
        exact Int.ceil_sub_one (N5 / 0.9)
      simp [this]

      have : ⌈N5 / 0.9⌉ -1 ≥ 0 := by
        refine Int.sub_nonneg_of_le ?_
        refine Int.one_le_ceil_iff.mpr ?_
        have : XN5 ≥ 0 := by linarith
        have : 0 < N5 := by ring_nf at *; linarith
        ring_nf; linarith
      have : XN3 ≥ N3 - 0.9 := by
        ring_nf at *; linarith
      have : (N5 - 0.9 - XN3 + 1.6) ≤ (N5 - N3 + 1.6) := by ring_nf at *; linarith

      by_cases this : (N5 - N3 + 1.6) ≤ 0
      . have : (↑⌈N5 / 0.9⌉ - 1) * (N5 - 0.9 - XN3 + 1.6) ≤ 0 := by qify at *; nlinarith
        have : 0 ⊔ (↑⌈N5 / 0.9⌉ - 1) * (N5 - 0.9 - XN3 + 1.6) = 0 := by
          exact Eq.symm (eq_max rfl this fun {d} a a_1 => a)
        simp [this]
        have : ↑⌈N5 / 0.9⌉ * (N5 - N3 + 1.6) ≤ 0 := by qify at *; nlinarith
        have : 0 ⊔ ↑⌈N5 / 0.9⌉ * (N5 - N3 + 1.6) = 0 := by
          exact Eq.symm (eq_max rfl this fun {d} a a_1 => a)
        simp [this] at ih
        ring_nf at *; nlinarith

      simp at this
      have : ↑⌈N5 / 0.9⌉ * (N5 - N3 + 1.6) ≥ 0 := by qify at *; nlinarith
      have h_simp : 0 ⊔ ↑⌈N5 / 0.9⌉ * (N5 - N3 + 1.6) = ↑⌈N5 / 0.9⌉ * (N5 - N3 + 1.6) := by
        exact max_eq_right this
      simp [this] at ih

      have : (↑⌈N5 / 0.9⌉ - 1) * (N5 - 0.9 - XN3 + 1.6) ≤ (↑⌈N5 / 0.9⌉ - 1) * (N5 - N3 + 1.6) := by
        qify at *; ring_nf at *; nlinarith

      have : 0 ⊔ (↑⌈N5 / 0.9⌉ - 1) * (N5 - 0.9 - XN3 + 1.6) ≤ 0 ⊔ (↑⌈N5 / 0.9⌉ - 1) * (N5 - N3 + 1.6) := by
        exact sup_le_sup_left this 0

      have : 5 + 0 ⊔ (↑⌈N5 / 0.9⌉ - 1) * (N5 - 0.9 - XN3 + 1.6) + 1 ≤ 5 + 0 ⊔ (↑⌈N5 / 0.9⌉ - 1) * (N5 - N3 + 1.6) + 1 := by
        linarith

      refine le_trans this ?_

      have : (↑⌈N5 / 0.9⌉ - 1) * (N5 - N3 + 1.6) ≥ 0 := by qify at *; ring_nf at *; nlinarith

      have : 0 ⊔ (↑⌈N5 / 0.9⌉ - 1) * (N5 - N3 + 1.6) = (↑⌈N5 / 0.9⌉ - 1) * (N5 - N3 + 1.6) := by
        exact max_eq_right this
      simp [this]

      have : (↑⌈N5 / 0.9⌉ - 1) * (N5 - N3 + 1.6) = ↑⌈N5 / 0.9⌉ * (N5 - N3 + 1.6) - (N5 - N3 + 1.6):= by ring
      simp [this]

      linarith

-- # Proof
theorem imp_guarantees : ⊨ LLTL[(assumptions ∧ i_guarantees) → guarantees] := by
    -- Setup
  intro t h
  have a_ig := h
  repeat rw [sat_and_iff] at h
  rcases h with ⟨⟨hA0, hA1, hA2, hA3, hA4, hA5, hA6⟩, ⟨hIG0, hIG1, hIG2, hIG3⟩⟩
  simp only [A0, A1, A2, A3, A4, A5, A6, IG0, IG1, IG2, IG3] at *

  apply globally_induction t
  . simp [push_ltl] at hA5 ⊢
    rcases hA5 with ⟨hA5_1, hA5_2⟩
    simp [hA5_2] at hA5_1

    ring_nf at hA5_1

    generalize_proofs at hA5_1
    rename_i pf
    have : 0 ⊔ (3 - (t.toFun! 0).N3) ≥ 0 := by
      exact le_max_left 0 (3 - (t.toFun! 0).N3)

    linarith

  simp [sat_globally_iff, sat_wshift_iff, sat_imp_iff]
  intro n h_n ih h_1_n
  have h_n_1: n + 1 < t.length := by
    generalize h_tl : t.length = tl
    rw [h_tl] at h_1_n h_n
    cases tl
    . simp
    norm_cast at h_1_n h_n ⊢
    omega

  -- Dispatch case where lead_dist > buffer_dist
  by_cases (t.shift (n + 1) h_n_1) ⊨ LLTL[(← lead_dist) > (← buffer_dist)]
  . rename_i h_ld_gt_bd
    have gt_bd_safety := gt_bd_safety
    simp [TraceSet.sem_imp] at gt_bd_safety
    specialize gt_bd_safety t a_ig
    simp [sat_globally_iff, sat_wshift_iff, sat_imp_iff] at gt_bd_safety
    specialize gt_bd_safety (n+1) h_n_1 h_ld_gt_bd
    simp [add_comm 1]
    exact gt_bd_safety
  have h_ld_le_bd : t.shift (n + 1) h_n_1 ⊨ LLTL[(← lead_dist) ≤ (← buffer_dist)] := by
    rename_i goal
    simp [push_ltl] at goal ⊢
    trivial

  -- Establish start of the braking block
  obtain ⟨n₀, h_n₀'⟩ := braking_block_bounds t a_ig (n+1) h_n_1 h_ld_le_bd
  have h_n₀ := h_n₀'
  simp [n₀_reqs] at h_n₀'
  rcases h_n₀' with ⟨h_n₀_1, h_n₀_2, h_n₀_3⟩

  have bb_init_ld := bb_init_ld t a_ig (n+1) h_n_1 h_ld_le_bd n₀ h_n₀ (n + 1 - n₀) (by omega)
  simp [push_ltl] at bb_init_ld

  have : (n₀ + (n + 1 - n₀)) = n + 1 := by omega
  simp [this] at bb_init_ld

  simp [push_ltl]
  simp [add_comm 1 n] at *

  generalize h_N4: (t.toFun! (n + 1)).N4 = N4 at *
  generalize h_N3: (t.toFun! (n + 1)).N3 = N3 at *
  generalize h_N5: (t.toFun! (n + 1)).N5 = N5 at *

  have : 0 ⊔ ↑⌈N5 / 0.9⌉ * (N5 - N3 + 1.6) ≥ 0 := by
    exact le_max_left 0 _

  ring_nf at *; linarith
