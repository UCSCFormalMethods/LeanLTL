import LeanLTL

namespace LeanLTL.Examples

open LeanLTL
open scoped LeanLTL.Notation

-- TODO: Some sort of element, possible optional, that makes this more interesting and undecidable? Right now this could be solved
--       by LTL MT
-- TODO: Support naturals/integers instead of rationals
-- TODO: Rewrite this, maybe using quantifiers, to be more compact/support more lights?
-- TODO: Use quantifiers over max_arrives, max_departs, to make problem more interesting?
--         (e.g. prove we can avoid starvation if max_departs > max_arrives and there's always eventually a break in traffic)
--       Or is there a better way to represent constant values in state across formulas? We could do it by declaring a signal that never changes,
--       but maybe we can add a shorthand?

-- Traffic Light Example
structure ExState where
  (TL1Green TL2Green : Prop)
  (TL1Arrives TL1Departs TL1Queue : ℕ)
  (TL2Arrives TL2Departs TL2Queue : ℕ)
  deriving Inhabited
open ExState

abbrev max_arrives : ℕ := 2
abbrev max_departs : ℕ := 3

-- Base Properties
-- TODO: Get rid of red prop
abbrev TL1StartGreen    := LLTL[TL1Green]
abbrev TL2StartRed      := LLTL[¬TL2Green]

abbrev TL1ToTL2Green    := LLTL[𝐆 ((TL1Green ∧ ((←ˢ TL1Queue) = 0)) → (𝐗ˢ (¬TL1Green ∧ TL2Green)))]
abbrev TL2ToTL1Green    := LLTL[𝐆 ((TL2Green ∧ ((←ˢ TL2Queue) = 0)) → (𝐗ˢ (TL1Green ∧ ¬ TL2Green)))]
abbrev TL1StayGreen     := LLTL[𝐆 ((TL1Green ∧ ((←ˢ TL1Queue) ≠ 0)) → (𝐗ˢ (TL1Green ∧ ¬ TL2Green)))]
abbrev TL2StayGreen     := LLTL[𝐆 ((TL2Green ∧ ((←ˢ TL2Queue) ≠ 0)) → (𝐗ˢ (¬ TL1Green ∧ TL2Green)))]

abbrev TL1GreenDeparts  := LLTL[𝐆 (TL1Green → ((←ˢ TL1Departs) = max_departs))]
abbrev TL1RedDeparts    := LLTL[𝐆 (¬TL1Green → ((←ˢ TL1Departs) = 0))]
abbrev TL2GreenDeparts  := LLTL[𝐆 (TL2Green → ((←ˢ TL2Departs) = max_departs))]
abbrev TL2RedDeparts    := LLTL[𝐆 (¬TL2Green → ((←ˢ TL2Departs) = 0))]

abbrev TL1ArrivesBounds := LLTL[𝐆 (0 ≤ (←ˢ TL1Arrives) ∧ (←ˢ TL1Arrives) ≤ max_arrives)]
abbrev TL2ArrivesBounds := LLTL[𝐆 (0 ≤ (←ˢ TL2Arrives) ∧ (←ˢ TL2Arrives) ≤ max_arrives)]

-- Note: Queues are defined as naturals, and so won't go negative if departures exceed queue size + arrivals
abbrev TL1QueueNext     := LLTL[𝐆 ((𝐗 (←ˢ TL1Queue)) = (←ˢ TL1Queue) + (←ˢ TL1Arrives) - (←ˢ TL1Departs))]
abbrev TL2QueueNext     := LLTL[𝐆 ((𝐗 (←ˢ TL2Queue)) = (←ˢ TL2Queue) + (←ˢ TL2Arrives) - (←ˢ TL2Departs))]

abbrev TLBaseProperties := LLTL[TL1StartGreen ∧ TL2StartRed ∧ TL1ToTL2Green ∧ TL2ToTL1Green
                            ∧ TL1StayGreen ∧ TL2StayGreen ∧ TL1GreenDeparts ∧ TL1RedDeparts
                            ∧ TL2GreenDeparts ∧ TL2RedDeparts ∧ TL1ArrivesBounds ∧ TL2ArrivesBounds
                            ∧ TL1QueueNext ∧ TL2QueueNext]

-- Goal Properties
abbrev G_OneLightGreen    := LLTL[𝐆 (TL1Green ↔ ¬TL2Green)]
abbrev G_F_Green          := LLTL[(𝐆 (𝐅 TL1Green)) ∧ (𝐆 (𝐅 TL2Green))]

-- Example Proofs
theorem Satisfies_G_OneLightGreen : ⊨ⁱ LLTL[TLBaseProperties → G_OneLightGreen] := by
  simp [TLBaseProperties]
  intro t h_t_inf h
  simp [TraceSet.sat_and_iff] at h
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

  apply TraceSet.globally_induction
  . simp [push_ltl] at h1 h2 ⊢
    tauto
  . simp [push_ltl, h_t_inf, TraceFun.eval_of_eq] at h3 h4 h5 h6 ⊢
    intro n hn
    by_cases h : t.shift n (Trace.coe_lt_length_of_infinite h_t_inf n) ⊨ LLTL[TL1Green]
    · specialize h3 n h
      specialize h5 n h
      tauto
    · specialize h4 n
      specialize h6 n
      tauto

theorem Satisfies_G_OneLightGreen' : ⊨ⁱ LLTL[TLBaseProperties → G_OneLightGreen] := by
  intro t h_t_inf h
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  apply TraceSet.globally_induction
  . simp [push_ltl] at h1 h2 ⊢
    tauto
  . simp [push_ltl, h_t_inf, TraceFun.eval_of_eq] at h3 h4 h5 h6 ⊢
    intro n hn
    specialize h3 n
    specialize h4 n
    specialize h5 n
    specialize h6 n
    simp_all
    tauto

lemma no_decreasing_nat_function (f : Nat → Nat) (h : ∀ n, f n > f (n + 1)) : False := by
  generalize hm : f 0 = m
  induction m using Nat.strongRecOn generalizing f with | _ m ih => ?_
  cases hm
  refine ih (f 1) (h 0) (fun n => f (n + 1)) ?_ rfl
  intro
  apply h

set_option maxHeartbeats 1000000 in
theorem Satisifies_G_F_Green : TLBaseProperties ⇒ⁱ G_F_Green := by
  simp [TLBaseProperties, TraceSet.sem_imp_inf_iff, TraceSet.sat_imp_iff]
  intro t h_t_inf h
  have assumptions := h
  simp [TraceSet.sat_and_iff] at h
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  simp [TraceSet.sat_and_iff]
  constructor
  . simp [push_ltl]
    intro n h_n
    -- Discharge trivial case where light is currently green
    by_cases (t.shift n h_n)⊨LLTL[TL1Green]
    . use 0
      use (lt_tsub_iff_left.mpr h_n)
      simp_all
    rename_i h_not_green

    -- Establish that other light must currently be green
    have h_f_one_green := Satisfies_G_OneLightGreen
    specialize h_f_one_green t h_t_inf assumptions
    rw [TraceSet.sat_globally_iff] at h_f_one_green
    have h_other_green := h_f_one_green n h_n
    rw [TraceSet.sat_iff_iff] at h_other_green
    rw [TraceSet.sat_not_iff] at h_other_green
    simp [h_not_green] at h_other_green

    -- Establish that the other light must eventually be red
    have h_f_other_red : (t.shift n h_n) ⊨ LLTL[𝐅 (¬TL2Green)] := by
      simp [push_ltl]
      have : ∃ i, (t.shift (n + i) (by simp_all)) ⊨ LLTL[(←ˢ TL2Queue) = 0] := by
        by_contra! h
        simp [push_ltl] at h
        -- TL2Queue not zero for all time, so TL2Green must remain true
        have : ∀ i, (t.shift (n + i) (by simp_all)) ⊨ LLTL[TL2Green] := by
          intro i
          induction i with
          | zero => simpa
          | succ i ih =>
            simp [push_ltl] at h6
            obtain ⟨_, _, h6⟩ := h6 (n + i) (by simp_all) ih (h i)
            convert h6 using 2
            ring
        apply no_decreasing_nat_function (fun i => LLTLV[TL2Queue].eval! (t.shift (n + i) (by simp [h_t_inf])))
        intro i
        simp [push_ltl, h_t_inf] at h14
        specialize h14 (n + i)
        have fact : 1 + (n + i) = n + (i + 1) := by ring
        simp_rw [fact] at h14
        simp [h14]
        specialize h i
        simp [push_ltl, h_t_inf, max_arrives, max_departs] at h12 h9
        specialize h12 (n + i)
        specialize h9 (n + i) (this _)
        omega
      let i₀ := by classical exact Nat.find this
      have fact1 : (t.shift (n+i₀) (by simp_all)) ⊨ LLTL[(←ˢ TL2Queue) = 0] := by
        classical
        exact Nat.find_spec this
      have fact2 : ∀ i ≤ i₀, (t.shift (n + i) (by simp_all)) ⊨ LLTL[TL2Green] := by
        intro i
        induction i with
        | zero => simp_all
        | succ i ih =>
          intro h
          specialize ih (by omega)
          classical
          have := Nat.find_min this h
          simp [push_ltl] at this
          simp [push_ltl, h_t_inf] at h6
          specialize h6 (n + i) ih this
          convert h6.2 using 2
          ring
      -- Use i₀+1
      use (i₀) + 1
      simp [*]
      simp [push_ltl] at h4
      specialize h4 (n + i₀)
      specialize fact2 i₀ (by simp)
      simp [push_ltl] at fact1
      simp [*] at h4
      obtain ⟨_, h4⟩ := h4
      ring_nf at h4 ⊢
      simp_all
    -- Finish proof
    simp [push_ltl] at h_f_other_red
    obtain ⟨n_1, h_n_1_tl, h_n_1⟩ := h_f_other_red
    use n_1
    use h_n_1_tl
    have := h_f_one_green (n_1 + n) (by simp_all)
    simp_all [TraceSet.sat_iff_iff, TraceSet.sat_not_iff]
  . simp [push_ltl]
    intro n h_n
    -- Discharge trivial case where light is currently green
    by_cases (t.shift n h_n)⊨LLTL[TL2Green]
    . use 0
      use (lt_tsub_iff_left.mpr h_n)
      simp_all
    rename_i h_not_green

    -- Establish that other light must currently be green
    have h_f_one_green := Satisfies_G_OneLightGreen
    specialize h_f_one_green t h_t_inf assumptions
    rw [TraceSet.sat_globally_iff] at h_f_one_green
    have h_other_green := h_f_one_green n h_n
    rw [TraceSet.sat_iff_iff] at h_other_green
    rw [TraceSet.sat_not_iff] at h_other_green
    simp [h_not_green] at h_other_green

    -- Establish that the other light must eventually be red
    have h_f_other_red : (t.shift n h_n) ⊨ LLTL[𝐅 (¬TL1Green)] := by
      simp [push_ltl]
      have : ∃ i, (t.shift (n + i) (by simp_all)) ⊨ LLTL[(←ˢ TL1Queue) = 0] := by
        by_contra! h
        simp [push_ltl] at h
        -- TL1Queue not zero for all time, so TL1Green must remain true
        have : ∀ i, (t.shift (n + i) (by simp_all)) ⊨ LLTL[TL1Green] := by
          intro i
          induction i with
          | zero => simpa
          | succ i ih =>
            simp [push_ltl] at h5
            obtain ⟨_, _, h5⟩ := h5 (n + i) (by simp_all) ih (h i)
            convert h5 using 2
            ring_nf at *
            simp_all
        apply no_decreasing_nat_function (fun i => LLTLV[TL1Queue].eval! (t.shift (n + i) (by simp_all)))
        intro i
        simp [push_ltl, h_t_inf] at h13
        specialize h13 (n + i)
        have fact : 1 + (n + i) = n + (i + 1) := by ring
        simp_rw [fact] at h13
        ring_nf at h13 ⊢
        simp [h13]
        specialize h i
        simp [push_ltl, h_t_inf, max_arrives, max_departs] at h11 h7
        specialize h11 (n + i)
        specialize h7 (n + i) (this _)
        omega
      let i₀ := by classical exact Nat.find this
      have fact1 : (t.shift (n+i₀) (by simp_all)) ⊨ LLTL[(←ˢ TL1Queue) = 0] := by
        classical
        exact Nat.find_spec this
      have fact2 : ∀ i ≤ i₀, (t.shift (n + i) (by simp_all)) ⊨ LLTL[TL1Green] := by
        intro i
        induction i with
        | zero => simp_all
        | succ i ih =>
          intro h
          specialize ih (by omega)
          classical
          have := Nat.find_min this h
          simp [push_ltl] at this
          simp [push_ltl, h_t_inf] at h5
          specialize h5 (n + i) ih this
          convert h5.2 using 2
          ring_nf at *
          simp_all
      -- Use i₀+1
      use (i₀) + 1
      simp [*]
      simp [push_ltl] at h3
      specialize h3 (n + i₀)
      specialize fact2 i₀ (by simp)
      simp [push_ltl] at fact1
      simp [*] at h3
      obtain ⟨_, h3⟩ := h3
      ring_nf at h3 ⊢
      simp_all
    -- Finish proof
    simp [push_ltl] at h_f_other_red
    obtain ⟨n_1, h_n_1_tl, h_n_1⟩ := h_f_other_red
    use n_1
    use h_n_1_tl
    have := h_f_one_green (n_1 + n) (by simp_all)
    simp_all [TraceSet.sat_iff_iff, TraceSet.sat_not_iff]
