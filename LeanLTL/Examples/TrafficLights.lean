import LeanLTL

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
  TL1Green : Prop
  TL2Green : Prop

  TL1Arrives : ℕ
  TL1Departs : ℕ
  TL2Arrives : ℕ
  TL2Departs : ℕ
  TL1Queue : ℕ
  TL2Queue : ℕ

abbrev TL1Green := TraceSet.of ExState.TL1Green
abbrev TL2Green := TraceSet.of ExState.TL2Green
abbrev TL1Arrives := TraceFun.of ExState.TL1Arrives
abbrev TL1Departs := TraceFun.of ExState.TL1Departs
abbrev TL2Arrives := TraceFun.of ExState.TL2Arrives
abbrev TL2Departs := TraceFun.of ExState.TL2Departs
abbrev TL1Queue := TraceFun.of ExState.TL1Queue
abbrev TL2Queue := TraceFun.of ExState.TL2Queue

abbrev max_arrives : ℕ := 2
abbrev max_departs : ℕ := 3

-- Base Properties
-- TODO: Get rid of red prop
abbrev TL1StartGreen    := LLTL[TL1Green]
abbrev TL2StartRed      := LLTL[¬TL2Green]

abbrev TL1ToTL2Green    := LLTL[G ((TL1Green ∧ ((← TL1Queue) == 0)) → (Xˢ (¬TL1Green ∧ TL2Green)))]
abbrev TL2ToTL1Green    := LLTL[G ((TL2Green ∧ ((← TL2Queue) == 0)) → (Xˢ (TL1Green ∧ ¬ TL2Green)))]
abbrev TL1StayGreen     := LLTL[G ((TL1Green ∧ ((← TL1Queue) != 0)) → (Xˢ (TL1Green ∧ ¬ TL2Green)))]
abbrev TL2StayGreen     := LLTL[G ((TL2Green ∧ ((← TL2Queue) != 0)) → (Xˢ (¬ TL1Green ∧ TL2Green)))]

abbrev TL1GreenDeparts  := LLTL[G (TL1Green → ((← TL1Departs) == max_departs))]
abbrev TL1RedDeparts    := LLTL[G (¬TL1Green → ((← TL1Departs) == 0))]
abbrev TL2GreenDeparts  := LLTL[G (TL2Green → ((← TL2Departs) == max_departs))]
abbrev TL2RedDeparts    := LLTL[G (¬TL2Green → ((← TL2Departs) == 0))]

abbrev TL1ArrivesBounds := LLTL[G (0 ≤ (← TL1Arrives) ∧ (← TL1Arrives) ≤ max_arrives)]
abbrev TL2ArrivesBounds := LLTL[G (0 ≤ (← TL2Arrives) ∧ (← TL2Arrives) ≤ max_arrives)]

abbrev TL1QueueNext     := LLTL[G ((X (← TL1Queue)) == (← TL1Queue) + (← TL1Arrives) - (← TL1Departs))]
abbrev TL2QueueNext     := LLTL[G ((X (← TL2Queue)) == (← TL2Queue) + (← TL2Arrives) - (← TL2Departs))]

abbrev TLBaseProperties := LLTL[TL1StartGreen ∧ TL2StartRed ∧ TL1ToTL2Green ∧ TL2ToTL1Green
                            ∧ TL1StayGreen ∧ TL2StayGreen ∧ TL1GreenDeparts ∧ TL1RedDeparts
                            ∧ TL2GreenDeparts ∧ TL2RedDeparts ∧ TL1ArrivesBounds ∧ TL2ArrivesBounds
                            ∧ TL1QueueNext ∧ TL2QueueNext]

-- Goal Properties
abbrev G_OneLightGreen    := LLTL[G (TL1Green ↔ ¬TL2Green)]
abbrev G_F_Green          := LLTL[G (F TL1Green) ∧ (G (F TL2Green))]

-- Example Proofs
theorem Satisfies_G_OneLightGreen : TLBaseProperties ⇒ⁱ G_OneLightGreen := by
  simp [TLBaseProperties, TraceSet.sem_imp_inf_iff, TraceSet.sat_imp_iff]
  intro t h_t_inf h
  simp [TraceSet.sat_and_iff] at h
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

  apply TraceSet.globally_induction
  . simp [push_ltl] at h1 h2 ⊢
    tauto
  . simp [push_ltl, h_t_inf, TraceFun.eval_of_eq] at h3 h4 h5 h6 ⊢
    intro n hn
    by_cases h : t.shift n (Trace.coe_lt_length_of_infinite h_t_inf n) ⊨ TL1Green
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

theorem no_decreasing_nat_function (f : Nat → Nat) (h : ∀ n, f n > f (n + 1)) : False := by
  generalize hm : f 0 = m
  induction m using Nat.strongRecOn generalizing f with | _ m ih => ?_
  cases hm
  refine ih (f 1) (h 0) (fun n => f (n + 1)) ?_ rfl
  intro
  apply h


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
    by_cases (t.shift n h_n)⊨TL1Green
    . use 0
      use (lt_tsub_iff_left.mpr h_n)
      simp_all
    rename_i h_not_green

    -- Establish that other light must currently be green
    have h_f_one_green := Satisfies_G_OneLightGreen
    simp [TraceSet.sem_imp_inf] at h_f_one_green
    specialize h_f_one_green t h_t_inf assumptions
    simp [push_ltl] at h_f_one_green
    have h_other_green := h_f_one_green n h_n
    simp [h_not_green] at h_other_green

    -- Establish that the other light must eventually be red
    have h_f_other_red : (t.shift n h_n) ⊨ LLTL[F (¬TL2Green)] := by
      simp [push_ltl]
      have : ∃ i, (t.shift (n + i) (by simp_all)) ⊨ LLTL[(← TL2Queue) = 0] := by
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
        apply no_decreasing_nat_function (fun i => TL2Queue.eval! (t.shift (n + i) (by simp_all)))
        intro i
        simp [push_ltl, h_t_inf] at h14
        specialize h14 (n + i)
        have fact : 1 + (n + i) = n + (i + 1) := by ring
        simp_rw [fact] at h14
        simp_rw [h14]
        specialize h i
        simp [push_ltl, h_t_inf, max_arrives, max_departs] at h12 h9
        specialize h12 (n + i)
        specialize h9 (n + i) (this _)
        simp [TL2Queue]
        omega
      -- Exists a timestep > n where TL2Queue is 0
      have h_exists_i : ∃ i, (t.shift (n+i) (by simp_all))⊨LLTL[TL2Green ∧ (← TL2Queue)=0] := by

        sorry
      -- Let n₀ be the earliest point that TL2Queue is 0
      generalize h_is: {i | (t.shift (n+i) (by simp_all))⊨LLTL[TL2Green ∧ (← TL2Queue)=0]} = is
      have h_is_nempty : is.Nonempty := by
        simp_all [← h_is]
        exact h_exists_i
      have h_inf_mem_is := Nat.sInf_mem h_is_nempty
      simp [← h_is] at h_inf_mem_is
      simp [h_is] at h_inf_mem_is
      simp [push_ltl] at h_inf_mem_is
      -- Use n₀+1
      use (sInf is) + 1
      simp [*]
      simp [push_ltl] at h4
      specialize h4 (n + sInf is)
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
    simp_all
  . sorry

namespace Teaser1
-- TODO: Teaser?
abbrev v : TraceFun ℕ ℕ := TraceFun.proj0

example : ⊨ⁱ LLTL[((← v) = 5 ∧ G ((X (← v)) = ((← v) + 1))) → G ((← v) ≥ 5)] := by
  simp +contextual [push_ltl]
  intros t tinf hp0 hi n
  induction n with
  | zero => simp_all
  | succ n ih =>
    specialize hi n
    simp only [add_comm] at *
    rw [hi]
    omega

example : ⊨ⁱ LLTL[((← v) = 5 ∧ G ((X (← v)) = ((← v) + 1))) → G (5 ≤ (← v))] := by
  --rw [TraceSet.sem_entail_inf_iff]
  rintro t hinf ⟨h1, h2⟩
  apply TraceSet.globally_induction <;> simp_all [push_ltl]
  omega

end Teaser1

example (σ : Type*) (p : σ → ℕ) :
    let v := TraceFun.of p
    ⊨ⁱ LLTL[((← v) = 5 ∧ G ((X (← v)) = ((← v) + 1))) → G (5 ≤ (← v))] := by
  rw [TraceSet.sem_entail_inf_iff]
  rintro t hinf ⟨h1, h2⟩
  apply TraceSet.globally_induction <;> simp_all [push_ltl]
  omega

example (σ : Type*) (p : σ → ℕ) :
    let v := TraceFun.of p
    ⊨ⁱ LLTL[((← v) = 5 ∧ G ((X (← v)) = ((← v) + 1))) → G (5 ≤ (← v))] := by
  simp +contextual [push_ltl]
  intro _ _ _ h n
  induction n with
  | zero => simp_all
  | succ n ih =>
    specialize h n
    simp_all [add_comm]
    omega

noncomputable section
namespace Teaser2
axiom σ : Type*
axiom p : σ → ℤ
abbrev x : TraceFun σ ℤ := TraceFun.of p

example : ⊨ⁱ LLTL[((← x) = 5 ∧ G ((X (← x)) = (← x) ^ 2)) → G (5 ≤ (← x))] := by
  rw [TraceSet.sem_entail_inf_iff]
  rintro t hinf ⟨h1, h2⟩
  apply TraceSet.globally_induction <;> simp_all [push_ltl, hinf]
  intros; nlinarith

end Teaser2
end
