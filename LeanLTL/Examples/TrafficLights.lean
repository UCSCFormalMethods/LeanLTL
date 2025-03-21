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
    · -- TODO: FIX
      specialize hn' h
      specialize h4 n hn'
      specialize h6 n hn'
      tauto

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
    have h_f_other_red : (t.shift n h_n)⊨LLTL[F (¬TL2Green)] := by

      sorry

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
  rw [TraceSet.sem_entail_inf_iff]
  rintro t hinf ⟨h1, h2⟩
  apply TraceSet.globally_induction <;> simp_all [push_ltl, hinf]
  omega

end Teaser1

example (σ : Type*) (p : σ → ℕ) :
    let v := TraceFun.of p
    ⊨ⁱ LLTL[((← v) = 5 ∧ G ((X (← v)) = ((← v) + 1))) → G (5 ≤ (← v))] := by
  rw [TraceSet.sem_entail_inf_iff]
  rintro t hinf ⟨h1, h2⟩
  apply TraceSet.globally_induction <;> simp_all [push_ltl, hinf]
  omega

noncomputable section
namespace Teaser2
axiom σ : Type*
axiom p : σ → ℕ
abbrev v : TraceFun σ ℕ := TraceFun.of p

example : ⊨ⁱ LLTL[((← v) = 5 ∧ G ((X (← v)) = ((← v) + 1))) → G (5 ≤ (← v))] := by
  rw [TraceSet.sem_entail_inf_iff]
  rintro t hinf ⟨h1, h2⟩
  apply TraceSet.globally_induction <;> simp_all [push_ltl, hinf]
  omega

end Teaser2
end
